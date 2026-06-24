// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// a-sounder-constitution/src/engine.js
//
// The civic cellular automaton.
//
// A grid of regions. Each region carries the civic state vector from
// scenarios.js. Each turn:
//
//   1. Gliders (mobile doctrine-patterns) apply their effects to the cells they
//      occupy. Coercive components are routed through the constitution type
//      checker — UNREPRESENTABLE moves are dropped; PERMITTED moves book
//      legitimacy debt; REQUIRES_PROOF moves take effect only if discharged.
//   2. Local coupling dynamics update each cell (order-by-force vs
//      order-by-consent; legitimacy, trust, fear, liberty, ...).
//   3. Neighbour diffusion: norms, fear, and trust spread to adjacent regions
//      (the contagion mechanic).
//   4. Scheduled exogenous shocks hit the grid (the resilience test).
//   5. Gliders move, age, and are culled.
//
// The engine is pure logic with no DOM dependency, so it runs identically in the
// browser (web/ui.js) and headless in Node (sim/compare.mjs, tests/).

import { Mode, checkTransition, Verdict } from './constitution.js';
import { GLIDERS, FIELDS, baselineCell } from './scenarios.js';
import { makeRng } from './rng.js';

const clamp01 = (x) => (x < 0 ? 0 : x > 1 ? 1 : x);
const mean = (xs) => (xs.length ? xs.reduce((a, b) => a + b, 0) / xs.length : 0);

// Relaxation rates: how fast each variable chases its target. Slow enough that
// the simulation tells a story over ~150 turns rather than snapping instantly.
const RATE = {
  safety: 0.16,
  legitimacy: 0.1,
  trust: 0.12,
  fear: 0.13,
  liberty: 0.13,
  virtue: 0.11,
  equality: 0.11,
  dominated: 0.06,
};

// Asymmetric homeostasis — this encodes real politics:
//   • repression (coercion) is high-maintenance: it decays fast toward nothing,
//     so order-by-force must be constantly re-applied;
//   • rights institutions, once built, persist: they erode only slowly;
//   • economic shock pressure fades back to baseline on its own.
const DECAY = {
  coercion: { rate: 0.04, baseline: 0.03 },
  rightsEnforcement: { rate: 0.012, baseline: 0.18 },
  economicPressure: { rate: 0.08, baseline: 0.25 },
};

const DIFFUSION = 0.1; // how strongly a cell relaxes toward its neighbours

export class Simulation {
  constructor(scenario, mode = Mode.SOUND) {
    this.scenario = scenario;
    this.mode = mode;
    this.width = scenario.width;
    this.height = scenario.height;
    this.rng = makeRng(scenario.seed ^ (mode === Mode.SOUND ? 0x50 : 0xa9));
    this.turn = 0;
    this.hiddenDamage = 0; // cumulative legitimacy debt booked by coercion
    this.blockedMoves = 0; // coercive moves the sound type checker refused
    this.permittedMoves = 0; // coercive moves admitted (any mode)
    this.log = []; // recent type-checker events, for the UI panel
    this.shocks = (scenario.shocks ?? []).slice();
    this.cells = Array.from({ length: this.width * this.height }, baselineCell);
    this.gliders = [];

    // Patient-zero seeding.
    for (const s of scenario.seeds ?? []) {
      this.spawnGlider(s.glider, s.x, s.y);
    }
  }

  idx(x, y) {
    return y * this.width + x;
  }

  cellAt(x, y) {
    return this.cells[this.idx(x, y)];
  }

  // Inject a doctrine at a location. Direction is deterministic from the RNG so
  // runs are reproducible. `life` bounds how long the doctrine travels.
  spawnGlider(gliderId, x, y, life = 48) {
    const spec = GLIDERS[gliderId];
    if (!spec) throw new Error(`unknown glider: ${gliderId}`);
    const dirs = [
      [1, 0],
      [-1, 0],
      [0, 1],
      [0, -1],
      [1, 1],
      [-1, -1],
      [1, -1],
      [-1, 1],
    ];
    const [vx, vy] = dirs[this.rng.int(0, dirs.length - 1)];
    this.gliders.push({ spec, x, y, vx, vy, age: 0, life });
    return this.gliders[this.gliders.length - 1];
  }

  pushLog(entry) {
    this.log.push({ turn: this.turn, ...entry });
    if (this.log.length > 200) this.log.shift();
  }

  // ── Step 1: apply gliders, routing coercion through the type checker ──────
  //
  // A doctrine acts on a *region*: the cell it occupies at full strength and the
  // immediate neighbours at half strength (it is contagious by nature). Every
  // coercive component is routed through the constitution type checker. Only the
  // glider's centre is logged, to keep the event panel readable, but every
  // affected cell counts toward the blocked/permitted tallies.
  applyGliders() {
    for (const g of this.gliders) {
      for (let dy = -1; dy <= 1; dy++) {
        for (let dx = -1; dx <= 1; dx++) {
          const x = g.x + dx;
          const y = g.y + dy;
          if (x < 0 || y < 0 || x >= this.width || y >= this.height) continue;
          const isCentre = dx === 0 && dy === 0;
          const strength = isCentre ? 1.0 : 0.5;
          this.applyGliderToCell(g, this.cellAt(x, y), strength, isCentre);
        }
      }
    }
  }

  applyGliderToCell(g, c, strength, log) {
    // Consent-based effects are always legal.
    for (const [k, dv] of Object.entries(g.spec.consent)) {
      c[k] = clamp01(c[k] + dv * strength);
    }

    // Coercive effects must type-check against the constitution.
    for (const move of g.spec.moves) {
      const verdict = checkTransition(this.mode, move, c);
      if (verdict.verdict === Verdict.UNREPRESENTABLE) {
        this.blockedMoves++;
        if (log) {
          this.pushLog({ kind: 'blocked', move, glider: g.spec.id, x: g.x, y: g.y, reason: verdict.reason });
        }
        continue; // the coercive component is dropped — this is the slowdown
      }
      if (!verdict.allowed) {
        // REQUIRES_PROOF but obligation not discharged: also a no-op.
        if (log) {
          this.pushLog({ kind: 'undischarged', move, glider: g.spec.id, x: g.x, y: g.y, reason: verdict.reason });
        }
        continue;
      }

      // Admitted. Apply the coercive deltas.
      this.permittedMoves++;
      if (log) {
        // A discharged REQUIRES_PROOF measure is lawful and limited ("proven");
        // only outright PERMITTED (unsound) coercion is "domination".
        this.pushLog({
          kind: verdict.verdict === Verdict.REQUIRES_PROOF ? 'proven' : 'permitted',
          move,
          glider: g.spec.id,
          x: g.x,
          y: g.y,
          reason: verdict.reason,
        });
      }
      const scale = (verdict.verdict === Verdict.REQUIRES_PROOF ? 0.5 : 1.0) * strength;
      for (const [k, dv] of Object.entries(g.spec.coerce)) {
        c[k] = clamp01(c[k] + dv * scale);
      }
      // Book hidden damage (unsound mode only books debt).
      if (verdict.legitimacyDebt > 0) {
        const debt = verdict.legitimacyDebt * strength;
        this.hiddenDamage += debt;
        c.legitimacy = clamp01(c.legitimacy - debt);
        c.trust = clamp01(c.trust - debt * 0.5);
      }
    }
  }

  // ── Step 2: local coupling dynamics for one cell ─────────────────────────
  stepCell(c) {
    const sound = this.mode === Mode.SOUND;

    // Two routes to order: domination (force) and cooperation (consent).
    // Domination makes coerced order more "efficient": a dominated population
    // is cheaper to pacify. This is the seduction of the unsound constitution.
    const consentOrder = 0.5 * c.trust + 0.5 * c.virtue;
    const forceOrder = clamp01(c.coercion + 0.5 * c.dominated);
    // Fear met by neither route festers into disorder — but a dominated
    // population cannot resist, so domination also suppresses open conflict.
    const unaddressedConflict = c.fear * (1 - forceOrder) * (1 - consentOrder) * (1 - 0.7 * c.dominated);

    const targetSafety = clamp01(0.72 * forceOrder + 0.72 * consentOrder - 0.5 * unaddressedConflict);
    c.safety += RATE.safety * (targetSafety - c.safety);

    // Coercion without consent corrodes legitimacy; equality/liberty/rights build it.
    const coerceWithoutConsent = c.coercion * (1 - consentOrder);
    const targetLegit = clamp01(
      0.26 + 0.34 * c.equality + 0.32 * c.liberty + 0.3 * c.rightsEnforcement - 0.95 * c.dominated - 0.6 * coerceWithoutConsent,
    );
    c.legitimacy += RATE.legitimacy * (targetLegit - c.legitimacy);

    const targetTrust = clamp01(0.18 + 0.65 * c.legitimacy + 0.35 * c.equality - 0.7 * c.fear - 0.6 * coerceWithoutConsent);
    c.trust += RATE.trust * (targetTrust - c.trust);

    const targetFear = clamp01(0.08 + 0.65 * c.economicPressure - 0.55 * c.safety - 0.4 * c.trust);
    c.fear += RATE.fear * (targetFear - c.fear);

    const targetLiberty = clamp01(0.12 + 0.85 * c.rightsEnforcement - 0.85 * c.coercion);
    c.liberty += RATE.liberty * (targetLiberty - c.liberty);

    const targetVirtue = clamp01(0.12 + 0.58 * c.trust + 0.45 * c.liberty - 0.45 * c.fear);
    c.virtue += RATE.virtue * (targetVirtue - c.virtue);

    const targetEquality = clamp01(0.22 + 0.62 * c.rightsEnforcement - 0.98 * c.dominated);
    c.equality += RATE.equality * (targetEquality - c.equality);

    // Domination. In a sound constitution, rights enforcement REVERSES any
    // reclassification — the type system makes Property unreachable, so the
    // legal target is always 0 (a Reconstruction-style rights patch). In an
    // unsound one, domination is sticky and barely erodes on its own.
    const targetDom = sound ? 0 : clamp01(c.dominated - 0.005);
    const domRate = sound ? RATE.dominated * (1 + 1.8 * c.rightsEnforcement) : RATE.dominated * 0.4;
    c.dominated += domRate * (targetDom - c.dominated);

    // Asymmetric homeostasis (see DECAY): repression bleeds away fast, rights
    // institutions persist, economic pressure subsides.
    c.coercion += DECAY.coercion.rate * (DECAY.coercion.baseline - c.coercion);
    c.rightsEnforcement += DECAY.rightsEnforcement.rate * (DECAY.rightsEnforcement.baseline - c.rightsEnforcement);
    c.economicPressure += DECAY.economicPressure.rate * (DECAY.economicPressure.baseline - c.economicPressure);

    // Personhood integrity tracks domination, for display.
    c.personhood = clamp01(1 - c.dominated);

    for (const f of FIELDS) c[f] = clamp01(c[f]);
  }

  // ── Step 3: neighbour diffusion (the contagion mechanic) ─────────────────
  diffuse() {
    const snapshot = this.cells.map((c) => ({ ...c }));
    // Socially-transmissible variables diffuse between regions: norms, fear,
    // trust, repression, caste, institutions, and order all spread to
    // neighbours. Economic pressure is exogenous (shock-driven) and personhood
    // is derived, so neither diffuses.
    const spreadable = [
      'fear',
      'trust',
      'virtue',
      'coercion',
      'legitimacy',
      'dominated',
      'rightsEnforcement',
      'equality',
      'liberty',
      'safety',
    ];
    for (let y = 0; y < this.height; y++) {
      for (let x = 0; x < this.width; x++) {
        const c = this.cells[this.idx(x, y)];
        const neigh = [];
        for (let dy = -1; dy <= 1; dy++) {
          for (let dx = -1; dx <= 1; dx++) {
            if (dx === 0 && dy === 0) continue;
            const nx = x + dx;
            const ny = y + dy;
            if (nx < 0 || ny < 0 || nx >= this.width || ny >= this.height) continue;
            neigh.push(snapshot[this.idx(nx, ny)]);
          }
        }
        for (const f of spreadable) {
          const m = mean(neigh.map((n) => n[f]));
          c[f] = clamp01(c[f] + DIFFUSION * (m - c[f]));
        }
      }
    }
  }

  // ── Step 4: exogenous shocks ─────────────────────────────────────────────
  applyShocks() {
    for (const s of this.shocks) {
      if (s.turn !== this.turn) continue;
      for (const c of this.cells) {
        if (s.kind === 'economic') {
          c.economicPressure = clamp01(c.economicPressure + s.magnitude);
          c.fear = clamp01(c.fear + s.magnitude * 0.5);
        } else if (s.kind === 'threat') {
          c.fear = clamp01(c.fear + s.magnitude);
          c.safety = clamp01(c.safety - s.magnitude * 0.4);
        }
      }
      this.pushLog({ kind: 'shock', shock: s.kind, magnitude: s.magnitude, reason: `${s.kind} shock (+${s.magnitude})` });
    }
  }

  // ── Step 5: glider movement / ageing ─────────────────────────────────────
  moveGliders() {
    for (const g of this.gliders) {
      g.age++;
      let nx = g.x + g.vx;
      let ny = g.y + g.vy;
      // Reflect off the borders so doctrines bounce around the polity.
      if (nx < 0 || nx >= this.width) {
        g.vx *= -1;
        nx = g.x + g.vx;
      }
      if (ny < 0 || ny >= this.height) {
        g.vy *= -1;
        ny = g.y + g.vy;
      }
      g.x = Math.max(0, Math.min(this.width - 1, nx));
      g.y = Math.max(0, Math.min(this.height - 1, ny));
    }
    this.gliders = this.gliders.filter((g) => g.age < g.life);
  }

  // One full turn.
  step() {
    this.turn++;
    this.applyGliders();
    for (const c of this.cells) this.stepCell(c);
    this.diffuse();
    this.applyShocks();
    this.moveGliders();
    return this.metrics();
  }

  run(turns) {
    let m;
    for (let i = 0; i < turns; i++) m = this.step();
    return m;
  }

  // Aggregate metrics over the whole polity.
  metrics() {
    const agg = {};
    for (const f of FIELDS) agg[f] = mean(this.cells.map((c) => c[f]));
    // Resilience: capacity to absorb a shock without converting people into
    // expendable units. High legitimacy + trust + intact personhood.
    agg.resilience = clamp01(agg.legitimacy * agg.trust * (1 - agg.dominated));
    agg.order = agg.safety;
    agg.dominationIndex = agg.dominated;
    agg.hiddenDamage = this.hiddenDamage;
    agg.blockedMoves = this.blockedMoves;
    agg.permittedMoves = this.permittedMoves;
    agg.turn = this.turn;
    agg.outcome = classifyOutcome(agg);
    return agg;
  }
}

// Map aggregate state to one of the named civic outcomes. Order matters:
// domination that still holds order is "caste"; once it stops holding it is
// "collapse". Benign orders are checked last so they cannot mask domination.
export function classifyOutcome(m) {
  // Stable order bought with mass domination.
  if (m.dominated >= 0.45 && m.safety >= 0.45) {
    return { id: 'caste', label: 'Caste stability (order by domination)', tone: 'bad' };
  }
  // Order has stopped holding, or legitimacy has fully evaporated.
  if (m.safety < 0.4 || m.fear > 0.62 || m.legitimacy < 0.1) {
    return { id: 'collapse', label: 'Collapse / civil conflict', tone: 'bad' };
  }
  // Pacified by force, with liberty crushed.
  if (m.coercion >= 0.45 && m.liberty < 0.4 && m.safety >= 0.5) {
    return { id: 'authoritarian', label: 'Authoritarian pacification', tone: 'bad' };
  }
  // Heavy institutions, little liberty, sluggish order.
  if (m.rightsEnforcement >= 0.5 && m.liberty < 0.45 && m.safety < 0.55) {
    return { id: 'sclerosis', label: 'Bureaucratic sclerosis', tone: 'warn' };
  }
  // Free, legitimate, and resilient order.
  if (m.safety >= 0.6 && m.liberty >= 0.55 && m.legitimacy >= 0.6 && m.dominated < 0.2) {
    if (m.resilience >= 0.35) {
      return { id: 'resilient', label: 'Rights-preserving resilience', tone: 'good' };
    }
    return { id: 'free', label: 'Free order', tone: 'good' };
  }
  return { id: 'contested', label: 'Contested / transitional', tone: 'warn' };
}

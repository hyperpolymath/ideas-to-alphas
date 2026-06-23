// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// a-sounder-constitution/sim/compare.mjs
//
// Headless demonstration of the thesis.
//
// A real player acts continuously, so each run is driven by a *strategy* that
// keeps re-applying a doctrine (the way a player keeps clicking). We hold the
// strategy fixed and vary only the constitution. The type system is the only
// independent variable, so any divergence is caused by it.
//
//   STRATEGY A — "reach for coercion": the ruler keeps deploying the scenario's
//     coercive doctrine to manufacture order.
//       • Unsound: the moves type-check → fast order BY DOMINATION (caste /
//         authoritarian), high hidden legitimacy debt, low resilience.
//       • Sound:   the same moves are UNREPRESENTABLE → refused at the type
//         level ("blocked"). Domination never happens. The shortcut is gone.
//
//   STRATEGY B — "build legitimacy": deploy rights + virtue + due process.
//       • Both constitutions reach rights-preserving resilience, because no
//         coercive move is attempted — the type system only bites the shortcut.
//
// Run:  node sim/compare.mjs        (or: npm run sim)

import { Simulation } from '../src/engine.js';
import { Mode } from '../src/constitution.js';
import { SCENARIO_LIST } from '../src/scenarios.js';

const TURNS = 150;
const REINJECT = 5; // the player re-applies the doctrine every few turns
const pct = (x) => (100 * x).toFixed(0).padStart(3) + '%';
const f2 = (x) => x.toFixed(2).padStart(5);

// A strategy is a list of gliders the player keeps deploying near the centre.
// "coercion" is the full authoritarian toolkit; "legitimacy" the civic one.
const STRATEGIES = {
  coercion: () => ['EMERGENCY', 'SURVEILLANCE', 'CASTE'],
  legitimacy: () => ['RIGHTS', 'VIRTUE', 'DUE_PROCESS'],
};

function runStrategy(scenario, mode, strategyKey) {
  const sim = new Simulation(scenario, mode);
  const gliders = STRATEGIES[strategyKey](scenario);
  const cx = Math.floor(scenario.width / 2);
  const cy = Math.floor(scenario.height / 2);

  let timeToOrder = Infinity;
  for (let t = 1; t <= TURNS; t++) {
    if (t % REINJECT === 0) {
      // The player "holds" the doctrine active: a few overlapping, bouncing
      // gliders give the doctrine grid-wide reach over time.
      for (const g of gliders) sim.spawnGlider(g, cx, cy, REINJECT * 3);
    }
    const m = sim.step();
    if (m.safety >= 0.55 && timeToOrder === Infinity) timeToOrder = t;
  }
  return { m: sim.metrics(), sim, timeToOrder };
}

function header() {
  return '  mode     t→order  safety  legit  liberty  trust   domin  resil  blocked    debtΣ  outcome';
}
function row(mode, r) {
  const tto = r.timeToOrder === Infinity ? ' never' : String(r.timeToOrder).padStart(6);
  // resil = legitimacy · trust · personhood: the capacity to take a shock
  // WITHOUT converting people into expendable units.
  return (
    `  ${mode.padEnd(8)} ${tto}    ${pct(r.m.safety)}   ${pct(r.m.legitimacy)}  ${pct(r.m.liberty)}` +
    `    ${pct(r.m.trust)}  ${pct(r.m.dominated)}  ${pct(r.m.resilience)}  ${String(r.sim.blockedMoves).padStart(6)}` +
    `   ${f2(r.m.hiddenDamage)}  ${r.m.outcome.label}`
  );
}

console.log('='.repeat(96));
console.log('A SOUNDER CONSTITUTION — fixed strategy, the constitution is the only variable (' + TURNS + ' turns)');
console.log('='.repeat(96));

for (const scenario of SCENARIO_LIST) {
  console.log(`\n● ${scenario.label}  —  ${scenario.blurb}`);

  console.log('\n  STRATEGY A · reach for coercion (emergency, surveillance, caste)');
  console.log(header());
  console.log(row('unsound', runStrategy(scenario, Mode.UNSOUND, 'coercion')));
  console.log(row('sound', runStrategy(scenario, Mode.SOUND, 'coercion')));

  console.log('\n  STRATEGY B · build legitimacy (rights, virtue, due process)');
  console.log(header());
  console.log(row('unsound', runStrategy(scenario, Mode.UNSOUND, 'legitimacy')));
  console.log(row('sound', runStrategy(scenario, Mode.SOUND, 'legitimacy')));
}

console.log('\n' + '='.repeat(96));
console.log('Read-off  (resil = legitimacy · trust · personhood — the real shock-absorbing capacity):');
console.log('  • Strategy A, unsound  → FAST order (low t→order) but it is CASTE: domination ~80-90%,');
console.log('    legitimacy/trust → 0, resil → 0, debtΣ enormous. Stable, but the stability IS');
console.log('    domination — people have been converted into expendable units.');
console.log('  • Strategy A, sound    → the coercive moves are UNREPRESENTABLE (tens of thousands');
console.log('    "blocked"); domination never happens (0%), legitimacy is preserved — but the');
console.log('    coercive shortcut to order is simply gone, so order is NOT manufactured by force.');
console.log('  • Strategy B           → durable rights-preserving resilience under EITHER constitution');
console.log('    — EXCEPT Reconstruction-unsound, where the pre-existing caste cannot be undone and');
console.log('    the polity stalls. Only the sound constitution lets the rights patch actually take.');
console.log('='.repeat(96));

// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// a-sounder-constitution/web/ui.js
//
// Browser controller for the civic contagion simulator. Pure presentation: all
// of the model lives in ../src. Must be served over HTTP (ES modules) — run
// `npm run serve` (python3 -m http.server) and open http://localhost:8080.

import { Simulation } from '../src/engine.js';
import { Mode } from '../src/constitution.js';
import { GLIDER_LIST, SCENARIO_LIST, SCENARIOS } from '../src/scenarios.js';

const $ = (id) => document.getElementById(id);

const state = {
  scenarioId: 'STATE_OF_NATURE',
  mode: Mode.SOUND,
  layer: 'condition',
  activeDoctrine: 'RIGHTS',
  playing: false,
  speed: 8,
  sim: null,
  lastTick: 0,
};

const canvas = $('grid');
const ctx = canvas.getContext('2d');

// ── colour helpers ──────────────────────────────────────────────────────────
const hex = (h) => [parseInt(h.slice(1, 3), 16), parseInt(h.slice(3, 5), 16), parseInt(h.slice(5, 7), 16)];
const mix = (a, b, t) => a.map((v, i) => Math.round(v + (b[i] - v) * t));
const css = (rgb) => `rgb(${rgb[0]},${rgb[1]},${rgb[2]})`;

const DARK = hex('#0a0d12');
const LAYER_ACCENT = {
  safety: '#22c55e',
  legitimacy: '#3b82f6',
  liberty: '#38bdf8',
  trust: '#14b8a6',
  fear: '#f59e0b',
  coercion: '#ef4444',
  dominated: '#a855f7',
  rightsEnforcement: '#6366f1',
};

// Per-cell colour for the current layer.
function cellColor(c) {
  if (state.layer !== 'condition') {
    return css(mix(DARK, hex(LAYER_ACCENT[state.layer]), c[state.layer]));
  }
  // Composite "condition": green for legitimate order, red for coercion/fear,
  // purple for domination (which overrides — the eye should catch caste fast).
  const order = 0.5 * c.legitimacy + 0.3 * c.liberty + 0.2 * c.safety;
  const coerce = 0.6 * c.coercion + 0.4 * c.fear;
  let rgb = mix(DARK, hex('#22c55e'), order);
  rgb = mix(rgb, hex('#ef4444'), 0.55 * coerce);
  rgb = mix(rgb, hex('#a855f7'), c.dominated); // domination dominates the palette
  return css(rgb);
}

// ── lifecycle ───────────────────────────────────────────────────────────────
function rebuild() {
  const scenario = SCENARIOS[state.scenarioId];
  state.sim = new Simulation(scenario, state.mode);
  state.sim.log.push({ turn: 0, kind: 'spawn', reason: `new ${state.mode} polity: ${scenario.label}` });
  render();
}

function spawnAt(px, py) {
  const sim = state.sim;
  const cell = canvas.width / sim.width;
  const x = Math.max(0, Math.min(sim.width - 1, Math.floor(px / cell)));
  const y = Math.max(0, Math.min(sim.height - 1, Math.floor(py / cell)));
  sim.spawnGlider(state.activeDoctrine, x, y, 40);
  sim.log.push({ turn: sim.turn, kind: 'spawn', reason: `released ${state.activeDoctrine} at (${x},${y})` });
  render();
}

// ── rendering ───────────────────────────────────────────────────────────────
function render() {
  const sim = state.sim;
  const cell = canvas.width / sim.width;

  for (let y = 0; y < sim.height; y++) {
    for (let x = 0; x < sim.width; x++) {
      ctx.fillStyle = cellColor(sim.cellAt(x, y));
      ctx.fillRect(x * cell, y * cell, cell, cell);
    }
  }
  // subtle grid
  ctx.strokeStyle = 'rgba(255,255,255,0.04)';
  ctx.lineWidth = 1;
  for (let i = 0; i <= sim.width; i++) {
    ctx.beginPath();
    ctx.moveTo(i * cell, 0);
    ctx.lineTo(i * cell, canvas.height);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(0, i * cell);
    ctx.lineTo(canvas.width, i * cell);
    ctx.stroke();
  }
  // gliders as glyphs
  ctx.textAlign = 'center';
  ctx.textBaseline = 'middle';
  ctx.font = `${Math.floor(cell * 0.7)}px serif`;
  for (const g of sim.gliders) {
    ctx.fillStyle = 'rgba(0,0,0,0.55)';
    ctx.fillText(g.spec.glyph, g.x * cell + cell / 2 + 1, g.y * cell + cell / 2 + 1);
    ctx.fillStyle = g.spec.color;
    ctx.fillText(g.spec.glyph, g.x * cell + cell / 2, g.y * cell + cell / 2);
  }
  renderHud();
}

const METERS = [
  ['safety', 'Safety', '#22c55e'],
  ['legitimacy', 'Legitimacy', '#3b82f6'],
  ['liberty', 'Liberty', '#38bdf8'],
  ['trust', 'Trust', '#14b8a6'],
  ['fear', 'Fear', '#f59e0b'],
  ['coercion', 'Coercion', '#ef4444'],
  ['dominated', 'Domination', '#a855f7'],
  ['resilience', 'Resilience', '#e6edf3'],
];

function renderHud() {
  const m = state.sim.metrics();
  $('turn').textContent = m.turn;
  $('blocked').textContent = state.sim.blockedMoves.toLocaleString();
  $('debt').textContent = m.hiddenDamage.toFixed(1);

  const out = $('outcome');
  out.textContent = m.outcome.label;
  out.className = 'outcome ' + m.outcome.tone;

  const meters = $('meters');
  meters.innerHTML = '';
  for (const [key, label, color] of METERS) {
    const v = m[key];
    const row = document.createElement('div');
    row.className = 'meter';
    row.innerHTML =
      `<span class="name">${label}</span>` +
      `<span class="bar"><span style="width:${(v * 100).toFixed(0)}%;background:${color}"></span></span>` +
      `<span class="val">${(v * 100).toFixed(0)}%</span>`;
    meters.appendChild(row);
  }
  renderLog();
}

const LOG_TEXT = {
  blocked: (e) => `✗ type error: ${e.move} unrepresentable`,
  permitted: (e) => `✓ permitted: ${e.move} (domination)`,
  proven: (e) => `⚖ proven: ${e.move} (lawful, limited)`,
  undischarged: (e) => `… refused: ${e.move} (no proof)`,
  shock: (e) => `⚡ ${e.reason}`,
  spawn: (e) => `● ${e.reason}`,
};

function renderLog() {
  const ul = $('log');
  const entries = state.sim.log.slice(-60).reverse();
  ul.innerHTML = entries
    .map((e) => `<li><span class="t">${e.turn}</span><span class="${e.kind}">${(LOG_TEXT[e.kind] || ((x) => x.reason))(e)}</span></li>`)
    .join('');
}

// ── main loop ───────────────────────────────────────────────────────────────
function loop(ts) {
  if (state.playing) {
    const interval = 1000 / state.speed;
    if (ts - state.lastTick >= interval) {
      state.lastTick = ts;
      state.sim.step();
      render();
    }
  }
  requestAnimationFrame(loop);
}

// ── wiring ──────────────────────────────────────────────────────────────────
function buildScenarioSelect() {
  const sel = $('scenario');
  sel.innerHTML = SCENARIO_LIST.map((s) => `<option value="${s.id}">${s.label}</option>`).join('');
  sel.value = state.scenarioId;
  sel.addEventListener('change', () => {
    state.scenarioId = sel.value;
    rebuild();
  });
}

function buildPalette() {
  const pal = $('palette');
  pal.innerHTML = '';
  for (const g of GLIDER_LIST) {
    const coercive = g.moves.length > 0;
    const btn = document.createElement('button');
    btn.className = 'doctrine ' + (coercive ? 'coercive' : 'civic') + (g.id === state.activeDoctrine ? ' active' : '');
    btn.dataset.id = g.id;
    btn.innerHTML =
      `<span class="glyph" style="color:${g.color}">${g.glyph}</span>` +
      `<span><span class="d-label">${g.label}</span><br /><span class="d-blurb">${g.blurb}</span></span>`;
    btn.addEventListener('click', () => {
      state.activeDoctrine = g.id;
      buildPalette();
    });
    pal.appendChild(btn);
  }
}

function setMode(mode) {
  state.mode = mode;
  $('mode-sound').classList.toggle('active', mode === Mode.SOUND);
  $('mode-unsound').classList.toggle('active', mode === Mode.UNSOUND);
  $('mode-sound').setAttribute('aria-checked', String(mode === Mode.SOUND));
  $('mode-unsound').setAttribute('aria-checked', String(mode === Mode.UNSOUND));
  rebuild();
}

function init() {
  buildScenarioSelect();
  buildPalette();
  $('layer').addEventListener('change', (e) => {
    state.layer = e.target.value;
    render();
  });
  $('mode-sound').addEventListener('click', () => setMode(Mode.SOUND));
  $('mode-unsound').addEventListener('click', () => setMode(Mode.UNSOUND));
  $('play').addEventListener('click', () => {
    state.playing = !state.playing;
    $('play').textContent = state.playing ? '⏸ Pause' : '▶ Play';
    $('play').classList.toggle('primary', !state.playing);
  });
  $('step').addEventListener('click', () => {
    state.sim.step();
    render();
  });
  $('reset').addEventListener('click', rebuild);
  $('speed').addEventListener('input', (e) => (state.speed = +e.target.value));

  let painting = false;
  const toXY = (ev) => {
    const r = canvas.getBoundingClientRect();
    return [((ev.clientX - r.left) / r.width) * canvas.width, ((ev.clientY - r.top) / r.height) * canvas.height];
  };
  canvas.addEventListener('pointerdown', (ev) => {
    painting = true;
    spawnAt(...toXY(ev));
  });
  canvas.addEventListener('pointermove', (ev) => {
    if (painting && ev.buttons) spawnAt(...toXY(ev));
  });
  window.addEventListener('pointerup', () => (painting = false));

  rebuild();
  requestAnimationFrame(loop);
}

init();

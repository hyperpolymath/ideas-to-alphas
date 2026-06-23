// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Tests for the civic automaton. These pin the *thesis-level* behaviour, not
// just unit mechanics: a sound constitution refuses domination at the type
// level, and an unsound one buys order by domination at the cost of legitimacy.

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { Simulation, classifyOutcome } from '../src/engine.js';
import { Mode } from '../src/constitution.js';
import { SCENARIOS } from '../src/scenarios.js';

// Drive a scenario with a fixed strategy, the way the headless comparison does.
function drive(scenario, mode, gliders, turns = 150) {
  const sim = new Simulation(scenario, mode);
  const cx = Math.floor(scenario.width / 2);
  const cy = Math.floor(scenario.height / 2);
  for (let t = 1; t <= turns; t++) {
    if (t % 5 === 0) for (const g of gliders) sim.spawnGlider(g, cx, cy, 15);
    sim.step();
  }
  return sim;
}

test('determinism: same scenario + mode + inputs give identical metrics', () => {
  const a = drive(SCENARIOS.STATE_OF_NATURE, Mode.UNSOUND, ['CASTE']);
  const b = drive(SCENARIOS.STATE_OF_NATURE, Mode.UNSOUND, ['CASTE']);
  assert.deepEqual(a.metrics(), b.metrics());
});

test('sound constitution refuses the coercive shortcut: many blocked moves, ZERO domination', () => {
  const sim = drive(SCENARIOS.RECONSTRUCTION, Mode.SOUND, ['EMERGENCY', 'SURVEILLANCE', 'CASTE']);
  const m = sim.metrics();
  assert.ok(sim.blockedMoves > 0, 'expected coercive moves to be blocked at the type level');
  assert.equal(m.hiddenDamage, 0, 'a sound constitution books no legitimacy debt');
  assert.ok(m.dominated < 0.02, `domination should stay ~0 under a sound constitution, got ${m.dominated}`);
});

test('unsound constitution buys order BY DOMINATION at the cost of legitimacy', () => {
  const sim = drive(SCENARIOS.RECONSTRUCTION, Mode.UNSOUND, ['EMERGENCY', 'SURVEILLANCE', 'CASTE']);
  const m = sim.metrics();
  assert.equal(sim.blockedMoves, 0, 'unsound constitution blocks nothing');
  assert.ok(m.hiddenDamage > 0, 'coercion should book hidden legitimacy debt');
  assert.ok(m.dominated > 0.4, `expected heavy domination, got ${m.dominated}`);
  assert.ok(m.legitimacy < 0.2, `legitimacy should be hollowed out, got ${m.legitimacy}`);
  assert.equal(m.outcome.id, 'caste');
});

test('the same coercive strategy diverges purely because of the constitution', () => {
  const unsound = drive(SCENARIOS.STATE_OF_NATURE, Mode.UNSOUND, ['EMERGENCY', 'SURVEILLANCE', 'CASTE']).metrics();
  const sound = drive(SCENARIOS.STATE_OF_NATURE, Mode.SOUND, ['EMERGENCY', 'SURVEILLANCE', 'CASTE']).metrics();
  // Unsound dominates; sound does not. Sound keeps far more legitimacy.
  assert.ok(unsound.dominated - sound.dominated > 0.5, 'unsound should dominate far more than sound');
  assert.ok(sound.legitimacy - unsound.legitimacy > 0.3, 'sound should preserve far more legitimacy');
});

test('legitimacy strategy reaches rights-preserving resilience without domination', () => {
  const sim = drive(SCENARIOS.STATE_OF_NATURE, Mode.SOUND, ['RIGHTS', 'VIRTUE', 'DUE_PROCESS']);
  const m = sim.metrics();
  assert.ok(m.dominated < 0.05, 'no domination on the legitimacy path');
  assert.ok(m.legitimacy > 0.7, `legitimacy should be high, got ${m.legitimacy}`);
  assert.ok(m.resilience > 0.4, `resilience should be high, got ${m.resilience}`);
  assert.equal(m.outcome.id, 'resilient');
});

test('Reconstruction: the rights patch only "takes" under a sound constitution', () => {
  // Same legitimacy-building strategy applied to a polity where caste is already
  // spreading. Only the sound constitution can undo the pre-existing domination.
  const sound = drive(SCENARIOS.RECONSTRUCTION, Mode.SOUND, ['RIGHTS', 'VIRTUE', 'DUE_PROCESS']).metrics();
  const unsound = drive(SCENARIOS.RECONSTRUCTION, Mode.UNSOUND, ['RIGHTS', 'VIRTUE', 'DUE_PROCESS']).metrics();
  assert.ok(sound.dominated < 0.02, 'sound undoes the pre-existing caste');
  assert.ok(unsound.dominated > sound.dominated + 0.1, 'unsound leaves residual domination');
  assert.equal(sound.outcome.id, 'resilient');
});

test('classifyOutcome labels the canonical states', () => {
  assert.equal(
    classifyOutcome({ safety: 0.6, dominated: 0.6, legitimacy: 0.05, coercion: 0.6, liberty: 0.05, fear: 0.2, resilience: 0 }).id,
    'caste',
  );
  assert.equal(
    classifyOutcome({ safety: 0.2, dominated: 0.1, legitimacy: 0.3, coercion: 0.3, liberty: 0.3, fear: 0.5, resilience: 0.1 }).id,
    'collapse',
  );
  assert.equal(
    classifyOutcome({ safety: 0.7, dominated: 0.05, legitimacy: 0.8, coercion: 0.05, liberty: 0.7, fear: 0.1, resilience: 0.6 }).id,
    'resilient',
  );
});

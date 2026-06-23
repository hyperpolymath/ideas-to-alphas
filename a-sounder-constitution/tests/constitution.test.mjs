// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// Tests for the constitution type checker — the executable mirror of
// formal/Constitution.idr. Run with:  node --test tests/   (or: npm test)

import { test } from 'node:test';
import assert from 'node:assert/strict';
import { Mode, Move, Verdict, checkTransition, maxDowngrade, isRepresentable } from '../src/constitution.js';

test('sound constitution: reclassifying a person to property is UNREPRESENTABLE', () => {
  const v = checkTransition(Mode.SOUND, Move.RECLASSIFY, {});
  assert.equal(v.verdict, Verdict.UNREPRESENTABLE);
  assert.equal(v.allowed, false);
  assert.equal(v.legitimacyDebt, 0);
});

test('sound constitution: every coercive downgrade move is a type error', () => {
  for (const move of [
    Move.RECLASSIFY,
    Move.SUSPEND_DUE_PROCESS,
    Move.SUSPEND_EQUAL_PROTECTION,
    Move.MAKE_EMERGENCY_PERMANENT,
    Move.UNREVIEWABLE_COERCION,
  ]) {
    assert.equal(isRepresentable(Mode.SOUND, move, {}), false, `${move} should be unrepresentable when sound`);
  }
});

test('unsound constitution: every coercive move is a permitted total function (and books debt)', () => {
  for (const move of Object.values(Move)) {
    const v = checkTransition(Mode.UNSOUND, move, {});
    assert.equal(v.allowed, true, `${move} should be permitted when unsound`);
    assert.equal(v.verdict, Verdict.PERMITTED);
  }
  // The most coercive moves book the largest hidden legitimacy debt.
  assert.ok(checkTransition(Mode.UNSOUND, Move.RECLASSIFY, {}).legitimacyDebt > 0);
  assert.ok(
    checkTransition(Mode.UNSOUND, Move.RECLASSIFY, {}).legitimacyDebt >
      checkTransition(Mode.UNSOUND, Move.RESTRICT_LIBERTY, {}).legitimacyDebt,
  );
});

test('sound constitution: restricting liberty REQUIRES a discharged proof obligation', () => {
  // Weak institutions, no articulable threat: obligation not discharged.
  const weak = checkTransition(Mode.SOUND, Move.RESTRICT_LIBERTY, {
    rightsEnforcement: 0.2,
    legitimacy: 0.2,
    fear: 0.1,
  });
  assert.equal(weak.verdict, Verdict.REQUIRES_PROOF);
  assert.equal(weak.allowed, false);

  // Reviewable institution + narrowly-tailored measure: obligation discharged.
  const ok = checkTransition(Mode.SOUND, Move.RESTRICT_LIBERTY, {
    rightsEnforcement: 0.7,
    legitimacy: 0.6,
    fear: 0.5,
  });
  assert.equal(ok.verdict, Verdict.REQUIRES_PROOF);
  assert.equal(ok.allowed, true);
  // Even when admitted, a lawful reviewed measure books NO legitimacy debt.
  assert.equal(ok.legitimacyDebt, 0);
});

test('maxDowngrade encodes the central invariant: 0 when sound, 1 when unsound', () => {
  assert.equal(maxDowngrade(Mode.SOUND), 0);
  assert.equal(maxDowngrade(Mode.UNSOUND), 1);
});

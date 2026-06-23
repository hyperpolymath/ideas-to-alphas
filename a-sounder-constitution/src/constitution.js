// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// a-sounder-constitution/src/constitution.js
//
// ─────────────────────────────────────────────────────────────────────────────
// THE CENTRAL THESIS, IN CODE.
// ─────────────────────────────────────────────────────────────────────────────
//
// Rights are NOT resources (sliders, budgets, points you spend). Rights are
// *type constraints on legal state transitions*. A constitution is therefore a
// transition relation: it decides which moves on civic state are even
// representable.
//
//   • SOUND constitution    — coercive downgrades of personhood are
//                             UNREPRESENTABLE (a type error, like calling a
//                             constructor that does not exist). Liberty
//                             restrictions are admissible only when a proof
//                             obligation is discharged (reviewable + narrow).
//
//   • UNSOUND constitution  — every coercive move is a permitted *total
//                             function*. Domination is cheap and fast — but each
//                             coercive move books hidden "legitimacy debt".
//
// This module is the executable mirror of `formal/Constitution.idr`, where the
// same statements are made at the *type* level: in the sound world `Property` is
// a type with no inhabitant, and sound personhood transitions are proven
// rank-monotone (standing can be recognised/upgraded, never stripped).
//
// The engine routes every coercive effect through `checkTransition` below. That
// is the whole game mechanic: in a sound constitution the type checker *drops*
// the coercive component of a doctrine, forcing the player onto slower,
// consent-based routes to order.

export const Mode = Object.freeze({ SOUND: 'sound', UNSOUND: 'unsound' });

// The personhood "type" a regional population can be assigned.
// Mirrors `data Human = FullPerson | PartialPerson | PropertyPerson | NonCitizenPerson`.
export const Status = Object.freeze({
  FULL: 'FullPerson',
  PARTIAL: 'PartialPerson',
  NONCITIZEN: 'NonCitizenPerson',
  PROPERTY: 'PropertyPerson',
});

// How dominated each status is (0 = full standing, 1 = chattel).
export const dominationOf = Object.freeze({
  FullPerson: 0.0,
  PartialPerson: 0.4,
  NonCitizenPerson: 0.7,
  PropertyPerson: 1.0,
});

// The coercive "moves" the simulation may try to apply to a region. These are
// the illegal state transitions of an unsound order:
//   Human -> Property, Person -> NonPerson, Emergency -> PermanentPower, ...
export const Move = Object.freeze({
  RECLASSIFY: 'reclassify-personhood', //  Human      -> lesser status
  SUSPEND_DUE_PROCESS: 'suspend-due-process', //  Person     -> RightlessSubject
  SUSPEND_EQUAL_PROTECTION: 'suspend-equal-protection',
  RESTRICT_LIBERTY: 'restrict-liberty',
  DECLARE_EMERGENCY: 'declare-emergency',
  MAKE_EMERGENCY_PERMANENT: 'make-emergency-permanent', //  Emergency -> PermanentPower
  UNREVIEWABLE_COERCION: 'unreviewable-coercion', //  Policing  -> UnreviewableCoercion
});

// The verdict the type checker returns for a move.
export const Verdict = Object.freeze({
  UNREPRESENTABLE: 'unrepresentable', // type error: this move cannot exist here
  REQUIRES_PROOF: 'requires-proof', // admissible only if obligation discharged
  PERMITTED: 'permitted', // legal move
});

// Under a SOUND constitution these moves are simply not in the transition
// relation. Attempting one is a type error — there is no constructor for it.
const SOUND_UNREPRESENTABLE = new Set([
  Move.RECLASSIFY,
  Move.SUSPEND_DUE_PROCESS,
  Move.SUSPEND_EQUAL_PROTECTION,
  Move.MAKE_EMERGENCY_PERMANENT,
  Move.UNREVIEWABLE_COERCION,
]);

// Under a SOUND constitution these moves are admissible, but ONLY when a proof
// obligation is discharged: the measure must be narrowly tailored to a real
// threat AND subject to genuine review.
const SOUND_REQUIRES_PROOF = new Set([Move.RESTRICT_LIBERTY, Move.DECLARE_EMERGENCY]);

// The proof obligation a sound constitution demands before an admissible-but-
// constrained coercive measure may take effect. The obligation is discharged
// only when the institution is actually capable of review (rights enforcement +
// legitimacy) and the measure answers an articulable threat (non-trivial fear).
//
// Mirrors the Idris `record Justification { reviewable, narrow }` plus the
// `SoundRestrict` constructor that *demands* a proof argument.
export function dischargeObligation(move, ctx) {
  const reviewable = ctx.rightsEnforcement >= 0.5 && ctx.legitimacy >= 0.45;
  const narrow = ctx.fear >= 0.35; // a real, articulable threat exists
  const ok = reviewable && narrow;
  return {
    ok,
    reviewable,
    narrow,
    detail: ok
      ? 'obligation discharged: reviewable institution + narrowly-tailored measure'
      : `obligation NOT discharged (reviewable=${reviewable}, narrow=${narrow})`,
  };
}

// The hidden cost an UNSOUND order books for each coercive move. Order arrives
// fast; the debt accrues silently and detonates under shock.
export function legitimacyDebtOf(move) {
  switch (move) {
    case Move.RECLASSIFY:
      return 0.2;
    case Move.UNREVIEWABLE_COERCION:
      return 0.16;
    case Move.SUSPEND_EQUAL_PROTECTION:
      return 0.14;
    case Move.SUSPEND_DUE_PROCESS:
      return 0.12;
    case Move.MAKE_EMERGENCY_PERMANENT:
      return 0.1;
    case Move.DECLARE_EMERGENCY:
      return 0.04;
    case Move.RESTRICT_LIBERTY:
      return 0.03;
    default:
      return 0;
  }
}

// ─────────────────────────────────────────────────────────────────────────────
// THE TYPE CHECKER
// ─────────────────────────────────────────────────────────────────────────────
//
// Given a constitution mode, a coercive move, and the live region context,
// decide whether the move is even representable — and if so, on what terms.
//
// Return shape:
//   { verdict, allowed, legitimacyDebt, reason, proof? }
export function checkTransition(mode, move, ctx = {}) {
  if (mode === Mode.UNSOUND) {
    // The broken type system: every coercive move is a permitted total
    // function. We still surface the hidden cost it books.
    const debt = legitimacyDebtOf(move);
    return {
      verdict: Verdict.PERMITTED,
      allowed: true,
      legitimacyDebt: debt,
      reason: `unsound constitution permits ${move} — books legitimacy debt ${debt.toFixed(2)}`,
    };
  }

  // SOUND constitution.
  if (SOUND_UNREPRESENTABLE.has(move)) {
    return {
      verdict: Verdict.UNREPRESENTABLE,
      allowed: false,
      legitimacyDebt: 0,
      reason: `type error: ${move} is unrepresentable under a sound constitution`,
    };
  }

  if (SOUND_REQUIRES_PROOF.has(move)) {
    const proof = dischargeObligation(move, ctx);
    return {
      verdict: Verdict.REQUIRES_PROOF,
      allowed: proof.ok,
      legitimacyDebt: 0, // a lawful, reviewed, narrow measure books no debt
      reason: `${move}: ${proof.detail}`,
      proof,
    };
  }

  // Non-coercive moves are always fine.
  return { verdict: Verdict.PERMITTED, allowed: true, legitimacyDebt: 0, reason: `${move} permitted` };
}

// The maximum personhood downgrade the constitution will allow in one step.
//   Sound:   0   (Property is unrepresentable; standing is rank-monotone)
//   Unsound: 1   (anyone may be reclassified all the way to Property)
export function maxDowngrade(mode) {
  return mode === Mode.SOUND ? 0 : 1;
}

// Convenience: is a given coercive move available at all in this mode?
export function isRepresentable(mode, move, ctx = {}) {
  return checkTransition(mode, move, ctx).verdict !== Verdict.UNREPRESENTABLE;
}

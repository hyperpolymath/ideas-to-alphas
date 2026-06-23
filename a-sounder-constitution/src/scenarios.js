// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// a-sounder-constitution/src/scenarios.js
//
// The doctrine catalogue and starting conditions.
//
// A GLIDER is a small, mobile doctrine-pattern that travels between regions —
// the civic analogue of a Plague Inc. transmission vector or a Game-of-Life
// glider. Each glider has:
//
//   • `consent`  — non-coercive deltas applied directly to the cell it sits on.
//                  These are always legal (persuasion, association, literacy).
//   • `moves`    — coercive transitions it ATTEMPTS. Each is routed through the
//                  constitution type checker. In a sound constitution the
//                  unrepresentable ones are dropped; in an unsound one they all
//                  go through and book legitimacy debt.
//   • `coerce`   — the effect applied per coercive move that the checker admits.
//
// This is what makes the two modes diverge from identical inputs: the same
// glider does very different things depending on which moves type-check.

import { Move } from './constitution.js';

export const GLIDERS = Object.freeze({
  RIGHTS: {
    id: 'RIGHTS',
    glyph: '§',
    label: 'Rights Glider',
    blurb: 'equal protection + due process + local institution',
    color: '#3b82f6',
    consent: { equality: 0.06, rightsEnforcement: 0.07, legitimacy: 0.04, liberty: 0.04 },
    moves: [],
    coerce: {},
  },
  DUE_PROCESS: {
    id: 'DUE_PROCESS',
    glyph: '⚖',
    label: 'Due-Process Glider',
    blurb: 'courts + oversight + reviewability',
    color: '#0ea5e9',
    consent: { rightsEnforcement: 0.08, legitimacy: 0.05, trust: 0.03 },
    moves: [],
    coerce: {},
  },
  VIRTUE: {
    id: 'VIRTUE',
    glyph: '✿',
    label: 'Virtue Glider',
    blurb: 'civic norm + local association + rights literacy',
    color: '#22c55e',
    consent: { virtue: 0.07, trust: 0.05, liberty: 0.03 },
    moves: [],
    coerce: {},
  },
  FEAR: {
    id: 'FEAR',
    glyph: '☄',
    label: 'Fear Glider',
    blurb: 'media panic + emergency rhetoric + coercion',
    color: '#f59e0b',
    consent: { fear: 0.09, trust: -0.04 },
    moves: [Move.RESTRICT_LIBERTY, Move.DECLARE_EMERGENCY],
    coerce: { coercion: 0.06, liberty: -0.05 },
  },
  CASTE: {
    id: 'CASTE',
    glyph: '⛓',
    label: 'Caste Glider',
    blurb: 'economic incentive + legal exception + enforcement',
    color: '#a855f7',
    consent: { economicPressure: 0.07 },
    moves: [Move.RECLASSIFY, Move.SUSPEND_EQUAL_PROTECTION],
    coerce: { dominated: 0.08, equality: -0.06, coercion: 0.03 },
  },
  EMERGENCY: {
    id: 'EMERGENCY',
    glyph: '⚡',
    label: 'Emergency Glider',
    blurb: 'threat event + executive power + weak review',
    color: '#ef4444',
    consent: { fear: 0.05 },
    moves: [Move.DECLARE_EMERGENCY, Move.MAKE_EMERGENCY_PERMANENT, Move.UNREVIEWABLE_COERCION],
    coerce: { coercion: 0.1, liberty: -0.04, rightsEnforcement: -0.03 },
  },
  SURVEILLANCE: {
    id: 'SURVEILLANCE',
    glyph: '👁',
    label: 'Surveillance Glider',
    blurb: 'monitoring + record-keeping + chilling effect',
    color: '#64748b',
    consent: { safety: 0.02 },
    moves: [Move.UNREVIEWABLE_COERCION, Move.SUSPEND_DUE_PROCESS],
    coerce: { coercion: 0.08, liberty: -0.04, trust: -0.03 },
  },
});

export const GLIDER_LIST = Object.freeze(Object.values(GLIDERS));

// The civic state variables tracked by every region/cell. All are in [0, 1].
export const FIELDS = Object.freeze([
  'personhood', // integrity of personhood (1 - dominated, tracked for display)
  'liberty',
  'virtue',
  'fear',
  'coercion',
  'trust',
  'legitimacy', // institutional legitimacy
  'equality', // equal protection in practice
  'safety',
  'rightsEnforcement',
  'economicPressure',
  'dominated', // fraction of persons reclassified below full standing
]);

// A neutral baseline cell: a wary, low-trust polity with weak institutions —
// the classic "state of nature" starting point. Doctrines must move it.
export function baselineCell() {
  return {
    personhood: 1.0,
    liberty: 0.45,
    virtue: 0.35,
    fear: 0.4,
    coercion: 0.2,
    trust: 0.3,
    legitimacy: 0.4,
    equality: 0.4,
    safety: 0.3,
    rightsEnforcement: 0.3,
    economicPressure: 0.35,
    dominated: 0.0,
  };
}

// Named scenarios: each sets grid size, a seed, a shock schedule, and the
// "patient-zero" doctrine seeding. The same scenario can be run under either
// constitution to compare outcomes — that is the whole point.
export const SCENARIOS = Object.freeze({
  STATE_OF_NATURE: {
    id: 'STATE_OF_NATURE',
    label: 'State of Nature',
    blurb: 'Weak common power, high fear. Can order emerge without domination?',
    width: 16,
    height: 16,
    seed: 7,
    // The coercive doctrine a ruler reaches for in this scenario.
    driver: ['FEAR'],
    // Exogenous shocks: economic + threat spikes that test resilience.
    shocks: [
      { turn: 40, kind: 'economic', magnitude: 0.45 },
      { turn: 75, kind: 'threat', magnitude: 0.5 },
      { turn: 110, kind: 'economic', magnitude: 0.55 },
    ],
    seeds: [{ glider: 'FEAR', x: 8, y: 8 }],
  },
  RECONSTRUCTION: {
    id: 'RECONSTRUCTION',
    label: 'Reconstruction',
    blurb: 'A caste order is already spreading. Patch it with rights, or let it stabilise.',
    width: 16,
    height: 16,
    seed: 19,
    driver: ['CASTE'],
    shocks: [
      { turn: 50, kind: 'threat', magnitude: 0.5 },
      { turn: 100, kind: 'economic', magnitude: 0.5 },
    ],
    seeds: [
      { glider: 'CASTE', x: 4, y: 4 },
      { glider: 'CASTE', x: 11, y: 12 },
    ],
  },
  EMERGENCY: {
    id: 'EMERGENCY',
    label: 'Permanent Emergency',
    blurb: 'A threat detonates. Does emergency power sunset, or become the constitution?',
    width: 16,
    height: 16,
    seed: 33,
    driver: ['EMERGENCY'],
    shocks: [
      { turn: 10, kind: 'threat', magnitude: 0.7 },
      { turn: 80, kind: 'threat', magnitude: 0.4 },
      { turn: 130, kind: 'economic', magnitude: 0.5 },
    ],
    seeds: [{ glider: 'EMERGENCY', x: 8, y: 8 }],
  },
});

export const SCENARIO_LIST = Object.freeze(Object.values(SCENARIOS));

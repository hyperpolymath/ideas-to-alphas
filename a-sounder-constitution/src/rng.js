// SPDX-License-Identifier: MPL-2.0
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
// a-sounder-constitution/src/rng.js
//
// A tiny seeded PRNG (mulberry32). The whole simulation is deterministic given
// a seed, so the sound-vs-unsound comparison is reproducible and the tests are
// stable. No dependencies — runs identically in the browser and in Node.

export function mulberry32(seed) {
  let a = seed >>> 0;
  return function next() {
    a |= 0;
    a = (a + 0x6d2b79f5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// Convenience wrapper exposing a few helpers over a seeded stream.
export function makeRng(seed = 1) {
  const next = mulberry32(seed);
  return {
    next, // float in [0, 1)
    range: (lo, hi) => lo + (hi - lo) * next(),
    int: (lo, hi) => lo + Math.floor((hi - lo + 1) * next()),
    chance: (p) => next() < p,
  };
}

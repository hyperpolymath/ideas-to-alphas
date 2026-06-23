-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- a-sounder-constitution/formal/Constitution.idr
--
-- THE THESIS, AT THE TYPE LEVEL.
--
-- The simulator's claim is that *rights are type constraints on legal state
-- transitions, not resources*. In the JavaScript engine that claim is enforced
-- dynamically (the type checker drops coercive moves). Here it is enforced
-- STATICALLY: under a sound constitution, reducing a person to property is not
-- a move that fails at runtime — it is a term that cannot be written, because
-- the type it would need to inhabit has no such inhabitant.
--
-- We make three statements precise and prove them:
--
--   (1) UNREPRESENTABILITY. In the sound world the personhood type has no
--       `Property` constructor. The embedding into the (unsound) `Human` space
--       provably never yields `PropertyPerson`.  →  soundNeverProperty
--
--   (2) MONOTONICITY. Every legal personhood transition under a sound
--       constitution can only recognise or upgrade standing, never strip it.
--       →  soundMonotone
--
--   (3) PROOF OBLIGATION. A liberty restriction is admissible only when it
--       carries evidence that it is reviewable and narrowly tailored; the type
--       of a lawful restriction *demands* those proofs as arguments.
--       →  SoundRestrict, lawfulRestriction
--
-- Contrast: in the unsound world `Property` is an ordinary constructor and
-- reclassification is a total function any human can be fed to.
--
-- VERIFICATION STATUS: written to compile under Idris2 with `%default total`
-- and zero `believe_me` / `assert_total`. It has NOT yet been run through
-- Idris2 in this environment (no idris2 on PATH); treat the "proved" claims as
-- pending CI, in line with this repo's blocker-tracking convention. The JS
-- mirror in ../src/constitution.js IS exercised by the test suite.

module Constitution

import Data.Nat

%default total

-- ─────────────────────────────────────────────────────────────────────────────
-- The UNSOUND human type — the broken data declaration.
-- ─────────────────────────────────────────────────────────────────────────────
--
--   data Human = FullPerson | PartialPerson | PropertyPerson | NonCitizenPerson
--
-- `PropertyPerson` is a perfectly ordinary inhabitant. Personhood is just a tag,
-- so anyone can be re-tagged. This is the unsound constitution: the type system
-- offers no obstacle to domination.

public export
data Human = FullPerson | PartialPerson | PropertyPerson | NonCitizenPerson

||| Under the unsound constitution, reclassification is a total function: any
||| human may be reduced to property. Domination is cheap and always available.
public export
unsoundReclassify : Human -> Human
unsoundReclassify _ = PropertyPerson

||| ...and `Property` is therefore reachable from every starting point.
public export
unsoundReachesProperty : (h : Human) -> unsoundReclassify h = PropertyPerson
unsoundReachesProperty _ = Refl

-- ─────────────────────────────────────────────────────────────────────────────
-- The SOUND person type — Property is unrepresentable by construction.
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The sound constitution does not model "person who happens not to be property".
-- It models a type whose grammar has no way to *say* property at all. This is
-- the type-level form of the record
--
--   record Human where
--     personhood      : Personhood
--     notProperty     : NotProperty      -- carried as evidence, not a flag
--     dueProcess      : DueProcess
--     equalProtection : EqualProtection
--
-- collapsed to its load-bearing core: the set of admissible standings.

public export
data Person = Full | Partial | NonCitizen
-- Note the deliberate absence of any `Property` constructor.

||| Embed sound standing back into the unsound vocabulary, so the two worlds are
||| comparable. Crucially, the image of `embed` never includes `PropertyPerson`.
public export
embed : Person -> Human
embed Full       = FullPerson
embed Partial    = PartialPerson
embed NonCitizen = NonCitizenPerson

-- (1) UNREPRESENTABILITY ──────────────────────────────────────────────────────
--
||| Theorem: under a sound constitution, nothing is property.
||| For every sound standing `p`, `embed p` is provably not `PropertyPerson`.
||| Each case is *impossible* — there is no equation to refute, because the
||| constructors differ. This is "rights are type constraints" as a proof:
||| Person -> Property is not a transition that is forbidden; it is a transition
||| that cannot be named.
public export
soundNeverProperty : (p : Person) -> Not (embed p = PropertyPerson)
soundNeverProperty Full       Refl impossible
soundNeverProperty Partial    Refl impossible
soundNeverProperty NonCitizen Refl impossible

-- ─────────────────────────────────────────────────────────────────────────────
-- (2) MONOTONICITY — legal standing transitions can only level up.
-- ─────────────────────────────────────────────────────────────────────────────

||| A numeric rank for standing, used only to state the monotonicity theorem.
public export
rank : Person -> Nat
rank Full       = 2
rank Partial    = 1
rank NonCitizen = 0

||| The legal personhood transitions a sound constitution offers. Observe that
||| every constructor's *target* has rank greater than or equal to its source:
||| standing may be kept, recognised, or naturalised — never stripped. There is
||| deliberately no `Demote`/`Strip`/`Enslave` constructor to write.
public export
data SoundStep : Person -> Person -> Type where
  Keep       : SoundStep p p
  Recognise  : SoundStep Partial Full
  Naturalise : SoundStep NonCitizen Full

||| Theorem: every sound step is rank-monotone. Standing is never reduced.
||| (The Reconstruction-style rights patch — only ever upward — is exactly the
||| set of moves this type admits.)
public export
soundMonotone : SoundStep a b -> LTE (rank a) (rank b)
soundMonotone Keep       = lteRefl          -- rank p <= rank p
soundMonotone Recognise  = LTESucc LTEZero  -- 1 <= 2
soundMonotone Naturalise = LTEZero          -- 0 <= 2

-- ─────────────────────────────────────────────────────────────────────────────
-- (3) PROOF OBLIGATION — coercion that is admissible-but-constrained.
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Not every coercive move is unrepresentable. A sound constitution permits, say,
-- a liberty restriction — but only on terms. The type of a lawful restriction
-- *demands* the proofs as arguments, so an unjustified restriction is, again,
-- not a term you can construct.

public export
record Justification where
  constructor MkJustification
  reviewable : Bool   -- subject to genuine review
  narrow     : Bool   -- narrowly tailored to an articulable threat

||| A lawful liberty restriction under a sound constitution. You cannot build one
||| without supplying proof that the justification is BOTH reviewable AND narrow.
public export
data SoundRestrict : Type where
  Restrict : (j : Justification)
          -> (reviewable j = True)
          -> (narrow j = True)
          -> SoundRestrict

||| A discharged obligation type-checks: reviewable and narrow are both `True`,
||| so both proofs are `Refl`.
public export
lawfulRestriction : SoundRestrict
lawfulRestriction = Restrict (MkJustification True True) Refl Refl

-- An UNlawful restriction does not type-check. Uncommenting the following is a
-- compile error, because `False = True` is uninhabited — there is no `Refl`:
--
--   unlawful : SoundRestrict
--   unlawful = Restrict (MkJustification False True) Refl Refl
--                                                    ^^^^  False = True  (no such proof)
--
-- That compile error IS the constitution doing its job.

-- ─────────────────────────────────────────────────────────────────────────────
-- Capstone: the contrast in one place.
-- ─────────────────────────────────────────────────────────────────────────────
--
--   • unsoundReclassify : Human -> Human          -- total; Property always reachable
--   • soundNeverProperty : ... -> Not (... = PropertyPerson)
--                                                  -- Property never reachable
--
-- Same intent ("reclassify a person"), two constitutions, two type systems:
-- in one it is a function, in the other it is a refuted proposition. The
-- difference in long-run outcomes the simulator measures (caste stability vs.
-- rights-preserving resilience) is downstream of exactly this distinction.

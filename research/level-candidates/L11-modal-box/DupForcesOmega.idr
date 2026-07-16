-- SPDX-License-Identifier: MPL-2.0
-- Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
--
-- research/level-candidates/L11-modal-box/DupForcesOmega.idr
--
-- Machine-checks the central claim of QTT-INTEGRATION.adoc section 5:
--
--     an ungraded `dup : Box a -> (Box a, Box a)` is admissible only where
--     r + r = r, hence only at r in {Zero, Many}.
--
-- Verified with Idris2 0.7.0:  idris2 --check DupForcesOmega.idr
--
-- This file supplies the semiring content that Modal.idr's `Multiplicity` never
-- had.  Modal.idr titles its section "the QTT multiplicity semiring from L10"
-- but defines a bare three-constructor enumeration: no (+), no (*), no laws, and
-- `Box` is not indexed by it.  That absence is precisely why the `dup` defect
-- survived unnoticed -- with no (+) in scope, `r + r = r` was not a question
-- anyone could ask.

module DupForcesOmega

-- ─────────────────────────────────────────────────────────────────────────────
-- The L10 usage multiplicities
-- ─────────────────────────────────────────────────────────────────────────────

data Multiplicity = Zero | One | Many

-- ─────────────────────────────────────────────────────────────────────────────
-- Semiring addition: how uses combine when a resource is SPLIT
-- ─────────────────────────────────────────────────────────────────────────────
--
-- The key entry is `plus One One = Many`: using a linear thing twice is
-- unrestricted use.  Everything below follows from that one line.

plus : Multiplicity -> Multiplicity -> Multiplicity
plus Zero Zero = Zero
plus Zero One  = One
plus Zero Many = Many
plus One  Zero = One
plus One  One  = Many
plus One  Many = Many
plus Many Zero = Many
plus Many One  = Many
plus Many Many = Many

-- ─────────────────────────────────────────────────────────────────────────────
-- Semiring multiplication: how uses compose when boxes NEST
-- ─────────────────────────────────────────────────────────────────────────────

mult : Multiplicity -> Multiplicity -> Multiplicity
mult Zero Zero = Zero
mult Zero One  = Zero
mult Zero Many = Zero
mult One  Zero = Zero
mult One  One  = One
mult One  Many = Many
mult Many Zero = Zero
mult Many One  = Many
mult Many Many = Many

-- ─────────────────────────────────────────────────────────────────────────────
-- The theorem
-- ─────────────────────────────────────────────────────────────────────────────

||| `dup : Box a -> (Box a, Box a)` returns two boxes at the SAME grade as its
||| input.  The only rule producing `Box r a` and `Box s a` from one box is
|||
|||     split : Box (r + s) a -> (Box r a, Box s a)
|||
||| Instantiating s := r gives premise `Box (r + r) a`, while the input `dup`
||| declares is `Box r a`.  Hence `dup` is admissible only where  r + r = r.
|||
||| This proves that constraint pins r to {Zero, Many} -- One is excluded.
dupForcesOmega : (r : Multiplicity) -> plus r r = r -> Either (r = Zero) (r = Many)
dupForcesOmega Zero Refl = Left Refl
dupForcesOmega One  Refl impossible
dupForcesOmega Many Refl = Right Refl

-- ─────────────────────────────────────────────────────────────────────────────
-- The three idempotence facts, separately
-- ─────────────────────────────────────────────────────────────────────────────

||| Zero is idempotent under (+).
zeroIdempotent : plus Zero Zero = Zero
zeroIdempotent = Refl

||| Many is idempotent under (+).  This is the grade `dup` actually lives at.
manyIdempotent : plus Many Many = Many
manyIdempotent = Refl

||| One is NOT idempotent under (+): the linear grade cannot be duplicated.
||| This single fact is the whole defect.
oneNotIdempotent : Not (plus One One = One)
oneNotIdempotent Refl impossible

-- ─────────────────────────────────────────────────────────────────────────────
-- Why {Zero, Many} collapses to just Many in practice
-- ─────────────────────────────────────────────────────────────────────────────
--
-- QTT-INTEGRATION.adoc s4 gates extraction on 1 <= r:
--
--     unbox : Box r a -> a     requires  One <= r
--
-- At r = Zero the content is erased and `unbox` is inadmissible, so a
-- `Box Zero a` carries nothing a program can observe.  Every USEFUL instance of
-- the ungraded `dup` therefore pins r = Many -- i.e. `Box a` as written in
-- Modal.idr is isomorphic to an L10 value at multiplicity omega, and L11 adds
-- nothing over L10 until `dup` is replaced by `split`.
--
-- Coda.  Idris2's own Prelude already contains
--
--     Prelude.dup : a -> (a, a)      -- "Function that duplicates its input"
--
-- which is exactly unrestricted duplication.  Modal.idr's `dup` collides with it
-- by name, and the collision is not a coincidence: at r = Many, the box's `dup`
-- IS Prelude.dup up to the MkBox wrapper.  Until 2026-07-16 that name clash made
-- Modal.idr fail to elaborate entirely (`Ambiguous elaboration: Modal.dup vs
-- Prelude.dup`), which meant the comonad laws it claimed to prove had never been
-- checked by anything.  The compiler was pointing at the defect the whole time.

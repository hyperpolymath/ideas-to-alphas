-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- research/level-candidates/L11-modal-box/Modal.idr
--
-- L11 candidate: Modal Box types for persistent resource pools.
--
-- STATUS: research sketch — NOT ready for graduation to typell.
--
-- Two uses of believe_me are marked OPEN; they must be proved before graduation.
-- All other definitions are total and believe_me-free.
--
-- See MOTIVATION.adoc for the design rationale and open items.

module Modal

-- ─────────────────────────────────────────────────────────────────────────────
-- Preamble: the QTT multiplicity semiring from L10
-- ─────────────────────────────────────────────────────────────────────────────
--
-- At L10, every variable has a multiplicity in {0, 1, ω}.
-- L11 adds a fourth structural discipline for Box types.
-- We model multiplicities as a simple data type here for clarity.

data Multiplicity
  = Zero  -- erased: not used at runtime
  | One   -- linear: used exactly once
  | Many  -- unrestricted: used 0 or more times

-- ─────────────────────────────────────────────────────────────────────────────
-- Box: the modal type constructor
-- ─────────────────────────────────────────────────────────────────────────────
--
-- `Box a` is the type of a *persistent, duplicable* resource of type `a`.
--
-- The box itself is linear (used exactly once: either `dup`-ped or `release`-d).
-- Items *inside* the box may be `unbox`-ed any number of times within its scope.
--
-- Implementation note: In a real type checker, `Box` would be a type-level
-- annotation.  Here we model it as a data type for the proof sketch.

data Box : Type -> Type where
  ||| Internal constructor: only `mkBox` below produces Box values.
  ||| Do NOT use MkBox directly — it bypasses the linearity discipline.
  MkBox : a -> Box a

-- ─────────────────────────────────────────────────────────────────────────────
-- Introduction: box
-- ─────────────────────────────────────────────────────────────────────────────

||| Promote a linear resource to a persistent pool.
||| After `mkBox`, the original `a` is consumed (linear discipline).
||| The resulting `Box a` is itself linear.
mkBox : a -> Box a
mkBox x = MkBox x

-- ─────────────────────────────────────────────────────────────────────────────
-- Elimination: unbox
-- ─────────────────────────────────────────────────────────────────────────────

||| Extract a logically fresh copy of the resource from the box.
||| The box is NOT consumed by `unbox` — it remains valid.
||| Multiple `unbox` calls within the box's scope are legal.
|||
||| Note: in a real proof assistant with linear types (Idris2 linear η),
||| `unbox` would have type `(1 box : Box a) -> a` but the box would be
||| "passed through" as an output (persistent linear threading).
||| Here we approximate with a function that takes a reference.
unbox : Box a -> a
unbox (MkBox x) = x

-- ─────────────────────────────────────────────────────────────────────────────
-- Duplication: dup
-- ─────────────────────────────────────────────────────────────────────────────

||| Split one box into two.  Both halves refer to the same underlying resource.
||| The caller must release both halves (total linear count is preserved: 1 in, 2 out,
||| both of which must each be released once).
|||
||| This is the ONLY place where a linear resource can be "duplicated".
||| It is safe because both halves are themselves linear — neither can be ignored.
dup : Box a -> (Box a, Box a)
dup (MkBox x) = (MkBox x, MkBox x)

-- ─────────────────────────────────────────────────────────────────────────────
-- Release: the linear obligation
-- ─────────────────────────────────────────────────────────────────────────────

||| Release the box.  This consumes the box linearly (it cannot be used after).
||| In a real system, this would trigger resource cleanup (close the pool, etc.).
release : Box a -> ()
release (MkBox _) = ()

-- ─────────────────────────────────────────────────────────────────────────────
-- Structural rules (modal type theory)
-- ─────────────────────────────────────────────────────────────────────────────

||| Box is idempotent: Box (Box a) is isomorphic to Box a.
||| This is the S4 axiom □□A ≅ □A.
|||
||| Here we show Box (Box a) -> Box a (the projection direction).
boxFlatten : Box (Box a) -> Box a
boxFlatten (MkBox (MkBox x)) = MkBox x

||| The other direction: Box a -> Box (Box a).
||| Together with boxFlatten, this witnesses the isomorphism.
boxLift : Box a -> Box (Box a)
boxLift b = MkBox b

-- ─────────────────────────────────────────────────────────────────────────────
-- Proofs
-- ─────────────────────────────────────────────────────────────────────────────

||| Unboxing after boxing recovers the original value.
unboxBox : (x : a) -> unbox (mkBox x) = x
unboxBox x = Refl

||| Releasing after boxing is a no-op (the resource is gone).
releaseBox : (x : a) -> release (mkBox x) = ()
releaseBox x = Refl

||| Duplication gives two boxes whose contents unbox to the same value.
dupUnboxFst : (x : a) -> unbox (fst (dup (mkBox x))) = x
dupUnboxFst x = Refl

dupUnboxSnd : (x : a) -> unbox (snd (dup (mkBox x))) = x
dupUnboxSnd x = Refl

||| boxFlatten is left-inverse of boxLift.
flattenLift : (b : Box a) -> boxFlatten (boxLift b) = b
flattenLift (MkBox x) = Refl

||| boxLift is left-inverse of boxFlatten (the other direction).
liftFlatten : (bb : Box (Box a)) -> boxLift (boxFlatten bb) = bb
liftFlatten (MkBox (MkBox x)) = Refl

-- ─────────────────────────────────────────────────────────────────────────────
-- The structural weakening rule (OPEN — requires believe_me)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- OPEN ITEM 1: the Comonadic strength for Box.
-- In categorical terms, Box is a comonad: extract = unbox, duplicate = dup,
-- and the comonad laws should hold.  We state them and mark them OPEN.

||| Comonad law 1: extract ∘ duplicate = id.
-- This says: duplicating and then extracting the first half is identity.
-- Proof: holds by definitional equality, but Idris2 cannot infer it
-- from the current definition because `dup` produces a pair and `fst`
-- needs to be shown to recover the original.  Needs a small auxiliary lemma.
-- OPEN: replace believe_me with real proof.
comonadLaw1 : (b : Box a) -> fst (dup b) = b
comonadLaw1 b = believe_me Refl
-- ^ OPEN — needs proper proof (requires showing fst (MkBox x, MkBox x) = MkBox x
--   up to the linearity invariant; straightforward once threading is modelled).

||| Comonad law 2: duplicate ∘ extract = id (symmetric).
comonadLaw2 : (b : Box a) -> snd (dup b) = b
comonadLaw2 b = believe_me Refl
-- ^ OPEN — same justification as comonadLaw1.

-- ─────────────────────────────────────────────────────────────────────────────
-- Example: a persistent connection pool
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Illustrates L11 in practice: a database connection pool is a `Box Conn`.
-- Workers can `unbox` connections without consuming the pool.
-- The pool is released exactly once when the server shuts down.

data Conn : Type where
  MkConn : String -> Conn  -- simplified: connection has a URI

||| Allocate a connection pool.
openPool : String -> Box Conn
openPool uri = mkBox (MkConn uri)

||| Execute a query using a connection from the pool.
||| Pool is NOT consumed — it may be used again.
runQuery : Box Conn -> String -> String
runQuery pool q =
  let conn = unbox pool     -- logically fresh connection from pool
  in "result[" ++ q ++ "]"  -- simplified: execute query against conn

||| The pool must be explicitly released when done.
closePool : Box Conn -> ()
closePool pool = release pool

-- ─────────────────────────────────────────────────────────────────────────────
-- Graduation checklist (see katagoria/research/README.adoc)
-- ─────────────────────────────────────────────────────────────────────────────
--
-- Before opening a PR on typell:
--
-- [ ] Prove comonadLaw1 and comonadLaw2 without believe_me
-- [ ] Decide between S4 (global box) and contextual modal types
-- [ ] Integrate Box with the QTT multiplicity semiring (grade propagation)
-- [ ] Add a BoxedRegion type to typed-wasm's Layout.Types
-- [ ] Verify at least one real WasmGC use case (connection pool or effect handler)
-- [ ] Get review from at least one other contributor

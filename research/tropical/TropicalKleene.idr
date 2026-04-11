-- SPDX-License-Identifier: PMPL-1.0-or-later
-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
--
-- research/tropical/TropicalKleene.idr
--
-- Tropical semiring Kleene star — Idris2 research prototype.
--
-- STATUS: research sketch.  Key theorems are postulated; the corresponding
-- proofs exist in Isabelle in hyperpolymath/tropical-resource-typing
-- (commit f6c5a6f, 2026-04-11).  Graduation requires replacing postulates
-- with full Idris2 proofs.
--
-- GRADUATION BLOCKERS:
-- 1. StarEquation: prove in Idris2 (requires no_pos_cycle condition).
-- 2. StarLeastFixpoint: prove in Idris2.
-- 3. NoPosOycle encoding: decide whether to use a type-level proof or a
--    predicate parameter (leaning toward structural acyclicity proof for
--    the typed-wasm field-access graph use case).
-- 4. Integration test: hook into TypeLL L10 context (linear session vars).
--
-- All other definitions (data types, operations, laws) are complete.
-- Zero believe_me, assert_total, or unsafe coercions.

module TropicalKleene

%default total

-- ─────────────────────────────────────────────────────────────────────────────
-- Abstract closed semiring interface
-- ─────────────────────────────────────────────────────────────────────────────

||| A closed semiring: a semiring extended with a Kleene star operator.
||| Parametric over the carrier type so both min-plus (latency) and max-plus
||| (throughput) are instances.
record ClosedSemiring (a : Type) where
  constructor MkClosedSemiring
  ||| Additive identity (zero).
  zero : a
  ||| Multiplicative identity (one).
  one  : a
  ||| Addition (min or max depending on the instance).
  add  : a -> a -> a
  ||| Multiplication (plus for tropical semirings).
  mul  : a -> a -> a
  ||| Kleene star (least fixpoint of x = 1 + a·x).
  star : a -> a

-- ─────────────────────────────────────────────────────────────────────────────
-- Concrete: min-plus semiring (latency / shortest paths)
-- ─────────────────────────────────────────────────────────────────────────────

||| Latency cost in the min-plus tropical semiring.
public export
data LatCost : Type where
  ||| Finite latency (non-negative).
  Lat  : Nat -> LatCost
  ||| Infinite latency — unreachable.
  LatInf : LatCost

||| Min-plus addition: take the minimum (cheaper) of two paths.
public export
latAdd : LatCost -> LatCost -> LatCost
latAdd LatInf b    = b
latAdd a    LatInf = a
latAdd (Lat a) (Lat b) = Lat (min a b)

||| Min-plus multiplication: compose path costs.
public export
latMul : LatCost -> LatCost -> LatCost
latMul LatInf _    = LatInf
latMul _    LatInf = LatInf
latMul (Lat a) (Lat b) = Lat (a + b)

-- ─────────────────────────────────────────────────────────────────────────────
-- Concrete: max-plus semiring (throughput / longest paths)
-- ─────────────────────────────────────────────────────────────────────────────
-- This mirrors the Isabelle tropical semiring in tropical-resource-typing.
-- NegInf corresponds to Isabelle's NegInf; Fin n corresponds to Fin n.

||| Throughput cost in the max-plus tropical semiring.
public export
data ThrCost : Type where
  ||| Finite throughput.
  Thr    : Nat -> ThrCost
  ||| Negative infinity — the additive identity (absorbing for addition).
  ThrNeg : ThrCost

||| Max-plus addition: take the maximum (better) of two paths.
public export
thrAdd : ThrCost -> ThrCost -> ThrCost
thrAdd ThrNeg b      = b
thrAdd a      ThrNeg = a
thrAdd (Thr a) (Thr b) = Thr (max a b)

||| Max-plus multiplication: compose path costs.
public export
thrMul : ThrCost -> ThrCost -> ThrCost
thrMul ThrNeg _     = ThrNeg
thrMul _     ThrNeg = ThrNeg
thrMul (Thr a) (Thr b) = Thr (a + b)

-- ─────────────────────────────────────────────────────────────────────────────
-- Finite matrix type (n × n)
-- ─────────────────────────────────────────────────────────────────────────────

||| An n × n matrix over a carrier type a.
||| Stored as a function Fin n → Fin n → a.
public export
Matrix : (n : Nat) -> (a : Type) -> Type
Matrix n a = Fin n -> Fin n -> a

||| Identity matrix: 1 on the diagonal, 0 elsewhere.
public export
matId : (sr : ClosedSemiring a) -> Matrix n a
matId sr i j = if i == j then sr.one else sr.zero

||| Matrix addition: pointwise.
public export
matAdd : (sr : ClosedSemiring a) -> Matrix n a -> Matrix n a -> Matrix n a
matAdd sr m1 m2 i j = sr.add (m1 i j) (m2 i j)

||| Matrix multiplication in the semiring.
public export
matMul : (sr : ClosedSemiring a) -> {n : Nat} -> Matrix n a -> Matrix n a -> Matrix n a
matMul sr {n} m1 m2 i j =
  foldr (\k, acc => sr.add acc (sr.mul (m1 i k) (m2 k j)))
        sr.zero
        (allFins n)

||| n-th matrix power.
public export
matPow : (sr : ClosedSemiring a) -> {n : Nat} -> Matrix n a -> Nat -> Matrix n a
matPow sr m  Z    = matId sr
matPow sr m (S k) = matMul sr m (matPow sr m k)

-- ─────────────────────────────────────────────────────────────────────────────
-- Kleene star
-- ─────────────────────────────────────────────────────────────────────────────
-- Star = join of all finite powers.  For n × n matrices over a finite carrier
-- with no positive cycles, the star is achieved at power n-1 (Floyd-Warshall).
-- See: tropical-resource-typing/Tropical_Kleene.thy (trop_mat_star_eq_sum_pow,
--      floyd_warshall_c).

||| Kleene star of a matrix: A* = I ⊕ A ⊕ A² ⊕ … ⊕ A^{n-1}.
||| In the min-plus case this computes all-pairs shortest paths (Bellman-Ford
||| interpretation); in max-plus it gives all-pairs longest simple paths.
public export
matStar : (sr : ClosedSemiring a) -> {n : Nat} -> Matrix n a -> Matrix n a
matStar sr {n = Z}   _ = matId sr  -- trivially identity for 0×0
matStar sr {n = S m} a =
  foldr (\k, acc => matAdd sr acc (matPow sr a k))
        (matId sr)
        (allFins (S m))

-- ─────────────────────────────────────────────────────────────────────────────
-- No-positive-cycle predicate
-- ─────────────────────────────────────────────────────────────────────────────
-- In tropical-resource-typing this is `no_pos_cycle n A`: all closed walks
-- have weight ≤ 1 (the multiplicative identity).  Here we state it as a
-- predicate on a matrix and a semiring.

||| `NoPosOycle sr n A`: every cycle in A has cost ≤ the multiplicative identity
||| under `sr.add` ordering.  Equivalent to: for all i < n, A*(i,i) ≤ sr.one.
public export
NoPosOycle : (sr : ClosedSemiring a) -> {n : Nat} -> Matrix n a -> Type
NoPosOycle sr {n} a = (i : Fin n) -> sr.add (matStar sr a i i) sr.one = sr.one

-- ─────────────────────────────────────────────────────────────────────────────
-- Key theorems — postulated pending full Idris2 proof
-- ─────────────────────────────────────────────────────────────────────────────
-- Each postulate has a corresponding complete proof in Isabelle.
-- See: hyperpolymath/tropical-resource-typing commit f6c5a6f.

||| Star equation: A* = I ⊕ A · A* (under no positive cycles).
|||
||| Isabelle reference: trop_mat_star_equation (Tropical_Kleene.thy).
||| Status: POSTULATED — Idris2 proof pending.
export postulate
StarEquation :
  (sr : ClosedSemiring a) ->
  {n : Nat} ->
  (a : Matrix n a) ->
  NoPosOycle sr a ->
  (i, j : Fin n) ->
  matStar sr a i j = matAdd sr (matId sr) (matMul sr a (matStar sr a)) i j

||| Least prefixpoint: A* is the least X satisfying X ≥ I ⊕ A · X.
|||
||| Isabelle reference: trop_mat_star_least_prefixpoint (Tropical_Kleene.thy).
||| Status: POSTULATED — Idris2 proof pending.
export postulate
StarLeastFixpoint :
  (sr : ClosedSemiring a) ->
  {n : Nat} ->
  (a x : Matrix n a) ->
  ((i, j : Fin n) ->
     sr.add (matAdd sr (matId sr) (matMul sr a x) i j) (x i j) = x i j) ->
  (i, j : Fin n) ->
  sr.add (matStar sr a i j) (x i j) = x i j

||| Star idempotency: (A*)* = A* (pointwise).
|||
||| Isabelle reference: trop_mat_star_idem (Tropical_CNO.thy).
||| Status: POSTULATED — Idris2 proof pending.
export postulate
StarIdem :
  (sr : ClosedSemiring a) ->
  {n : Nat} ->
  (a : Matrix n a) ->
  (i, j : Fin n) ->
  matStar sr (matStar sr a) i j = matStar sr a i j

-- ─────────────────────────────────────────────────────────────────────────────
-- Semiring laws (proved)
-- ─────────────────────────────────────────────────────────────────────────────

||| latAdd is commutative.
export
latAddComm : (a, b : LatCost) -> latAdd a b = latAdd b a
latAddComm LatInf    LatInf    = Refl
latAddComm LatInf    (Lat _)   = Refl
latAddComm (Lat _)   LatInf    = Refl
latAddComm (Lat a)   (Lat b)   = cong Lat (minCommutative a b)

||| LatInf is the identity for latAdd.
export
latAddIdentity : (a : LatCost) -> latAdd a LatInf = a
latAddIdentity LatInf  = Refl
latAddIdentity (Lat _) = Refl

||| Lat 0 is the identity for latMul.
export
latMulIdentity : (a : LatCost) -> latMul (Lat 0) a = a
latMulIdentity LatInf  = Refl
latMulIdentity (Lat _) = Refl

||| thrAdd is commutative.
export
thrAddComm : (a, b : ThrCost) -> thrAdd a b = thrAdd b a
thrAddComm ThrNeg    ThrNeg    = Refl
thrAddComm ThrNeg    (Thr _)   = Refl
thrAddComm (Thr _)   ThrNeg    = Refl
thrAddComm (Thr a)   (Thr b)   = cong Thr (sym (maxCommutative a b))

||| ThrNeg is the identity for thrAdd.
export
thrAddIdentity : (a : ThrCost) -> thrAdd a ThrNeg = a
thrAddIdentity ThrNeg  = Refl
thrAddIdentity (Thr _) = Refl

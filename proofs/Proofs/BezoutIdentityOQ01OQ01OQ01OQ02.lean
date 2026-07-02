/-
# HGCD Matrix Invariant: 2×2 Integer Matrices Encode Partial Euclidean Steps

## Open Question (bezout-identity-oq-01-oq-01-oq-01-oq-02)

Does the O(log² n) bit-complexity analysis of the parent
`bezout-identity-oq-01-oq-01-oq-01` (Stein's binary GCD) extend to the HGCD
(half-GCD) algorithm of Schönhage, giving `O(M(n) log n)` complexity where `M(n)`
is the integer-multiplication cost? The Seeker statement names three sub-tasks:

  (a) HGCD's key invariant that 2×2 integer matrices encode partial Euclidean steps;
  (b) the Master theorem in Lean (currently absent from Mathlib);
  (c) parametrization over the multiplication primitive `M`.

## What This File Proves: Part (a), in full

Part (a) is genuine, constructive linear algebra and is **independent** of the
Master theorem and of any cost model. We formalize it completely here.

A single Euclidean step
  `(r_{i-1}, r_i) ↦ (r_i, r_{i-1} − q_i · r_i)`
is left-multiplication of the column `(r_{i-1}, r_i)ᵀ` by the **quotient matrix**
  `Q(q) = !![0, 1; 1, −q]`  over ℤ.

We prove the three facts that make matrices encode Euclidean steps:

1. `Q_mulVec`     — one step:  `(Q q).mulVec ![x, y] = ![y, x − q·y]`.
2. `det_Q`        — each quotient matrix is unimodular: `det (Q q) = −1`.
3. `det_Rprod`    — the product `R_k = Q(q_k) ⋯ Q(q_1)` satisfies `det R_k = (−1)^k`,
                    so `R_k` is unimodular. This `det = ±1` is exactly what lets HGCD
                    splice a partial transformation matrix into a recursive call.
4. `Rprod_mulVec` — the full invariant: applying the product to a vector folds the
                    individual Euclidean steps.

The entries of `R_k` are (up to sign) the Bézout cofactors `s_k, t_k`, i.e. the
continuants `K(q_1,…,q_k)` computed by the extended Euclidean algorithm. Mathlib
proves the field-level analogue for `GenContFract` convergents
(`Mathlib/Algebra/ContinuedFractions/Determinant.lean`); here we work directly over
`Matrix (Fin 2) (Fin 2) ℤ`, which is the cleaner route for integer Euclidean steps.

## Out of scope (parts (b), (c)): the cost-model-gated asymptotic

The closing `O(M(n) log n)` bound rests on the Master theorem for the recurrence
`T(n) = 2 T(n/2) + M(n)` — the **critical case** `T(n) = 2T(n/2) + Θ(n)`, which is
absent from Mathlib (no Master/Akra–Bazzi theorem, no Big-O cost monad for `M`).
This mirrors the parent entry's decision to bound/axiomatize its closing asymptotic
(Part 2) rather than overclaim. The matrix invariant below is what the OQ's part (a)
actually asks for and is provable today.

## References
- Schönhage (1971), Schnelle Berechnung von Kettenbruchentwicklungen
- Knuth, TAOCP Vol. 2, §4.5.3 (analysis of Euclid's algorithm, continuants)
- Mathlib: `Mathlib/Algebra/ContinuedFractions/Determinant.lean` (field analogue)
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace BezoutIdentityOQ01OQ01OQ01OQ02

open Matrix

-- ============================================================
-- PART I: THE QUOTIENT MATRIX
-- ============================================================

/-- The Euclidean **quotient matrix** for a quotient `q`:
    `Q(q) = !![0, 1; 1, -q]`. Left-multiplying the column `(x, y)ᵀ` performs one
    Euclidean step `(x, y) ↦ (y, x - q·y)`. -/
def Q (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -q]

/-- One Euclidean step as a map on the remainder pair. -/
def euclidStep (q : ℤ) (v : Fin 2 → ℤ) : Fin 2 → ℤ := ![v 1, v 0 - q * v 1]

/-- **One step**: applying the quotient matrix to a pair performs one Euclidean step.
    `(Q q).mulVec ![x, y] = ![y, x - q·y]`. -/
theorem Q_mulVec (q : ℤ) (v : Fin 2 → ℤ) :
    (Q q).mulVec v = euclidStep q v := by
  funext i
  fin_cases i <;>
    simp [Q, euclidStep, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- **Unimodularity of a single quotient matrix**: `det (Q q) = -1`.
    Each Euclidean step is encoded by a determinant `-1` matrix. -/
@[simp] theorem det_Q (q : ℤ) : (Q q).det = -1 := by
  rw [Q, Matrix.det_fin_two_of]; ring

-- ============================================================
-- PART II: THE REMAINDER-SEQUENCE PRODUCT R_k
-- ============================================================

/-- The product `R_k = Q(q_k) · Q(q_{k-1}) · ⋯ · Q(q_1)` of quotient matrices.
    Given the quotient list `[q_k, …, q_1]` (most recent step first), this is the
    accumulated transformation taking `(a, b)ᵀ = (r_0, r_1)ᵀ` to `(r_k, r_{k+1})ᵀ`. -/
def Rprod : List ℤ → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | q :: qs => Q q * Rprod qs

@[simp] theorem Rprod_nil : Rprod [] = 1 := rfl

@[simp] theorem Rprod_cons (q : ℤ) (qs : List ℤ) :
    Rprod (q :: qs) = Q q * Rprod qs := rfl

/-- **Unimodularity of the accumulated product**: `det R_k = (-1)^k` where
    `k` is the number of Euclidean steps. Hence every partial Euclidean
    transformation matrix is unimodular — the property HGCD relies on to splice a
    partial matrix into a recursive call. -/
theorem det_Rprod (qs : List ℤ) : (Rprod qs).det = (-1) ^ qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    rw [Rprod_cons, Matrix.det_mul, det_Q, ih, List.length_cons, pow_succ]
    ring

/-- **The full matrix–Euclidean invariant**: applying the accumulated product to a
    vector is exactly the right-to-left fold of the individual Euclidean steps.
    With `v = ![a, b] = (r_0, r_1)ᵀ`, this yields `(r_k, r_{k+1})ᵀ`. -/
theorem Rprod_mulVec (qs : List ℤ) (v : Fin 2 → ℤ) :
    (Rprod qs).mulVec v = qs.foldr euclidStep v := by
  induction qs with
  | nil => simp [Matrix.one_mulVec]
  | cons q qs ih =>
    rw [Rprod_cons, ← Matrix.mulVec_mulVec, Q_mulVec, ih]
    rfl

-- ============================================================
-- PART III: WORKED EXAMPLES
-- ============================================================

-- gcd(252, 198): quotients of the Euclidean remainder sequence are 1, 3, 1, 2, ...
-- A single step on (252, 198) with quotient 1: (252, 198) ↦ (198, 252 - 1·198) = (198, 54).
example : (Q 1).mulVec ![252, 198] = ![198, 54] := by
  rw [Q_mulVec]
  funext i; fin_cases i <;> simp [euclidStep]

-- det of a 3-step product is (-1)^3 = -1.
example : (Rprod [1, 3, 1]).det = -1 := by
  rw [det_Rprod]; decide

-- det of a 4-step product is (-1)^4 = 1 (unimodular, orientation preserved).
example : (Rprod [2, 1, 3, 1]).det = 1 := by
  rw [det_Rprod]; decide

end BezoutIdentityOQ01OQ01OQ01OQ02

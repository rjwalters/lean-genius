/-
# HGCD Quotient-Matrix Invariant (Schönhage half-GCD)

## Problem (bezout-identity-oq-01-oq-01-oq-01-oq-02)
Does the binary-GCD bit-complexity analysis extend to the HGCD (half-GCD)
algorithm of Schönhage, giving `O(M(n) log n)` complexity?

## Scope of this file: MS1 — the matrix invariant (part (a))

The full open question has three parts (per the Seeker statement):
  (a) HGCD's invariant that 2×2 integer matrices encode partial Euclidean steps,
  (b) the Master theorem in Lean (currently absent from Mathlib),
  (c) parametrization over the multiplication primitive `M`.

Part (a) is genuine, constructive linear algebra and is **independent of the
Master theorem and of any cost model**. It is the heart of why HGCD works: each
Euclidean step is left-multiplication by a unimodular `2×2` integer quotient
matrix, so a block of steps is encoded by a single unimodular matrix that can be
spliced into a recursive call. This file formalizes that invariant.

Parts (b)+(c) — the closing `Θ(M(n) log n)` asymptotic via the Master theorem
(critical case `T(n) = 2T(n/2) + Θ(n)`), parametric over `M` — are blocked on
Mathlib lacking a Master/Akra–Bazzi theorem, mirroring the parent entry's choice
to bound/axiomatize the closing asymptotic. They are out of scope here.

## The invariant

A single Euclidean step `(rₖ₋₁, rₖ) ↦ (rₖ, rₖ₋₁ − qₖ·rₖ)` is left
multiplication of the column `(rₖ₋₁, rₖ)ᵀ` by the **quotient matrix**
`Q(q) = !![0, 1; 1, -q]` over `ℤ`. Hence the remainder-sequence product
`R(q_k, …, q_1) = Q(q_k)·…·Q(q_1)` satisfies:

  * **single-step:** `Q(q) *ᵥ ![x, y] = ![y, x − q·y]`
  * **determinant:** `det (Q q) = -1`, so `det (R qs) = (-1)^(qs.length)`.

The determinant relation is the integer continuant/convergent identity; it is
exactly what makes the product unimodular. (Mathlib proves the field-level
analogue in `Algebra/ContinuedFractions/Determinant.lean`; here we work directly
over `Matrix (Fin 2) (Fin 2) ℤ`, which is cleaner than bridging `GenContFract`.)

## References
- Schönhage (1971), Schnelle Berechnung von Kettenbruchentwicklungen
- Knuth, TAOCP Vol. 2, §4.5.3 (analysis of Euclid's algorithm; continuants)
- Mathlib `Algebra/ContinuedFractions/Determinant.lean` (field-level analogue)
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace BezoutIdentityOQ01OQ01OQ01OQ02

open Matrix

-- ============================================================
-- PART I: THE QUOTIENT MATRIX
-- ============================================================

/-- The Euclidean **quotient matrix** for quotient `q`: the `2×2` integer matrix
    `!![0, 1; 1, -q]` whose left action sends `(rₖ₋₁, rₖ)ᵀ ↦ (rₖ, rₖ₋₁ − q·rₖ)ᵀ`,
    i.e. performs one Euclidean step with quotient `q`. -/
def Q (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -q]

/-- **Single Euclidean step.** Left-multiplying the column `(x, y)` by `Q q`
    produces `(y, x − q·y)` — exactly one step of the remainder recurrence
    `rₖ₊₁ = rₖ₋₁ − qₖ·rₖ`. -/
theorem Q_mulVec (q x y : ℤ) : (Q q) *ᵥ ![x, y] = ![y, x - q * y] := by
  funext i
  fin_cases i <;>
    simp [Q, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring

/-- **Each quotient matrix is unimodular:** `det (Q q) = -1`. -/
theorem det_Q (q : ℤ) : (Q q).det = -1 := by
  simp [Q, Matrix.det_fin_two_of]

-- ============================================================
-- PART II: THE REMAINDER-SEQUENCE PRODUCT
-- ============================================================

/-- The product `R(q_k, …, q_1) = Q(q_k)·…·Q(q_1)` of quotient matrices, indexed
    by the (most-recent-first) list of quotients. `R []` is the identity. -/
def R : List ℤ → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | q :: qs => Q q * R qs

@[simp] theorem R_nil : R [] = 1 := rfl

@[simp] theorem R_cons (q : ℤ) (qs : List ℤ) : R (q :: qs) = Q q * R qs := rfl

/-- **The HGCD matrix invariant (part (a)).** The remainder-sequence product is
    unimodular with determinant `(-1)^k` where `k` is the number of Euclidean
    steps. This is the integer continuant/convergent determinant relation; it is
    what lets HGCD splice a partial transformation matrix into a recursive call. -/
theorem det_R (qs : List ℤ) : (R qs).det = (-1) ^ qs.length := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
      rw [R_cons, Matrix.det_mul, det_Q, ih, List.length_cons, pow_succ]
      ring

/-- **Unimodularity corollary:** the product matrix is invertible over `ℤ`
    (its determinant is a unit). -/
theorem isUnit_det_R (qs : List ℤ) : IsUnit (R qs).det := by
  rw [det_R]
  exact (isUnit_one.neg).pow qs.length

end BezoutIdentityOQ01OQ01OQ01OQ02

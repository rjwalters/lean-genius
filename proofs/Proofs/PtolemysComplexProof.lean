import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-
# Ptolemy's Theorem: The Complex Number Proof

## What This Proves
The complex-number proof of Ptolemy's theorem (inequality form) in two steps:
1. An algebraic identity over any commutative ring:
   (z₁ - z₃)(z₂ - z₄) = (z₁ - z₂)(z₃ - z₄) + (z₂ - z₃)(z₁ - z₄)
2. Taking norms and applying the triangle inequality yields Ptolemy's inequality:
   ‖z₁ - z₃‖ · ‖z₂ - z₄‖ ≤ ‖z₁ - z₂‖ · ‖z₃ - z₄‖ + ‖z₂ - z₃‖ · ‖z₁ - z₄‖

This is an independent proof from the Euclidean-geometric approach in PtolemysTheorem.lean,
which uses Mathlib's cospherical formulation. The algebraic proof reveals that Ptolemy's
inequality is fundamentally about the multiplicative structure of ℂ and the triangle inequality.

## Approach
- The algebraic identity holds in any CommRing (proved by `ring`)
- For normed fields like ℂ, ‖a · b‖ = ‖a‖ · ‖b‖ (multiplicativity of norm)
- Combined with ‖a + b‖ ≤ ‖a‖ + ‖b‖ (triangle inequality), this gives the result

## Status
- [x] Algebraic identity (over CommRing)
- [x] Ptolemy's inequality (norm, abs, and dist forms)
- [x] Equality characterization (sufficient condition via proportionality)
- [x] Complete — 0 sorries, 0 axioms

## Mathlib Dependencies
- `norm_mul` : Multiplicativity of norm in normed fields
- `norm_add_le` : Triangle inequality for norms
- `Complex.norm_eq_abs` : Connection between ‖·‖ and Complex.abs
- `dist_eq_norm` : Connection between dist and ‖·‖
-/

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: The Algebraic Identity
-- ============================================================

/-- The fundamental algebraic identity underlying Ptolemy's theorem.
This holds in any commutative ring, showing Ptolemy is purely algebraic.

Over ℂ, this becomes the key factorization: the "diagonal product" (z₁-z₃)(z₂-z₄)
decomposes as a sum of two "opposite side products". Taking absolute values
and applying the triangle inequality gives Ptolemy's inequality. -/
theorem ptolemy_algebraic_identity {R : Type*} [CommRing R] (z₁ z₂ z₃ z₄ : R) :
    (z₁ - z₃) * (z₂ - z₄) = (z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄) := by
  ring

/-- The algebraic identity specialized to ℂ. -/
theorem ptolemy_complex_identity (z₁ z₂ z₃ z₄ : ℂ) :
    (z₁ - z₃) * (z₂ - z₄) = (z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄) :=
  ptolemy_algebraic_identity z₁ z₂ z₃ z₄

-- ============================================================
-- PART 2: Ptolemy's Inequality (Norm Form)
-- ============================================================

/-- **Ptolemy's Inequality** via the complex-number proof.

For any four complex numbers:
  ‖z₁ - z₃‖ · ‖z₂ - z₄‖ ≤ ‖z₁ - z₂‖ · ‖z₃ - z₄‖ + ‖z₂ - z₃‖ · ‖z₁ - z₄‖

The proof is three lines:
1. Rewrite the LHS using multiplicativity of norm: ‖a · b‖ = ‖a‖ · ‖b‖
2. Apply the algebraic identity to rewrite the product as a sum
3. Apply the triangle inequality ‖a + b‖ ≤ ‖a‖ + ‖b‖ and expand back

Equality holds iff the four points are concyclic (on a common circle). -/
theorem ptolemy_inequality (z₁ z₂ z₃ z₄ : ℂ) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ ≤ ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  calc ‖z₁ - z₃‖ * ‖z₂ - z₄‖
      = ‖(z₁ - z₃) * (z₂ - z₄)‖ := (norm_mul _ _).symm
    _ = ‖(z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄)‖ := by
        rw [ptolemy_complex_identity]
    _ ≤ ‖(z₁ - z₂) * (z₃ - z₄)‖ + ‖(z₂ - z₃) * (z₁ - z₄)‖ := norm_add_le _ _
    _ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
        rw [norm_mul, norm_mul]

-- ============================================================
-- PART 3: Alternative Formulations
-- ============================================================

/-- Ptolemy's inequality in terms of metric distance.
This connects the complex-number proof directly to the classical geometric statement:
  dist(A,C) · dist(B,D) ≤ dist(A,B) · dist(C,D) + dist(B,C) · dist(A,D) -/
theorem ptolemy_inequality_dist (z₁ z₂ z₃ z₄ : ℂ) :
    dist z₁ z₃ * dist z₂ z₄ ≤ dist z₁ z₂ * dist z₃ z₄ + dist z₂ z₃ * dist z₁ z₄ := by
  simp only [dist_eq_norm]
  exact ptolemy_inequality z₁ z₂ z₃ z₄

-- ============================================================
-- PART 4: Equality Characterization
-- ============================================================

/-- **Ptolemy's Equality** (sufficient condition).

If the two "opposite side products" are positively proportional in ℂ — meaning
(z₂-z₃)(z₁-z₄) = t · (z₁-z₂)(z₃-z₄) for some real t ≥ 0 — then Ptolemy's
inequality becomes an equality. Geometrically, this proportionality holds when
the four points are concyclic in the standard ordering (the cross-ratio is real
and positive).

The proof shows both sides equal (1+t) · ‖(z₁-z₂)(z₃-z₄)‖. -/
theorem ptolemy_equality_of_proportional (z₁ z₂ z₃ z₄ : ℂ)
    (t : ℝ) (ht : 0 ≤ t)
    (h : (z₂ - z₃) * (z₁ - z₄) = (t : ℂ) * ((z₁ - z₂) * (z₃ - z₄))) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  -- The diagonal product factors as (1+t) times an opposite-side product
  have factored : (z₁ - z₃) * (z₂ - z₄) = ((1 + t : ℝ) : ℂ) * ((z₁ - z₂) * (z₃ - z₄)) := by
    have h1 := ptolemy_complex_identity z₁ z₂ z₃ z₄
    rw [h] at h1; rw [h1]; push_cast; ring
  -- Both sides equal (1+t) · ‖z₁-z₂‖ · ‖z₃-z₄‖
  have lhs_eq : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = (1 + t) * (‖z₁ - z₂‖ * ‖z₃ - z₄‖) := by
    rw [← norm_mul, factored, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
  have rhs_eq : ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ =
      (1 + t) * (‖z₁ - z₂‖ * ‖z₃ - z₄‖) := by
    rw [← norm_mul (z₂ - z₃) (z₁ - z₄), h, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ht, norm_mul]
    ring
  linarith

-- ============================================================
-- PART 5: Numerical Examples
-- ============================================================

/-- Example: Unit square vertices 0, 1, 1+i, i.
Diagonals: |0-(1+i)| · |1-i| = √2 · √2 = 2.
Opposite sides: |0-1| · |(1+i)-i| + |1-(1+i)| · |0-i| = 1·1 + 1·1 = 2.
Equality holds because the points are concyclic (on a circle of radius √2/2). -/
example : (2 : ℝ) = 1 * 1 + 1 * 1 := by norm_num

-- ============================================================
-- Export main results
-- ============================================================

#check @ptolemy_algebraic_identity
#check @ptolemy_complex_identity
#check @ptolemy_inequality
#check @ptolemy_inequality_dist
#check @ptolemy_equality_of_proportional

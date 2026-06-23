import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Tactic

/-!
# Ptolemy's Converse: Equality ↔ Same Ray

## What This Proves
The converse of the equality characterization from `PtolemysComplexProof.lean`, and the full
biconditional: Ptolemy's equality holds for four complex numbers if and only if the two
"opposite-side products" lie on the same ray in ℂ (viewed as an ℝ-module).

  ‖z₁-z₃‖·‖z₂-z₄‖ = ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖
    ↔  SameRay ℝ ((z₁-z₂)(z₃-z₄)) ((z₂-z₃)(z₁-z₄))

## Key Insight
The algebraic identity `(z₁-z₃)(z₂-z₄) = (z₁-z₂)(z₃-z₄) + (z₂-z₃)(z₁-z₄)` (from
`PtolemysComplexProof.lean`) reduces Ptolemy's equality to the equality case of the triangle
inequality: `‖a + b‖ = ‖a‖ + ‖b‖`. In a strictly convex normed space, this holds if and only
if `SameRay ℝ a b` (i.e., `a` and `b` are zero or positively proportional).

ℂ is strictly convex: it inherits this from `InnerProductSpace ℝ ℂ` (the real inner product
space structure), via `InnerProductSpace.toUniformConvexSpace` and
`UniformConvexSpace.toStrictConvexSpace`.

## Relationship to PtolemysComplexProof.lean
- `ptolemy_equality_of_proportional` (there): `∃ t ≥ 0, (z₂-z₃)(z₁-z₄) = ↑t·(z₁-z₂)(z₃-z₄)`
  → Ptolemy equality. (Sufficient condition, using `SameRay.norm_add`.)
- `ptolemy_equality_iff_sameRay` (here): Full biconditional via `sameRay_iff_norm_add`.
  Ptolemy equality → SameRay is the new (converse) direction.

## Status
Complete — 0 sorries, 0 axioms.

## Mathlib Dependencies
- `sameRay_iff_norm_add` : In a strictly convex space, `SameRay ℝ x y ↔ ‖x + y‖ = ‖x‖ + ‖y‖`
- `InnerProductSpace.toUniformConvexSpace`, `UniformConvexSpace.toStrictConvexSpace` :
  ℂ is strictly convex (as a real inner product space)
- `norm_mul` : Multiplicativity of norm in normed fields: `‖a * b‖ = ‖a‖ * ‖b‖`
-/

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: The Biconditional
-- ============================================================

/-- **Ptolemy Equality ↔ Same Ray** (Complete Characterization)

For any four complex numbers z₁, z₂, z₃, z₄, the following are equivalent:

1. **Ptolemy equality**: ‖z₁-z₃‖·‖z₂-z₄‖ = ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖
2. **Same ray**: The opposite-side products (z₁-z₂)(z₃-z₄) and (z₂-z₃)(z₁-z₄) lie on the
   same ray in ℂ (as ℝ-module): they are zero or positively real-proportional.

**Proof**: Let a = (z₁-z₂)(z₃-z₄) and b = (z₂-z₃)(z₁-z₄). The algebraic identity gives
`a + b = (z₁-z₃)(z₂-z₄)`, so by multiplicativity of norm:

  Ptolemy equality ↔ ‖a + b‖ = ‖a‖ + ‖b‖ (triangle equality)
                   ↔ SameRay ℝ a b  (by `sameRay_iff_norm_add`, using strict convexity of ℂ)

The new direction is Ptolemy equality → SameRay. The reverse is from `SameRay.norm_add`. -/
theorem ptolemy_equality_iff_sameRay (z₁ z₂ z₃ z₄ : ℂ) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ ↔
    SameRay ℝ ((z₁ - z₂) * (z₃ - z₄)) ((z₂ - z₃) * (z₁ - z₄)) := by
  constructor
  · intro h
    rw [sameRay_iff_norm_add]
    calc ‖(z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄)‖
        = ‖(z₁ - z₃) * (z₂ - z₄)‖ := by congr 1; ring
      _ = ‖z₁ - z₃‖ * ‖z₂ - z₄‖ := norm_mul _ _
      _ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := h
      _ = ‖(z₁ - z₂) * (z₃ - z₄)‖ + ‖(z₂ - z₃) * (z₁ - z₄)‖ := by
            rw [← norm_mul (z₁ - z₂), ← norm_mul (z₂ - z₃)]
  · intro h
    rw [sameRay_iff_norm_add] at h
    calc ‖z₁ - z₃‖ * ‖z₂ - z₄‖
        = ‖(z₁ - z₃) * (z₂ - z₄)‖ := (norm_mul _ _).symm
      _ = ‖(z₁ - z₂) * (z₃ - z₄) + (z₂ - z₃) * (z₁ - z₄)‖ := by congr 1; ring
      _ = ‖(z₁ - z₂) * (z₃ - z₄)‖ + ‖(z₂ - z₃) * (z₁ - z₄)‖ := h
      _ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
            rw [norm_mul (z₁ - z₂), norm_mul (z₂ - z₃)]

-- ============================================================
-- PART 2: Explicit Proportionality (when factors are nonzero)
-- ============================================================

/-- When the opposite-side products are nonzero, Ptolemy equality yields an explicit positive
real proportionality constant. If (z₁-z₂)(z₃-z₄) ≠ 0 and (z₂-z₃)(z₁-z₄) ≠ 0, then there
exists a positive real t such that t·(z₁-z₂)(z₃-z₄) = (z₂-z₃)(z₁-z₄).

This is the converse of `ptolemy_equality_of_proportional` from `PtolemysComplexProof.lean`. -/
theorem ptolemy_equality_implies_proportional (z₁ z₂ z₃ z₄ : ℂ)
    (h : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖)
    (ha : (z₁ - z₂) * (z₃ - z₄) ≠ 0)
    (hb : (z₂ - z₃) * (z₁ - z₄) ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ t • ((z₁ - z₂) * (z₃ - z₄)) = (z₂ - z₃) * (z₁ - z₄) :=
  ((ptolemy_equality_iff_sameRay z₁ z₂ z₃ z₄).mp h).exists_pos_left ha hb

-- ============================================================
-- PART 3: Converse as a Standalone Theorem
-- ============================================================

/-- **Ptolemy Equality implies Same Ray** (the new direction).

This is the converse of the sufficient condition in `PtolemysComplexProof.lean`.
The proof uses the equality case of the triangle inequality in the strictly convex space ℂ. -/
theorem ptolemy_equality_implies_sameRay (z₁ z₂ z₃ z₄ : ℂ)
    (h : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) :
    SameRay ℝ ((z₁ - z₂) * (z₃ - z₄)) ((z₂ - z₃) * (z₁ - z₄)) :=
  (ptolemy_equality_iff_sameRay z₁ z₂ z₃ z₄).mp h

-- ============================================================
-- PART 4: Numerical Verification (Unit Square)
-- ============================================================

/-- The unit square vertices {z₁=0, z₂=1, z₃=1+i, z₄=i} are concyclic.
The opposite-side products are:
  a = (z₁-z₂)(z₃-z₄) = (0-1)·((1+i)-i) = (-1)·1 = -1
  b = (z₂-z₃)(z₁-z₄) = (1-(1+i))·(0-i) = (-i)·(-i) = i² = -1
Both products equal -1, confirming SameRay ℝ (-1) (-1). -/
example : SameRay ℝ ((0 - 1 : ℂ) * ((1 + Complex.I) - Complex.I))
                    ((1 - (1 + Complex.I) : ℂ) * (0 - Complex.I)) := by
  -- Both products reduce to -1
  have h1 : (0 - 1 : ℂ) * ((1 + Complex.I) - Complex.I) = -1 := by ring
  have h2 : (1 - (1 + Complex.I) : ℂ) * (0 - Complex.I) = -1 := by
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    calc (1 - (1 + Complex.I) : ℂ) * (0 - Complex.I)
        = Complex.I ^ 2 := by ring
      _ = -1 := hI
  rw [h1, h2]

#check @ptolemy_equality_iff_sameRay
#check @ptolemy_equality_implies_sameRay
#check @ptolemy_equality_implies_proportional

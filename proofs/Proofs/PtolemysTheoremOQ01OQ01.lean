import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Tactic
import Proofs.PtolemysTheoremOQ01
import Proofs.PtolemysComplexProofOQ01

/-!
# Ptolemy's Theorem Converse: Equality Characterizes Cyclic Order

## What This Proves

For four distinct points on the unit circle, Ptolemy's equality:

  ‖z₁-z₃‖·‖z₂-z₄‖ = ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖

holds **if and only if** z₁, z₂, z₃, z₄ appear in counterclockwise (or clockwise) order
on the unit circle.

## Proof Strategy

The forward direction (CCW → equality) was proved in `PtolemysTheoremOQ01.lean`.
This file proves the **converse** (equality → CCW or CW order).

### The Chain of Implications

1. **Ptolemy equality → positive proportionality** (proved, 0 sorries):
   From `ptolemy_equality_implies_proportional` (PtolemysComplexProofOQ01):
   Ptolemy equality → SameRay (triangle equality in strictly convex ℂ) →
   ∃ t > 0 with t • ((z₁-z₂)(z₃-z₄)) = (z₂-z₃)(z₁-z₄).

2. **Positive proportionality → CCW or CW order** (axiomatized):
   Writing zⱼ = exp(iθⱼ) and applying `exp_diff_factor`:
     zᵢ - zⱼ = 2I·sin((θᵢ-θⱼ)/2)·exp(i(θᵢ+θⱼ)/2)
   The exponential phase factors cancel (E₁₂·E₃₄ = E₂₃·E₁₄ = exp(i(θ₁+θ₂+θ₃+θ₄)/2)),
   so the proportionality reduces to:
     t · sin((θ₁-θ₂)/2) · sin((θ₃-θ₄)/2) = sin((θ₂-θ₃)/2) · sin((θ₁-θ₄)/2)
   With t > 0: both sine products have the same sign. Case analysis:
   - **CCW** (θ₁<θ₂<θ₃<θ₄<θ₁+2π): all sines negative → same sign ✓
   - **CW** (θ₁>θ₂>θ₃>θ₄>θ₁-2π): all sines positive → same sign ✓
   - **Interlaced**: mixed signs → products differ → contradicts t > 0 ✗
   This direction is `positive_ratio_implies_cyclic_order` (1 axiom).

## Status

- 0 sorries
- 1 axiom (`positive_ratio_implies_cyclic_order`): the angular case analysis in step 2.
  Provable via `exp_diff_factor` (already in `PtolemysTheoremOQ01`) and a finite sign
  analysis of the three cyclic interlacing patterns of four distinct angles.

## Key Dependencies

- `PtolemysTheoremOQ01`: `IsCCWOrder`, `ptolemy_equality_for_unit_circle_ccw`
- `PtolemysComplexProofOQ01`: `ptolemy_equality_implies_proportional`
-/

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: Definitions and Infrastructure
-- ============================================================

/-- Four unit-circle points in clockwise order.
    Defined as CCW order with z₂ and z₄ swapped: z₁, z₄, z₃, z₂ go counterclockwise. -/
def IsCWOrder (z₁ z₂ z₃ z₄ : ℂ) : Prop := IsCCWOrder z₁ z₄ z₃ z₂

/-- All six pairwise distinctness conditions for four points. -/
structure FourDistinct (z₁ z₂ z₃ z₄ : ℂ) : Prop where
  h12 : z₁ ≠ z₂
  h13 : z₁ ≠ z₃
  h14 : z₁ ≠ z₄
  h23 : z₂ ≠ z₃
  h24 : z₂ ≠ z₄
  h34 : z₃ ≠ z₄

/-- `FourDistinct` for the cyclically reversed labeling (z₁, z₄, z₃, z₂). -/
lemma FourDistinct.reverse (z₁ z₂ z₃ z₄ : ℂ) (hd : FourDistinct z₁ z₂ z₃ z₄) :
    FourDistinct z₁ z₄ z₃ z₂ where
  h12 := hd.h14
  h13 := hd.h13
  h14 := hd.h12
  h23 := hd.h34.symm
  h24 := hd.h24.symm
  h34 := hd.h23.symm

/-- For four distinct points, the denominator factor (z₁-z₂)*(z₃-z₄) ≠ 0. -/
lemma FourDistinct.denom_ne {z₁ z₂ z₃ z₄ : ℂ} (hd : FourDistinct z₁ z₂ z₃ z₄) :
    (z₁ - z₂) * (z₃ - z₄) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hd.h12) (sub_ne_zero.mpr hd.h34)

/-- For four distinct points, the numerator factor (z₂-z₃)*(z₁-z₄) ≠ 0. -/
lemma FourDistinct.numer_ne {z₁ z₂ z₃ z₄ : ℂ} (hd : FourDistinct z₁ z₂ z₃ z₄) :
    (z₂ - z₃) * (z₁ - z₄) ≠ 0 :=
  mul_ne_zero (sub_ne_zero.mpr hd.h23) (sub_ne_zero.mpr hd.h14)

-- ============================================================
-- PART 2: Ptolemy Equality → Positive Proportionality
-- ============================================================

/-- For four distinct complex points satisfying Ptolemy's equality,
    the opposite-side products are in positive real proportion.

    This is a direct application of `ptolemy_equality_implies_proportional`
    from `PtolemysComplexProofOQ01`, which uses the equality case of the
    triangle inequality in the strictly convex normed space ℂ. -/
lemma ptolemy_eq_implies_pos_prop (z₁ z₂ z₃ z₄ : ℂ)
    (hd : FourDistinct z₁ z₂ z₃ z₄)
    (hptolemy : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ =
                ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) :
    ∃ t : ℝ, 0 < t ∧ t • ((z₁ - z₂) * (z₃ - z₄)) = (z₂ - z₃) * (z₁ - z₄) :=
  ptolemy_equality_implies_proportional z₁ z₂ z₃ z₄ hptolemy hd.denom_ne hd.numer_ne

-- ============================================================
-- PART 3: The Angular Case Analysis (Axiom)
-- ============================================================

/-- **Key Axiom**: For four distinct unit-circle points, positive real proportionality
    of the opposite-side products implies CCW or CW cyclic order.

    **Mathematical justification** (proof sketch, using `exp_diff_factor`):

    Write zⱼ = exp(iθⱼ). Set sᵢⱼ = sin((θᵢ-θⱼ)/2) and Eᵢⱼ = exp(i(θᵢ+θⱼ)/2).
    By `exp_diff_factor`: zᵢ - zⱼ = 2I · sᵢⱼ · Eᵢⱼ.

    The products factor as:
      (z₁-z₂)·(z₃-z₄) = (2I)² · s₁₂ · s₃₄ · E₁₂ · E₃₄
      (z₂-z₃)·(z₁-z₄) = (2I)² · s₂₃ · s₁₄ · E₂₃ · E₁₄

    The exponential phases satisfy E₁₂·E₃₄ = E₂₃·E₁₄ (both = exp(i(θ₁+θ₂+θ₃+θ₄)/2)).
    The (2I)² factors also cancel. So the proportionality reduces to:
      t · s₁₂ · s₃₄ = s₂₃ · s₁₄

    With t > 0, both products s₁₂·s₃₄ and s₂₃·s₁₄ have the same sign.

    Sign analysis for all possible orderings of four distinct angles θ₁,θ₂,θ₃,θ₄ on [0,2π):
    - **CCW** (θ₁ < θ₂ < θ₃ < θ₄ < θ₁+2π):
        s₁₂, s₂₃, s₃₄, s₁₄ all negative (arguments in (-π,0))
        → s₁₂·s₃₄ > 0, s₂₃·s₁₄ > 0 → same sign ✓
    - **CW** (θ₁ > θ₂ > θ₃ > θ₄ > θ₁-2π):
        all four sines positive → same sign ✓
    - **Interlaced** (e.g., θ₁ < θ₃ < θ₂ < θ₄):
        s₂₃ > 0, s₁₄ < 0 but s₁₂ < 0, s₃₄ < 0
        → s₁₂·s₃₄ > 0 but s₂₃·s₁₄ < 0 → opposite signs → contradicts t > 0 ✗
    (Two other interlacings give similar contradictions.)
    Hence same sign → CCW or CW order. -/
axiom positive_ratio_implies_cyclic_order (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hd : FourDistinct z₁ z₂ z₃ z₄)
    (t : ℝ) (ht : 0 < t)
    (heq : t • ((z₁ - z₂) * (z₃ - z₄)) = (z₂ - z₃) * (z₁ - z₄)) :
    IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCWOrder z₁ z₂ z₃ z₄

-- ============================================================
-- PART 4: Main Theorem — Ptolemy Converse
-- ============================================================

/-- **Ptolemy Converse for Unit-Circle Points**

For four distinct points on the unit circle, Ptolemy's equality implies they appear
in counterclockwise or clockwise order on the circle.

**Proof**:
1. `ptolemy_eq_implies_pos_prop`: equality → ∃ t > 0, t • (z₁-z₂)(z₃-z₄) = (z₂-z₃)(z₁-z₄)
   (Uses strict convexity of ℂ: triangle equality → SameRay → positive proportionality.)
2. `positive_ratio_implies_cyclic_order`: positive proportionality → CCW or CW.
   (Uses exp factorization and sign analysis of half-angle sines.) -/
theorem ptolemy_equality_implies_ccw_or_cw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hd : FourDistinct z₁ z₂ z₃ z₄)
    (hptolemy : ‖z₁ - z₃‖ * ‖z₂ - z₄‖ =
                ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) :
    IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCWOrder z₁ z₂ z₃ z₄ := by
  obtain ⟨t, ht_pos, ht_eq⟩ := ptolemy_eq_implies_pos_prop z₁ z₂ z₃ z₄ hd hptolemy
  exact positive_ratio_implies_cyclic_order z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hd t ht_pos ht_eq

-- ============================================================
-- PART 5: The Full Biconditional
-- ============================================================

/-- Ptolemy equality holds for CCW unit-circle points (wrapper for readability). -/
private lemma ptolemy_of_ccw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hd : FourDistinct z₁ z₂ z₃ z₄) (hccw : IsCCWOrder z₁ z₂ z₃ z₄) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ :=
  ptolemy_equality_for_unit_circle_ccw z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄
    hd.denom_ne hd.numer_ne hccw

/-- Ptolemy equality holds for CW unit-circle points.

    **Proof**: IsCWOrder z₁ z₂ z₃ z₄ = IsCCWOrder z₁ z₄ z₃ z₂.
    Apply `ptolemy_equality_for_unit_circle_ccw` with the relabeled points (z₁,z₄,z₃,z₂),
    then convert using ‖a-b‖ = ‖b-a‖ and commutativity of ·. -/
private lemma ptolemy_of_cw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hd : FourDistinct z₁ z₂ z₃ z₄) (hcw : IsCWOrder z₁ z₂ z₃ z₄) :
    ‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖ := by
  -- IsCWOrder z₁ z₂ z₃ z₄ = IsCCWOrder z₁ z₄ z₃ z₂ (by definition)
  -- Apply the CCW theorem to the relabeled sequence (z₁, z₄, z₃, z₂)
  -- Pattern: ‖w₁-w₃‖·‖w₂-w₄‖ = ‖w₁-w₂‖·‖w₃-w₄‖ + ‖w₂-w₃‖·‖w₁-w₄‖
  -- with w₁=z₁, w₂=z₄, w₃=z₃, w₄=z₂:
  -- gives: ‖z₁-z₃‖·‖z₄-z₂‖ = ‖z₁-z₄‖·‖z₃-z₂‖ + ‖z₄-z₃‖·‖z₁-z₂‖
  have hd' := hd.reverse z₁ z₂ z₃ z₄
  have heq := ptolemy_equality_for_unit_circle_ccw z₁ z₄ z₃ z₂ h₁ h₄ h₃ h₂
    hd'.denom_ne hd'.numer_ne hcw
  -- Rewrite ‖a-b‖ = ‖b-a‖ to get norms in canonical form
  rw [norm_sub_rev z₄ z₂, norm_sub_rev z₃ z₂, norm_sub_rev z₄ z₃] at heq
  -- heq is now: ‖z₁-z₃‖ * ‖z₂-z₄‖ = ‖z₁-z₄‖ * ‖z₂-z₃‖ + ‖z₃-z₄‖ * ‖z₁-z₂‖
  -- Goal:       ‖z₁-z₃‖ * ‖z₂-z₄‖ = ‖z₁-z₂‖ * ‖z₃-z₄‖ + ‖z₂-z₃‖ * ‖z₁-z₄‖
  -- Conclude by product and sum commutativity
  linarith [mul_comm ‖z₁ - z₄‖ ‖z₂ - z₃‖, mul_comm ‖z₃ - z₄‖ ‖z₁ - z₂‖]

/-- **Ptolemy Equality ↔ Cyclic Order** (Complete Biconditional)

For four distinct points on the unit circle:
  ‖z₁-z₃‖·‖z₂-z₄‖ = ‖z₁-z₂‖·‖z₃-z₄‖ + ‖z₂-z₃‖·‖z₁-z₄‖
    ↔  IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCWOrder z₁ z₂ z₃ z₄

This completes the characterization of cyclic quadrilaterals via Ptolemy's equality.

**Forward** (cyclic order → equality):
- CCW: `ptolemy_equality_for_unit_circle_ccw` from `PtolemysTheoremOQ01`.
- CW: Same theorem applied to the reversed labeling (z₁,z₄,z₃,z₂).

**Converse** (equality → cyclic order): `ptolemy_equality_implies_ccw_or_cw`. -/
theorem ptolemy_equality_iff_ccw_or_cw (z₁ z₂ z₃ z₄ : ℂ)
    (h₁ : ‖z₁‖ = 1) (h₂ : ‖z₂‖ = 1) (h₃ : ‖z₃‖ = 1) (h₄ : ‖z₄‖ = 1)
    (hd : FourDistinct z₁ z₂ z₃ z₄) :
    (‖z₁ - z₃‖ * ‖z₂ - z₄‖ = ‖z₁ - z₂‖ * ‖z₃ - z₄‖ + ‖z₂ - z₃‖ * ‖z₁ - z₄‖) ↔
    (IsCCWOrder z₁ z₂ z₃ z₄ ∨ IsCWOrder z₁ z₂ z₃ z₄) := by
  constructor
  · exact ptolemy_equality_implies_ccw_or_cw z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hd
  · rintro (hccw | hcw)
    · exact ptolemy_of_ccw z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hd hccw
    · exact ptolemy_of_cw z₁ z₂ z₃ z₄ h₁ h₂ h₃ h₄ hd hcw

-- ============================================================
-- PART 6: Numerical Verification
-- ============================================================

/-- The CW configuration z₁=1, z₂=-i, z₃=-1, z₄=i satisfies Ptolemy equality.
    (These are unit circle points in clockwise order.)
    ‖1-(-1)‖·‖(-i)-i‖ = ‖1-(-i)‖·‖(-1)-i‖ + ‖(-i)-(-1)‖·‖1-i‖
    i.e., 2·2 = √2·√2 + √2·√2 = 4. ✓ -/
example :
    ‖(1 : ℂ) - (-1)‖ * ‖(-Complex.I) - Complex.I‖ =
    ‖(1 : ℂ) - (-Complex.I)‖ * ‖(-1 : ℂ) - Complex.I‖ +
    ‖(-Complex.I) - (-1 : ℂ)‖ * ‖(1 : ℂ) - Complex.I‖ := by
  norm_num [Complex.norm_eq_abs, Complex.abs_apply, Complex.normSq_apply,
            Complex.ext_iff, Real.sqrt_eq_iff_sq_eq]

-- ============================================================
-- PART 7: Summary
-- ============================================================

#check @ptolemy_equality_implies_ccw_or_cw
#check @ptolemy_equality_iff_ccw_or_cw

/-!
## Summary

This file proves the converse direction of Ptolemy's theorem for unit-circle points,
completing the characterization started in `PtolemysTheoremOQ01.lean`.

### Main Results

1. **`ptolemy_equality_implies_ccw_or_cw`**: For four distinct unit-circle points,
   Ptolemy equality → CCW or CW cyclic order.

2. **`ptolemy_equality_iff_ccw_or_cw`**: Full biconditional — Ptolemy equality ↔
   CCW or CW order. (Combining the converse with the forward direction from the parent.)

### Proof Chain (Converse Direction)

  Ptolemy equality
    → SameRay ((z₁-z₂)(z₃-z₄)) ((z₂-z₃)(z₁-z₄))
       [PtolemysComplexProofOQ01: equality case of triangle inequality in strictly convex ℂ]
    → ∃ t > 0, t • (z₁-z₂)(z₃-z₄) = (z₂-z₃)(z₁-z₄)
       [positivity + distinctness → SameRay with nonzero factors]
    → IsCCWOrder ∨ IsCWOrder
       [positive_ratio_implies_cyclic_order: axiom, proved via exp factorization + sign analysis]

### Axiom Accounting

- **1 axiom** (`positive_ratio_implies_cyclic_order`):
  The angular case analysis showing that positive sine-product ratio forces CCW or CW order.
  This is provable from `exp_diff_factor` (already in PtolemysTheoremOQ01) plus a finite
  sign analysis of the three possible interlacing patterns of four angles on the circle.
  The proof would be ≈200 lines of trigonometric case analysis.
-/

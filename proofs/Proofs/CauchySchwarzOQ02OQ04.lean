import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-
# Cauchy-Schwarz OQ-02 → OQ-04: Operator-Norm Cauchy-Schwarz Inequality

## Overview

The classical Cauchy-Schwarz inequality bounds an inner product by the product of
norms: `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`.  When one of the vectors is the image of a *bounded
operator* `T`, the bound sharpens to involve the operator norm:

      ‖⟪T x, y⟫‖ ≤ ‖T‖ * ‖x‖ * ‖y‖.

This file develops the operator-norm form of Cauchy-Schwarz on inner product spaces
over `𝕜 = ℝ` or `ℂ` (`RCLike`), as a follow-up to the L²/Hölder material in
`CauchySchwarzOQ02`.  Everything is assembled from two Mathlib ingredients:

  * `norm_inner_le_norm` — the scalar Cauchy-Schwarz inequality `‖⟪u, v⟫‖ ≤ ‖u‖ * ‖v‖`,
  * `ContinuousLinearMap.le_opNorm` — the defining bound `‖T x‖ ≤ ‖T‖ * ‖x‖`.

It also includes the genuinely *operator-theoretic* Cauchy-Schwarz for a positive
symmetric operator (a Kadison–Schwarz-type inequality),

      ⟪T x, y⟫² ≤ ⟪T x, x⟫ * ⟪T y, y⟫        (T positive symmetric),

proved from the nonnegativity of the quadratic `t ↦ ⟪T(x + t•y), x + t•y⟫` via the
discriminant criterion `discrim_le_zero`.

## Main Results (13 theorems, 0 definitions, 0 sorries)

1. `operator_cauchy_schwarz`        — ‖⟪T x, y⟫‖ ≤ ‖T‖ * ‖x‖ * ‖y‖
2. `operator_cauchy_schwarz_right`  — same with the operator in the right slot
3. `operator_numerical_radius_bound`— ‖⟪T x, x⟫‖ ≤ ‖T‖ * ‖x‖²
4. `operator_cs_unit`               — unit vectors give ‖⟪T x, y⟫‖ ≤ ‖T‖
5. `operator_cs_comp`               — composition: ‖⟪(S∘T) x, y⟫‖ ≤ ‖S‖ * ‖T‖ * ‖x‖ * ‖y‖
6. `operator_cs_smul`               — scalar multiple: ‖⟪(c•T) x, y⟫‖ ≤ ‖c‖ * ‖T‖ * ‖x‖ * ‖y‖
7. `recovers_classical_cs`          — the identity operator recovers ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖
8. `operator_cs_adjoint`            — adjoint form ‖⟪(T†) y, x⟫‖ ≤ ‖T‖ * ‖y‖ * ‖x‖
9. `positive_operator_cauchy_schwarz` — ⟪T x, y⟫² ≤ ⟪T x, x⟫ * ⟪T y, y⟫
10. `positive_operator_cs_abs`      — |⟪T x, y⟫| ≤ √(⟪T x, x⟫) * √(⟪T y, y⟫)
11. `positive_operator_diagonal_nonneg` — sanity: ⟪T x, x⟫ ≥ 0 reused as a corollary
-/

noncomputable section

open RCLike ContinuousLinearMap

namespace CauchySchwarzOperatorNorm

section RCLikeBase

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F G : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **Operator-norm Cauchy-Schwarz.**  For a bounded operator `T : E →L[𝕜] F`,
the inner product `⟪T x, y⟫` is controlled by the operator norm. -/
theorem operator_cauchy_schwarz (T : E →L[𝕜] F) (x : E) (y : F) :
    ‖⟪T x, y⟫‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  calc ‖⟪T x, y⟫‖ ≤ ‖T x‖ * ‖y‖ := norm_inner_le_norm _ _
    _ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
        gcongr
        exact T.le_opNorm x

/-- Operator-norm Cauchy-Schwarz with the operator image in the *right* slot. -/
theorem operator_cauchy_schwarz_right (T : E →L[𝕜] F) (x : E) (y : F) :
    ‖⟪y, T x⟫‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  calc ‖⟪y, T x⟫‖ ≤ ‖y‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T‖ * ‖x‖) := by gcongr; exact T.le_opNorm x
    _ = ‖T‖ * ‖x‖ * ‖y‖ := by ring

/-- **Numerical radius bound.**  Taking `y = x` gives `‖⟪T x, x⟫‖ ≤ ‖T‖ * ‖x‖²`.
The supremum of the left side over unit `x` is the numerical radius `w(T) ≤ ‖T‖`. -/
theorem operator_numerical_radius_bound (T : E →L[𝕜] E) (x : E) :
    ‖⟪T x, x⟫‖ ≤ ‖T‖ * ‖x‖ ^ 2 := by
  have h := operator_cauchy_schwarz T x x
  nlinarith [h, norm_nonneg x, norm_nonneg (T : E →L[𝕜] E)]

/-- For unit vectors the bound collapses to `‖⟪T x, y⟫‖ ≤ ‖T‖`. -/
theorem operator_cs_unit (T : E →L[𝕜] F) {x : E} {y : F}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ‖⟪T x, y⟫‖ ≤ ‖T‖ := by
  have h := operator_cauchy_schwarz T x y
  rw [hx, hy] at h
  simpa using h

/-- **Composition.**  The operator-norm Cauchy-Schwarz bound is submultiplicative
under composition of operators. -/
theorem operator_cs_comp (S : F →L[𝕜] G) (T : E →L[𝕜] F) (x : E) (y : G) :
    ‖⟪(S ∘L T) x, y⟫‖ ≤ ‖S‖ * ‖T‖ * ‖x‖ * ‖y‖ := by
  have h := operator_cauchy_schwarz S (T x) y
  have hT : ‖T x‖ ≤ ‖T‖ * ‖x‖ := T.le_opNorm x
  simp only [ContinuousLinearMap.comp_apply]
  calc ‖⟪S (T x), y⟫‖ ≤ ‖S‖ * ‖T x‖ * ‖y‖ := h
    _ ≤ ‖S‖ * (‖T‖ * ‖x‖) * ‖y‖ := by gcongr
    _ = ‖S‖ * ‖T‖ * ‖x‖ * ‖y‖ := by ring

/-- **Scalar multiple.**  Scaling the operator scales the bound. -/
theorem operator_cs_smul (c : 𝕜) (T : E →L[𝕜] F) (x : E) (y : F) :
    ‖⟪(c • T) x, y⟫‖ ≤ ‖c‖ * ‖T‖ * ‖x‖ * ‖y‖ := by
  have h := operator_cauchy_schwarz (c • T) x y
  rwa [norm_smul] at h

/-- **Recovering classical Cauchy-Schwarz.**  Applying the operator bound to the
identity operator (`‖id‖ ≤ 1`) recovers `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`. -/
theorem recovers_classical_cs (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := by
  have h := operator_cauchy_schwarz (ContinuousLinearMap.id 𝕜 E) x y
  simp only [ContinuousLinearMap.id_apply] at h
  calc ‖⟪x, y⟫‖ ≤ ‖ContinuousLinearMap.id 𝕜 E‖ * ‖x‖ * ‖y‖ := h
    _ ≤ 1 * ‖x‖ * ‖y‖ := by gcongr; exact norm_id_le
    _ = ‖x‖ * ‖y‖ := by ring

end RCLikeBase

section Adjoint

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **Adjoint form.**  Using `⟪T† y, x⟫ = ⟪y, T x⟫`, the same operator norm `‖T‖`
controls the inner product against the adjoint. -/
theorem operator_cs_adjoint (T : E →L[𝕜] F) (y : F) (x : E) :
    ‖⟪(ContinuousLinearMap.adjoint T) y, x⟫‖ ≤ ‖T‖ * ‖y‖ * ‖x‖ := by
  rw [ContinuousLinearMap.adjoint_inner_left]
  calc ‖⟪y, T x⟫‖ ≤ ‖y‖ * ‖T x‖ := norm_inner_le_norm _ _
    _ ≤ ‖y‖ * (‖T‖ * ‖x‖) := by gcongr; exact T.le_opNorm x
    _ = ‖T‖ * ‖y‖ * ‖x‖ := by ring

end Adjoint

section PositiveOperator

open scoped RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/- A continuous linear operator `T` on a real inner product space is *positive
symmetric* when it is symmetric (`⟪T a, b⟫ = ⟪a, T b⟫`) and its diagonal form is
nonnegative (`0 ≤ ⟪T a, a⟫`).  These hypotheses are carried explicitly; no axioms. -/

/-- Restating the positivity hypothesis as a corollary for readability. -/
theorem positive_operator_diagonal_nonneg (T : F →L[ℝ] F)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (a : F) :
    0 ≤ ⟪T a, a⟫ := hpos a

/-- **Operator Cauchy-Schwarz for a positive symmetric operator** (Kadison–Schwarz
form).  The sesquilinear form `(x, y) ↦ ⟪T x, y⟫` of a positive symmetric operator
satisfies Cauchy-Schwarz:

      ⟪T x, y⟫² ≤ ⟪T x, x⟫ * ⟪T y, y⟫.

The proof optimizes the nonnegative quadratic `t ↦ ⟪T(x + t•y), x + t•y⟫ ≥ 0`,
whose discriminant must therefore be nonpositive. -/
theorem positive_operator_cauchy_schwarz (T : F →L[ℝ] F)
    (hsymm : ∀ a b : F, ⟪T a, b⟫ = ⟪a, T b⟫)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x y : F) :
    ⟪T x, y⟫ ^ 2 ≤ ⟪T x, x⟫ * ⟪T y, y⟫ := by
  -- symmetry of the form: ⟪T y, x⟫ = ⟪T x, y⟫
  have hsy : ⟪T y, x⟫ = ⟪T x, y⟫ := by
    rw [hsymm y x, real_inner_comm]
  -- the quadratic in `t` is nonnegative for every `t`
  have key : ∀ t : ℝ,
      0 ≤ ⟪T y, y⟫ * (t * t) + 2 * ⟪T x, y⟫ * t + ⟪T x, x⟫ := by
    intro t
    have h := hpos (x + t • y)
    rw [map_add, map_smul] at h
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at h
    rw [hsy] at h
    nlinarith [h]
  -- discriminant of `a t² + b t + c ≥ 0` is ≤ 0
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith [hd]

/-- **Absolute-value / square-root form** of the positive-operator Cauchy-Schwarz
inequality: `|⟪T x, y⟫| ≤ √⟪T x, x⟫ · √⟪T y, y⟫`. -/
theorem positive_operator_cs_abs (T : F →L[ℝ] F)
    (hsymm : ∀ a b : F, ⟪T a, b⟫ = ⟪a, T b⟫)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x y : F) :
    |⟪T x, y⟫| ≤ Real.sqrt ⟪T x, x⟫ * Real.sqrt ⟪T y, y⟫ := by
  have hcs := positive_operator_cauchy_schwarz T hsymm hpos x y
  rw [← Real.sqrt_mul_self (abs_nonneg (⟪T x, y⟫ : ℝ)), ← Real.sqrt_mul (hpos x)]
  apply Real.sqrt_le_sqrt
  rw [abs_mul_abs_self]
  nlinarith [hcs]

/-- **Absolute homogeneity of the induced seminorm.**  For *any* operator `T`, the
functional `p(x) = √⟪T x, x⟫` scales absolutely: `p(c • x) = |c| · p(x)`.  This is the
homogeneity axiom of a seminorm and needs neither symmetry nor positivity of `T`. -/
theorem positive_operator_seminorm_smul (T : F →L[ℝ] F) (c : ℝ) (x : F) :
    Real.sqrt ⟪T (c • x), c • x⟫ = |c| * Real.sqrt ⟪T x, x⟫ := by
  have h : ⟪T (c • x), c • x⟫ = c ^ 2 * ⟪T x, x⟫ := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- **Triangle inequality for the induced seminorm** (Minkowski form).  For a positive
symmetric operator `T`, the functional `p(x) = √⟪T x, x⟫` is subadditive:

      √⟪T (x + y), x + y⟫ ≤ √⟪T x, x⟫ + √⟪T y, y⟫.

Together with `positive_operator_seminorm_smul` (absolute homogeneity) and the
nonnegativity `hpos`, this shows the sesquilinear form of a positive symmetric operator
induces a genuine **seminorm** on `F`.  The proof expands the diagonal
`⟪T (x + y), x + y⟫ = ⟪T x, x⟫ + 2⟪T x, y⟫ + ⟪T y, y⟫` and bounds the cross term via the
Kadison–Schwarz inequality `positive_operator_cs_abs`. -/
theorem positive_operator_seminorm_triangle (T : F →L[ℝ] F)
    (hsymm : ∀ a b : F, ⟪T a, b⟫ = ⟪a, T b⟫)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x y : F) :
    Real.sqrt ⟪T (x + y), x + y⟫ ≤ Real.sqrt ⟪T x, x⟫ + Real.sqrt ⟪T y, y⟫ := by
  -- symmetry of the form
  have hsy : ⟪T y, x⟫ = ⟪T x, y⟫ := by rw [hsymm y x, real_inner_comm]
  -- expand the diagonal at `x + y`
  have hexp : ⟪T (x + y), x + y⟫ = ⟪T x, x⟫ + 2 * ⟪T x, y⟫ + ⟪T y, y⟫ := by
    rw [map_add]
    simp only [inner_add_left, inner_add_right]
    rw [hsy]; ring
  -- bound the cross term by the Kadison–Schwarz inequality
  have hcs := positive_operator_cs_abs T hsymm hpos x y
  have hle : ⟪T x, y⟫ ≤ Real.sqrt ⟪T x, x⟫ * Real.sqrt ⟪T y, y⟫ :=
    (le_abs_self _).trans hcs
  have e1 : Real.sqrt ⟪T x, x⟫ ^ 2 = ⟪T x, x⟫ := Real.sq_sqrt (hpos x)
  have e2 : Real.sqrt ⟪T y, y⟫ ^ 2 = ⟪T y, y⟫ := Real.sq_sqrt (hpos y)
  have hbound : ⟪T (x + y), x + y⟫ ≤
      (Real.sqrt ⟪T x, x⟫ + Real.sqrt ⟪T y, y⟫) ^ 2 := by
    rw [hexp]; nlinarith [hle, e1, e2]
  calc Real.sqrt ⟪T (x + y), x + y⟫
      ≤ Real.sqrt ((Real.sqrt ⟪T x, x⟫ + Real.sqrt ⟪T y, y⟫) ^ 2) :=
        Real.sqrt_le_sqrt hbound
    _ = Real.sqrt ⟪T x, x⟫ + Real.sqrt ⟪T y, y⟫ := Real.sqrt_sq (by positivity)

end PositiveOperator

end CauchySchwarzOperatorNorm

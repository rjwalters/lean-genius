import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

/-
# Cauchy-Schwarz OQ-02 → OQ-04 → OQ-02: The Energy Seminorm of a Positive Operator

## Overview

The parent file `CauchySchwarzOQ02OQ04` proves the positive-operator (Kadison–Schwarz)
Cauchy-Schwarz inequality for a positive symmetric operator `T` on a real inner product
space:

      ⟪T x, y⟫² ≤ ⟪T x, x⟫ * ⟪T y, y⟫        (T positive symmetric).

This is exactly the Cauchy-Schwarz inequality for the *positive semidefinite bilinear
form* `(x, y) ↦ ⟪T x, y⟫`.  A standard consequence of Cauchy-Schwarz for such a form is
that the induced **energy seminorm**

      ‖x‖_T := √⟪T x, x⟫

is a genuine seminorm: it is nonnegative, absolutely homogeneous (`‖c • x‖_T = |c| ‖x‖_T`),
and — the substantive content — satisfies the **triangle inequality**

      ‖x + y‖_T ≤ ‖x‖_T + ‖y‖_T.

The triangle inequality is the place where Cauchy-Schwarz does real work: expanding
`‖x + y‖_T² = ‖x‖_T² + 2⟪T x, y⟫ + ‖y‖_T²` and bounding the cross term `⟪T x, y⟫ ≤
|⟪T x, y⟫| ≤ ‖x‖_T ‖y‖_T` turns the square into a perfect square `(‖x‖_T + ‖y‖_T)²`.

This promotes the *inequality* of the parent into a *structure*: every positive symmetric
operator equips the space with a seminorm (a norm exactly when `T` is positive definite),
and the parallelogram law holds for it without any positivity hypothesis at all — it is a
purely bilinear identity.

## Main Results (9 theorems, 1 definition, 0 sorries)

1. `energyNorm`                  — def `‖x‖_T = √⟪T x, x⟫`
2. `energy_cauchy_schwarz`       — ⟪T x, y⟫² ≤ ⟪T x, x⟫ * ⟪T y, y⟫ (re-derived from discriminant)
3. `energyNorm_nonneg`           — 0 ≤ ‖x‖_T
4. `energyNorm_sq`               — ‖x‖_T² = ⟪T x, x⟫
5. `energyNorm_zero`             — ‖0‖_T = 0
6. `energyNorm_smul`             — ‖c • x‖_T = |c| * ‖x‖_T (absolute homogeneity)
7. `energyNorm_cauchy_schwarz`   — |⟪T x, y⟫| ≤ ‖x‖_T * ‖y‖_T (√ form)
8. `energyNorm_triangle`         — ‖x + y‖_T ≤ ‖x‖_T + ‖y‖_T (the seminorm triangle inequality)
9. `energyNorm_parallelogram`    — ‖x+y‖_T² + ‖x-y‖_T² = 2‖x‖_T² + 2‖y‖_T²

Positivity and symmetry of `T` are carried as explicit hypotheses (`hpos`, `hsymm`); there
are no axioms and no structure-encoded assumptions.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace CauchySchwarzPositiveSeminorm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (T : F →L[ℝ] F)

/-- The **energy seminorm** induced by an operator `T`: `‖x‖_T := √⟪T x, x⟫`.
For a positive symmetric operator this is a genuine seminorm (Theorems below). -/
def energyNorm (x : F) : ℝ := Real.sqrt ⟪T x, x⟫

/-- **Operator Cauchy-Schwarz for a positive symmetric operator.**  The bilinear form
`(x, y) ↦ ⟪T x, y⟫` is positive semidefinite, hence obeys Cauchy-Schwarz.  Re-derived
here (self-contained) from the nonnegativity of the quadratic `t ↦ ⟪T(x + t•y), x + t•y⟫`
via the discriminant criterion. -/
theorem energy_cauchy_schwarz
    (hsymm : ∀ a b : F, ⟪T a, b⟫ = ⟪a, T b⟫)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x y : F) :
    ⟪T x, y⟫ ^ 2 ≤ ⟪T x, x⟫ * ⟪T y, y⟫ := by
  have hsy : ⟪T y, x⟫ = ⟪T x, y⟫ := by rw [hsymm y x, real_inner_comm]
  have key : ∀ t : ℝ,
      0 ≤ ⟪T y, y⟫ * (t * t) + 2 * ⟪T x, y⟫ * t + ⟪T x, x⟫ := by
    intro t
    have h := hpos (x + t • y)
    rw [map_add, map_smul] at h
    simp only [inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at h
    rw [hsy] at h
    nlinarith [h]
  have hd := discrim_le_zero key
  simp only [discrim] at hd
  nlinarith [hd]

/-- The energy seminorm is nonnegative (no hypotheses needed: `√` is nonnegative). -/
theorem energyNorm_nonneg (x : F) : 0 ≤ energyNorm T x := Real.sqrt_nonneg _

/-- The square of the energy seminorm recovers the diagonal form `⟪T x, x⟫`
(using positivity so that `√` and squaring are inverse). -/
theorem energyNorm_sq (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x : F) :
    (energyNorm T x) ^ 2 = ⟪T x, x⟫ := by
  unfold energyNorm
  rw [Real.sq_sqrt (hpos x)]

/-- The energy seminorm of `0` is `0`. -/
theorem energyNorm_zero : energyNorm T 0 = 0 := by
  unfold energyNorm
  rw [map_zero, inner_zero_left, Real.sqrt_zero]

/-- **Absolute homogeneity.**  `‖c • x‖_T = |c| * ‖x‖_T`, because the form is bilinear:
`⟪T(c•x), c•x⟫ = c² ⟪T x, x⟫`. -/
theorem energyNorm_smul (c : ℝ) (x : F) :
    energyNorm T (c • x) = |c| * energyNorm T x := by
  unfold energyNorm
  rw [map_smul, real_inner_smul_left, real_inner_smul_right,
    show c * (c * ⟪T x, x⟫) = c ^ 2 * ⟪T x, x⟫ from by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

/-- **Square-root form of Cauchy-Schwarz** for the energy seminorm:
`|⟪T x, y⟫| ≤ ‖x‖_T * ‖y‖_T`. -/
theorem energyNorm_cauchy_schwarz
    (hsymm : ∀ a b : F, ⟪T a, b⟫ = ⟪a, T b⟫)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x y : F) :
    |⟪T x, y⟫| ≤ energyNorm T x * energyNorm T y := by
  have hcs := energy_cauchy_schwarz T hsymm hpos x y
  unfold energyNorm
  rw [← Real.sqrt_mul (hpos x), ← Real.sqrt_sq (abs_nonneg (⟪T x, y⟫ : ℝ))]
  apply Real.sqrt_le_sqrt
  rw [sq_abs]
  exact hcs

/-- **Triangle inequality for the energy seminorm.**  `‖x + y‖_T ≤ ‖x‖_T + ‖y‖_T`.
This is the substantive seminorm axiom: it is exactly where the Cauchy-Schwarz bound on
the cross term `⟪T x, y⟫` is used, turning `‖x + y‖_T²` into the perfect square
`(‖x‖_T + ‖y‖_T)²`. -/
theorem energyNorm_triangle
    (hsymm : ∀ a b : F, ⟪T a, b⟫ = ⟪a, T b⟫)
    (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x y : F) :
    energyNorm T (x + y) ≤ energyNorm T x + energyNorm T y := by
  have hsy : ⟪T y, x⟫ = ⟪T x, y⟫ := by rw [hsymm y x, real_inner_comm]
  have hexp : ⟪T (x + y), x + y⟫ = ⟪T x, x⟫ + 2 * ⟪T x, y⟫ + ⟪T y, y⟫ := by
    rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsy]
    ring
  have hcs := energyNorm_cauchy_schwarz T hsymm hpos x y
  have hxsq := energyNorm_sq T hpos x
  have hysq := energyNorm_sq T hpos y
  have habs : ⟪T x, y⟫ ≤ |⟪T x, y⟫| := le_abs_self _
  have hsum_nonneg : 0 ≤ energyNorm T x + energyNorm T y :=
    add_nonneg (energyNorm_nonneg T x) (energyNorm_nonneg T y)
  show Real.sqrt ⟪T (x + y), x + y⟫ ≤ energyNorm T x + energyNorm T y
  rw [← Real.sqrt_sq hsum_nonneg]
  apply Real.sqrt_le_sqrt
  rw [hexp]
  nlinarith [hcs, hxsq, hysq, habs, energyNorm_nonneg T x, energyNorm_nonneg T y]

/-- **Parallelogram law** for the energy seminorm:
`‖x + y‖_T² + ‖x − y‖_T² = 2‖x‖_T² + 2‖y‖_T²`.  Unlike the triangle inequality this is a
pure bilinear identity — the cross terms cancel — and needs only positivity (to identify
`‖·‖_T²` with the diagonal form), not symmetry. -/
theorem energyNorm_parallelogram (hpos : ∀ a : F, 0 ≤ ⟪T a, a⟫) (x y : F) :
    (energyNorm T (x + y)) ^ 2 + (energyNorm T (x - y)) ^ 2
      = 2 * (energyNorm T x) ^ 2 + 2 * (energyNorm T y) ^ 2 := by
  rw [energyNorm_sq T hpos, energyNorm_sq T hpos, energyNorm_sq T hpos,
    energyNorm_sq T hpos]
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right]
  ring

end CauchySchwarzPositiveSeminorm

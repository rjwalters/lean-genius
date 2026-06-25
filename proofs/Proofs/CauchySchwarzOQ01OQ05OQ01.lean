/-
The Cauchy-Schwarz defect as the squared norm of the orthogonal residual,
connecting the algebraic Lagrange identity to Mathlib's `starProjection`
(orthogonal projection) onto a single vector.

Open Question (cauchy-schwarz-oq-01-oq-05-oq-01):
"Can the Lagrange identity for the Cauchy-Schwarz defect be packaged as the
squared norm of an *explicit orthogonal residual*, to connect with Mathlib's
`orthogonalProjection`/`starProjection`?"

Answer: YES. Let `P x y := (𝕜 ∙ x).starProjection y` be the orthogonal
projection of `y` onto the line `𝕜 ∙ x`, and let the residual be

    r := y − P x y                    (the component of y perpendicular to x).

The parent problem (cauchy-schwarz-oq-01-oq-05) proves the *division-free*
Gram identity for the scaled Gram vector `w := ⟪x,x⟫ • y − ⟪x,y⟫ • x`:

    ‖w‖² = ‖x‖² · ( ‖x‖²·‖y‖² − ‖⟪x,y⟫‖² ).                       (★)

Here we show that this scaled Gram vector is exactly `⟪x,x⟫` times the
residual,

    w = ⟪x,x⟫ • r,                                                 (bridge)

because Mathlib's `starProjection_singleton` gives `P x y = (⟪x,y⟫/‖x‖²) • x`,
so `⟪x,x⟫ • P x y = ⟪x,y⟫ • x`. Substituting (bridge) into (★) and cancelling
`‖x‖²` (for `x ≠ 0`) yields the clean residual form of the Cauchy-Schwarz
defect:

    ‖x‖²·‖y‖² − ‖⟪x,y⟫‖² = ‖x‖² · ‖r‖²       (defect = ‖x‖²·‖residual‖²).

From this the inequality is immediate (`‖r‖² ≥ 0`), and equality holds iff the
residual vanishes, i.e. iff `y` already lies on the line `𝕜 ∙ x`
(`P x y = y`).

This file formalizes:
1. The residual `r = y − P x y` is orthogonal to `x`            (Mathlib API)
2. The bridge identity `⟪x,x⟫ • y − ⟪x,y⟫ • x = ⟪x,x⟫ • r`
3. The defect-as-residual identity `defect = ‖x‖²·‖r‖²`          (x ≠ 0)
4. Cauchy-Schwarz recovered from nonnegativity of `‖r‖²`
5. Equality characterization `‖⟪x,y⟫‖ = ‖x‖·‖y‖ ↔ P x y = y`
6. Specializations to ℝ and ℂ

References:
- Mathlib: starProjection_singleton, sub_starProjection_mem_orthogonal,
  mem_orthogonal_singleton_iff_inner_right, inner_self_eq_norm_sq_to_K
- Parent entry CauchySchwarzOQ01OQ05 (the division-free Lagrange identity ★)
-/

import Proofs.CauchySchwarzOQ01OQ05
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped InnerProductSpace
open RCLike

namespace CauchySchwarzOQ01OQ05OQ01

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The orthogonal projection of `y` onto the line `𝕜 ∙ x`. -/
noncomputable def proj (x y : E) : E := (𝕜 ∙ x).starProjection y

/-- The orthogonal residual: the component of `y` perpendicular to `x`. -/
noncomputable def residual (x y : E) : E := y - proj (𝕜 := 𝕜) x y

-- ============================================================
-- PART I: The residual is orthogonal to x
-- ============================================================

/-- **Residual ⟂ x.** The residual `r = y − P x y` is orthogonal to `x`:
`⟪x, r⟫ = 0`. This is the defining property of the orthogonal projection,
specialised to the line `𝕜 ∙ x`. -/
theorem inner_residual_right (x y : E) :
    ⟪x, residual (𝕜 := 𝕜) x y⟫_𝕜 = 0 := by
  have hr : residual (𝕜 := 𝕜) x y ∈ (𝕜 ∙ x)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (K := 𝕜 ∙ x) y
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).mp hr

/-- The explicit Mathlib formula for the projection onto a single vector. -/
theorem proj_eq (x y : E) :
    proj (𝕜 := 𝕜) x y = (⟪x, y⟫_𝕜 / ((‖x‖ ^ 2 : ℝ) : 𝕜)) • x :=
  Submodule.starProjection_singleton 𝕜 y

-- ============================================================
-- PART II: The bridge — scaled Gram vector = ⟪x,x⟫ • residual
-- ============================================================

/-- **Bridge identity.** The scaled Gram vector of the parent problem is
exactly `⟪x,x⟫` times the orthogonal residual:
`⟪x,x⟫ • y − ⟪x,y⟫ • x = ⟪x,x⟫ • (y − P x y)`.

This is what links the parent's *division-free* algebraic Lagrange identity to
Mathlib's orthogonal-projection machinery: the only content is that
`⟪x,x⟫ • P x y = ⟪x,y⟫ • x`, which holds because `P x y = (⟪x,y⟫/‖x‖²) • x`
and `⟪x,x⟫ = (‖x‖² : 𝕜)`. Valid for all `x` (at `x = 0` both sides vanish). -/
theorem gram_vector_eq_smul_residual (x y : E) :
    ⟪x, x⟫_𝕜 • y - ⟪x, y⟫_𝕜 • x = ⟪x, x⟫_𝕜 • residual (𝕜 := 𝕜) x y := by
  rw [residual, smul_sub, proj_eq, smul_smul, inner_self_eq_norm_sq_to_K]
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hxK : ((‖x‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
      rw [Ne, RCLike.ofReal_eq_zero]; exact pow_ne_zero 2 hxn
    rw [show ((‖x‖ : 𝕜) ^ 2) = ((‖x‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring,
        mul_div_cancel₀ _ hxK]

-- ============================================================
-- PART III: The defect as the squared norm of the residual
-- ============================================================

/-- **Defect = ‖x‖² · ‖residual‖².** The Cauchy-Schwarz defect equals `‖x‖²`
times the squared norm of the orthogonal residual:
`‖x‖²·‖y‖² − ‖⟪x,y⟫‖² = ‖x‖² · ‖y − P x y‖²`.

Proof: substitute the bridge identity into the parent's Lagrange identity (★),
`‖w‖² = ‖x‖²·defect`, where `w = ⟪x,x⟫ • r`. Then
`‖w‖² = ‖⟪x,x⟫‖²·‖r‖² = ‖x‖⁴·‖r‖²`, so `‖x‖²·defect = ‖x‖⁴·‖r‖²`; cancelling the
positive factor `‖x‖²` (using `x ≠ 0`) gives the result. -/
theorem defect_eq_norm_sq_residual (x y : E) (hx : x ≠ 0) :
    ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_𝕜‖ ^ 2
      = ‖x‖ ^ 2 * ‖residual (𝕜 := 𝕜) x y‖ ^ 2 := by
  have hlag := CauchySchwarzOQ01OQ05.gram_norm_sq (𝕜 := 𝕜) x y
  rw [gram_vector_eq_smul_residual, norm_smul, mul_pow,
      inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg x)] at hlag
  -- hlag : (‖x‖^2)^2 * ‖r‖^2 = ‖x‖^2 * (‖x‖^2*‖y‖^2 - ‖⟪x,y⟫‖^2)
  have hxpos : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    positivity
  nlinarith [hlag, hxpos]

-- ============================================================
-- PART IV: Cauchy-Schwarz and equality, from the residual
-- ============================================================

/-- **Cauchy-Schwarz from the residual.** Since `‖r‖² ≥ 0`, the residual form
of the defect gives `‖⟪x,y⟫‖² ≤ ‖x‖²·‖y‖²` directly. -/
theorem cauchy_schwarz_sq (x y : E) :
    ‖⟪x, y⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  · have h := defect_eq_norm_sq_residual (𝕜 := 𝕜) x y hx
    nlinarith [h, sq_nonneg ‖residual (𝕜 := 𝕜) x y‖, norm_nonneg x]

/-- **Equality iff the residual vanishes.** For `x ≠ 0`, equality
`‖⟪x,y⟫‖ = ‖x‖·‖y‖` holds **iff** the orthogonal projection recovers `y`,
i.e. the residual is zero (`P x y = y`), i.e. `y ∈ 𝕜 ∙ x`. -/
theorem eq_iff_proj_eq (x y : E) (hx : x ≠ 0) :
    ‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ proj (𝕜 := 𝕜) x y = y := by
  have hxpos : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.mpr hx
    positivity
  have hdef := defect_eq_norm_sq_residual (𝕜 := 𝕜) x y hx
  constructor
  · intro h
    have hsq : ‖⟪x, y⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by rw [h, mul_pow]
    have hr0 : ‖residual (𝕜 := 𝕜) x y‖ ^ 2 = 0 := by nlinarith [hdef, hsq, hxpos]
    have : residual (𝕜 := 𝕜) x y = 0 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hr0
      exact norm_eq_zero.mp this
    rw [residual, sub_eq_zero] at this
    exact this.symm
  · intro h
    have hr0 : residual (𝕜 := 𝕜) x y = 0 := by rw [residual, h, sub_self]
    rw [hr0, norm_zero] at hdef
    have hsq : ‖⟪x, y⟫_𝕜‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by rw [mul_pow]; nlinarith [hdef]
    have hb : (0 : ℝ) ≤ ‖x‖ * ‖y‖ := by positivity
    nlinarith [hsq, norm_nonneg (⟪x, y⟫_𝕜), hb]

-- ============================================================
-- PART V: Specializations
-- ============================================================

/-- The defect-as-residual identity over a **real** inner product space. -/
theorem defect_eq_norm_sq_residual_real
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) (hx : x ≠ 0) :
    ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_ℝ‖ ^ 2
      = ‖x‖ ^ 2 * ‖residual (𝕜 := ℝ) x y‖ ^ 2 :=
  defect_eq_norm_sq_residual (𝕜 := ℝ) x y hx

/-- The defect-as-residual identity over a **complex** inner product space. -/
theorem defect_eq_norm_sq_residual_complex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) (hx : x ≠ 0) :
    ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_ℂ‖ ^ 2
      = ‖x‖ ^ 2 * ‖residual (𝕜 := ℂ) x y‖ ^ 2 :=
  defect_eq_norm_sq_residual (𝕜 := ℂ) x y hx

end CauchySchwarzOQ01OQ05OQ01

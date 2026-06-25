/-
Quantitative Cauchy-Schwarz via the Lagrange / Gram defect identity
for complex (RCLike) inner product spaces

Open Question (cauchy-schwarz-oq-01-oq-05):
"For complex (and general RCLike) inner product spaces, is there an exact,
division-free algebraic identity for the Cauchy-Schwarz *defect*
‖x‖²·‖y‖² − ‖⟪x,y⟫‖², from which both the inequality and its equality
characterization follow directly — without invoking Mathlib's
`inner_mul_le_norm_mul_norm` or an orthogonal-projection coefficient?"

Answer: YES. The key is the scaled Gram vector

    w := ⟪x,x⟫ • y − ⟪x,y⟫ • x          (no division: ⟪x,x⟫ is a scalar)

which is orthogonal to x and satisfies the abstract Lagrange identity

    ‖w‖² = ‖x‖² · ( ‖x‖²·‖y‖² − ‖⟪x,y⟫‖² ).                 (★)

Since the left side is ≥ 0 and ‖x‖² ≥ 0, the bracket is ≥ 0, giving
Cauchy-Schwarz; equality forces w = 0, i.e. ⟪x,x⟫ • y = ⟪x,y⟫ • x, which
for x ≠ 0 means y is a scalar multiple of x.

Distinct from the sibling entry cauchy-schwarz-oq-01-oq-01, which uses the
projection coefficient ⟪v,u⟫/⟪v,v⟫ and a Pythagoras argument: here the
identity (★) is purely algebraic, division-free, and valid for *all* x
(including x = 0). It is the inner-product-space analogue of the classical
Lagrange identity, here proved over an arbitrary RCLike field with the
sesquilinear bookkeeping (conjugate-linearity in the first slot) handled
explicitly.

This file formalizes:
1. The 𝕜-valued Gram identity ⟪w,w⟫ = ⟪x,x⟫·(⟪x,x⟫⟪y,y⟫ − ⟪x,y⟫⟪y,x⟫)
2. The real Lagrange defect identity (★)
3. Cauchy-Schwarz (squared and norm form), recovered from (★)
4. Nonnegativity of the defect
5. Equality characterization ‖⟪x,y⟫‖ = ‖x‖·‖y‖ ↔ ⟪x,x⟫ • y = ⟪x,y⟫ • x
6. Linear-dependence corollary for x ≠ 0
7. Specializations to ℝ and ℂ

References:
- Mathlib: inner_self_eq_norm_sq_to_K, inner_conj_symm, RCLike.mul_conj
- Lagrange (1773); Schwarz (1885); Bunyakovsky (1859); Gram (1883)
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false

open scoped InnerProductSpace
open RCLike

namespace CauchySchwarzOQ01OQ05

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- ============================================================
-- PART I: The 𝕜-valued Gram identity
-- ============================================================

/-- **Gram identity (𝕜-valued).** For the scaled Gram vector
`w = ⟪x,x⟫ • y − ⟪x,y⟫ • x`, the self inner product factors as
`⟪w,w⟫ = ⟪x,x⟫ · (⟪x,x⟫⟪y,y⟫ − ⟪x,y⟫⟪y,x⟫)`.

The middle cross term cancels because `w ⊥ x`; what remains is the
Gram determinant of `x, y` scaled by `⟪x,x⟫`. Proof: expand the
sesquilinear form and simplify the conjugates `conj⟪x,x⟫ = ⟪x,x⟫`,
`conj⟪x,y⟫ = ⟪y,x⟫`. -/
theorem inner_gram_self (x y : E) :
    ⟪⟪x, x⟫_𝕜 • y - ⟪x, y⟫_𝕜 • x, ⟪x, x⟫_𝕜 • y - ⟪x, y⟫_𝕜 • x⟫_𝕜
      = ⟪x, x⟫_𝕜 * (⟪x, x⟫_𝕜 * ⟪y, y⟫_𝕜 - ⟪x, y⟫_𝕜 * ⟪y, x⟫_𝕜) := by
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    inner_conj_symm]
  ring

-- ============================================================
-- PART II: The real Lagrange defect identity (★)
-- ============================================================

/-- **Lagrange / Gram defect identity (★).** The squared norm of the scaled
Gram vector equals `‖x‖²` times the Cauchy-Schwarz defect:
`‖⟪x,x⟫ • y − ⟪x,y⟫ • x‖² = ‖x‖² · (‖x‖²·‖y‖² − ‖⟪x,y⟫‖²)`.

This is an exact, division-free identity valid for *all* `x, y` (including
`x = 0`, where both sides vanish). -/
theorem gram_norm_sq (x y : E) :
    ‖⟪x, x⟫_𝕜 • y - ⟪x, y⟫_𝕜 • x‖ ^ 2
      = ‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_𝕜‖ ^ 2) := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [RCLike.ofReal_pow,
      ← inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) (⟪x, x⟫_𝕜 • y - ⟪x, y⟫_𝕜 • x),
      inner_gram_self,
      ← inner_conj_symm y x, RCLike.mul_conj]
  simp only [inner_self_eq_norm_sq_to_K]
  push_cast
  ring

-- ============================================================
-- PART III: Cauchy-Schwarz, recovered from (★)
-- ============================================================

/-- The Cauchy-Schwarz defect is nonnegative:
`‖⟪x,y⟫‖² ≤ ‖x‖²·‖y‖²`. Proved directly from the Lagrange identity (★):
the left side of (★) is a square, hence `≥ 0`, and for `x ≠ 0` we may
cancel the positive factor `‖x‖²`; the case `x = 0` is immediate. -/
theorem cauchy_schwarz_sq (x y : E) :
    ‖⟪x, y⟫_𝕜‖ ^ 2 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  have hw : (0 : ℝ) ≤ ‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_𝕜‖ ^ 2) := by
    rw [← gram_norm_sq]; exact sq_nonneg _
  rcases eq_or_ne x 0 with hx | hx
  · subst hx; simp
  · have hxpos : 0 < ‖x‖ ^ 2 := by
      have : 0 < ‖x‖ := norm_pos_iff.mpr hx
      positivity
    nlinarith [hw, hxpos]

/-- **Cauchy-Schwarz inequality** for complex (RCLike) inner product spaces,
`‖⟪x,y⟫‖ ≤ ‖x‖·‖y‖`, obtained from the squared form by monotonicity of
`√`. This re-derives the headline result of the parent problem
(`cauchy-schwarz-oq-01`) *without* calling `inner_mul_le_norm_mul_norm`. -/
theorem cauchy_schwarz (x y : E) : ‖⟪x, y⟫_𝕜‖ ≤ ‖x‖ * ‖y‖ := by
  have h2 : ‖⟪x, y⟫_𝕜‖ ^ 2 ≤ (‖x‖ * ‖y‖) ^ 2 := by
    rw [mul_pow]; exact cauchy_schwarz_sq x y
  have hb : (0 : ℝ) ≤ ‖x‖ * ‖y‖ := by positivity
  calc ‖⟪x, y⟫_𝕜‖ = Real.sqrt (‖⟪x, y⟫_𝕜‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖x‖ * ‖y‖) ^ 2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ * ‖y‖ := Real.sqrt_sq hb

/-- The Gram determinant of `x, y` is nonnegative:
`‖x‖²·‖y‖² − ‖⟪x,y⟫‖² ≥ 0`. -/
theorem gram_det_nonneg (x y : E) :
    0 ≤ ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_𝕜‖ ^ 2 := by
  have := cauchy_schwarz_sq (𝕜 := 𝕜) x y
  linarith

-- ============================================================
-- PART IV: Equality characterization
-- ============================================================

/-- **Equality in Cauchy-Schwarz, characterized by the Gram vector.**
`‖⟪x,y⟫‖ = ‖x‖·‖y‖` holds **iff** the scaled Gram vector vanishes,
`⟪x,x⟫ • y = ⟪x,y⟫ • x`.

Forward: equality makes the defect `0`, so by (★) `‖w‖² = ‖x‖²·0 = 0`, hence
`w = 0` — with no case split. Backward: `w = 0` makes `‖x‖²·defect = 0`; for
`x ≠ 0` the defect is `0`, and for `x = 0` both sides are `0`. -/
theorem cauchy_schwarz_eq_iff (x y : E) :
    ‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ ⟪x, x⟫_𝕜 • y = ⟪x, y⟫_𝕜 • x := by
  rw [← sub_eq_zero (a := ⟪x, x⟫_𝕜 • y), ← norm_eq_zero (a := ⟪x, x⟫_𝕜 • y - ⟪x, y⟫_𝕜 • x),
      ← sq_eq_zero_iff (a := ‖⟪x, x⟫_𝕜 • y - ⟪x, y⟫_𝕜 • x‖), gram_norm_sq]
  constructor
  · intro h
    have hsq : ‖⟪x, y⟫_𝕜‖ ^ 2 = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
      rw [h, mul_pow]
    rw [hsq]; ring
  · intro h
    rcases eq_or_ne x 0 with hx | hx
    · subst hx; simp
    · have hxpos : 0 < ‖x‖ ^ 2 := by
        have : 0 < ‖x‖ := norm_pos_iff.mpr hx
        positivity
      have hdef : ‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_𝕜‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 (ne_of_gt hxpos)
        · exact h2
      have hsq : ‖⟪x, y⟫_𝕜‖ ^ 2 = (‖x‖ * ‖y‖) ^ 2 := by
        rw [mul_pow]; linarith
      have := norm_nonneg (⟪x, y⟫_𝕜)
      have hb : (0 : ℝ) ≤ ‖x‖ * ‖y‖ := by positivity
      nlinarith [hsq, this, hb]

/-- **Linear-dependence corollary.** For `x ≠ 0`, equality in Cauchy-Schwarz
holds **iff** `y` is a scalar multiple of `x`. -/
theorem eq_iff_smul_of_ne_zero (x y : E) (hx : x ≠ 0) :
    ‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ ∃ c : 𝕜, y = c • x := by
  have hxx : ⟪x, x⟫_𝕜 ≠ 0 := fun h => hx (inner_self_eq_zero.mp h)
  rw [cauchy_schwarz_eq_iff]
  constructor
  · intro hgram
    refine ⟨(⟪x, x⟫_𝕜)⁻¹ * ⟪x, y⟫_𝕜, ?_⟩
    rw [mul_smul, ← hgram, smul_smul, inv_mul_cancel₀ hxx, one_smul]
  · rintro ⟨c, rfl⟩
    rw [inner_smul_right, smul_smul, mul_comm c (⟪x, x⟫_𝕜)]

-- ============================================================
-- PART V: Specializations
-- ============================================================

/-- The Lagrange defect identity over a **real** inner product space. -/
theorem gram_norm_sq_real
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) :
    ‖(⟪x, x⟫_ℝ : ℝ) • y - (⟪x, y⟫_ℝ : ℝ) • x‖ ^ 2
      = ‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_ℝ‖ ^ 2) :=
  gram_norm_sq (𝕜 := ℝ) x y

/-- The Lagrange defect identity over a **complex** inner product space. -/
theorem gram_norm_sq_complex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) :
    ‖⟪x, x⟫_ℂ • y - ⟪x, y⟫_ℂ • x‖ ^ 2
      = ‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫_ℂ‖ ^ 2) :=
  gram_norm_sq (𝕜 := ℂ) x y

/-- Cauchy-Schwarz over a complex inner product space, via (★). -/
theorem cauchy_schwarz_complex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) :
    ‖⟪x, y⟫_ℂ‖ ≤ ‖x‖ * ‖y‖ :=
  cauchy_schwarz (𝕜 := ℂ) x y

end CauchySchwarzOQ01OQ05

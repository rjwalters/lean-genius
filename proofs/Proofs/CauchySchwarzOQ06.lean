/-
  Cauchy-Schwarz Equality: The Linear-Dependence Characterization
  Open Question: cauchy-schwarz-oq-06

  The Cauchy-Schwarz inequality `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` holds in every inner-product
  space over `𝕜 = ℝ` or `ℂ`. This file characterizes EXACTLY when equality occurs:

      ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖   ↔   the pair {x, y} is linearly dependent.

  Mathlib's `norm_inner_eq_norm_iff` already proves an equality case, but it requires
  BOTH vectors to be nonzero and phrases proportionality asymmetrically as
  `∃ r, y = r • x`. The contribution here is the fully UNCONDITIONAL and SYMMETRIC
  statement in terms of `¬ LinearIndependent 𝕜 ![x, y]` — the standard textbook
  formulation of "linearly dependent" — which automatically subsumes the degenerate
  cases `x = 0` and `y = 0`.

  We also record the sharp boundary form:

      ‖⟪x, y⟫‖ < ‖x‖ * ‖y‖   ↔   {x, y} is linearly INDEPENDENT,

  i.e. strict inequality is exactly the generic (independent) situation.

  References:
  - Cauchy (1821), Bunyakovsky (1859), Schwarz (1888): the inequality and its
    equality case.
  - Steele, "The Cauchy-Schwarz Master Class" (2004), Chapter 1.
  - Mathlib `Mathlib/Analysis/InnerProductSpace/Basic.lean`:
    `norm_inner_eq_norm_tfae`, `norm_inner_eq_norm_iff`, `norm_inner_le_norm`.
-/

import Mathlib

namespace CauchySchwarzOQ06

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

-- ============================================================================
-- Part I: Linear dependence of a pair, in explicit form
-- ============================================================================

/-- A pair of vectors fails to be linearly independent exactly when some nontrivial
linear combination vanishes. This is `LinearIndependent.pair_iff` negated, repackaged
into the convenient "exists a nonzero coefficient" shape. -/
theorem not_linearIndependent_pair_iff (x y : E) :
    ¬ LinearIndependent 𝕜 ![x, y] ↔
      ∃ s t : 𝕜, (s ≠ 0 ∨ t ≠ 0) ∧ s • x + t • y = 0 := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h
    rw [not_forall] at h
    obtain ⟨s, h⟩ := h
    rw [not_forall] at h
    obtain ⟨t, h⟩ := h
    rw [_root_.not_imp] at h
    obtain ⟨hst, hnot⟩ := h
    rw [not_and_or] at hnot
    exact ⟨s, t, hnot, hst⟩
  · rintro ⟨s, t, hne, hst⟩ hLI
    obtain ⟨hs, ht⟩ := hLI s t hst
    rcases hne with h | h
    · exact h hs
    · exact h ht

-- ============================================================================
-- Part II: The equality case of Cauchy-Schwarz
-- ============================================================================

/-- **Equality case of Cauchy-Schwarz (linear-dependence form).**

For any two vectors `x y` in an inner-product space over `𝕜 = ℝ` or `ℂ`,

    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖   ↔   ¬ LinearIndependent 𝕜 ![x, y].

Unlike Mathlib's `norm_inner_eq_norm_iff`, this needs no nonzero hypotheses and is
symmetric in `x` and `y`: the degenerate cases `x = 0` and `y = 0` are absorbed into
the linear-dependence condition. -/
theorem norm_inner_eq_norm_mul_iff_not_linearIndependent (x y : E) :
    ‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ ¬ LinearIndependent 𝕜 ![x, y] := by
  have key : ‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : 𝕜, y = r • x :=
    (norm_inner_eq_norm_tfae 𝕜 x y).out 0 2
  rw [key, not_linearIndependent_pair_iff]
  constructor
  · rintro (rfl | ⟨r, rfl⟩)
    · -- x = 0: the combination 1 • 0 + 0 • y = 0 witnesses dependence.
      exact ⟨1, 0, Or.inl one_ne_zero, by simp⟩
    · -- y = r • x: the combination r • x + (-1) • (r • x) = 0 witnesses dependence.
      exact ⟨r, -1, Or.inr (neg_ne_zero.mpr one_ne_zero), by rw [neg_one_smul, add_neg_cancel]⟩
  · rintro ⟨s, t, hne, hst⟩
    rcases eq_or_ne t 0 with rfl | ht
    · -- The `y` coefficient is zero, so `s ≠ 0` and `s • x = 0`, forcing `x = 0`.
      have hs : s ≠ 0 := hne.resolve_right (by simp)
      simp only [zero_smul, add_zero] at hst
      exact Or.inl ((smul_eq_zero.mp hst).resolve_left hs)
    · -- The `y` coefficient is nonzero, so `y` is the explicit multiple `(-(t⁻¹ s)) • x`.
      right
      have h1 : t • y = (-s) • x := by
        rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hst
      have h2 : (t⁻¹ * (-s)) • x = y := by
        rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      exact ⟨t⁻¹ * (-s), h2.symm⟩

/-- The equality case stated as an explicit vanishing combination (symmetric form). -/
theorem norm_inner_eq_norm_mul_iff_exists (x y : E) :
    ‖⟪x, y⟫_𝕜‖ = ‖x‖ * ‖y‖ ↔ ∃ s t : 𝕜, (s ≠ 0 ∨ t ≠ 0) ∧ s • x + t • y = 0 := by
  rw [norm_inner_eq_norm_mul_iff_not_linearIndependent, not_linearIndependent_pair_iff]

-- ============================================================================
-- Part III: The sharp boundary — strict inequality is linear independence
-- ============================================================================

/-- **Sharp form of Cauchy-Schwarz.**

Strict inequality `‖⟪x, y⟫‖ < ‖x‖ * ‖y‖` holds exactly when `x` and `y` are linearly
independent. Together with the equality case this gives a complete dichotomy governed
by linear (in)dependence. -/
theorem norm_inner_lt_norm_mul_iff_linearIndependent (x y : E) :
    ‖⟪x, y⟫_𝕜‖ < ‖x‖ * ‖y‖ ↔ LinearIndependent 𝕜 ![x, y] := by
  rw [lt_iff_le_and_ne, and_iff_right (norm_inner_le_norm x y), ne_eq,
    norm_inner_eq_norm_mul_iff_not_linearIndependent, not_not]

-- ============================================================================
-- Part IV: Real specialization (absolute value form)
-- ============================================================================

/-- The equality case over a real inner-product space, with the inner product's
absolute value in place of its norm. -/
theorem abs_real_inner_eq_norm_mul_iff_not_linearIndependent
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) :
    |⟪x, y⟫_ℝ| = ‖x‖ * ‖y‖ ↔ ¬ LinearIndependent ℝ ![x, y] := by
  rw [← Real.norm_eq_abs]
  exact norm_inner_eq_norm_mul_iff_not_linearIndependent x y

/-- The real sharp form: strict inequality `|⟪x, y⟫| < ‖x‖ * ‖y‖` is linear independence. -/
theorem abs_real_inner_lt_norm_mul_iff_linearIndependent
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] (x y : F) :
    |⟪x, y⟫_ℝ| < ‖x‖ * ‖y‖ ↔ LinearIndependent ℝ ![x, y] := by
  rw [← Real.norm_eq_abs]
  exact norm_inner_lt_norm_mul_iff_linearIndependent x y

-- ============================================================================
-- Part V: Sanity corollaries
-- ============================================================================

/-- Equality always holds when the left vector is zero (a degenerate case the
nonzero-hypothesis form cannot state). -/
theorem norm_inner_eq_norm_mul_left_zero (y : E) :
    ‖⟪(0 : E), y⟫_𝕜‖ = ‖(0 : E)‖ * ‖y‖ := by
  rw [norm_inner_eq_norm_mul_iff_not_linearIndependent]
  -- ![0, y] is dependent: `1 • 0 + 0 • y = 0`.
  rw [not_linearIndependent_pair_iff]
  exact ⟨1, 0, Or.inl one_ne_zero, by simp⟩

/-- Equality holds whenever `y` is a scalar multiple of `x`. -/
theorem norm_inner_eq_norm_mul_of_smul (x : E) (r : 𝕜) :
    ‖⟪x, r • x⟫_𝕜‖ = ‖x‖ * ‖r • x‖ := by
  rw [norm_inner_eq_norm_mul_iff_not_linearIndependent, not_linearIndependent_pair_iff]
  exact ⟨r, -1, Or.inr (neg_ne_zero.mpr one_ne_zero), by rw [neg_one_smul, add_neg_cancel]⟩

#check @norm_inner_eq_norm_mul_iff_not_linearIndependent
#check @norm_inner_lt_norm_mul_iff_linearIndependent
#check @abs_real_inner_eq_norm_mul_iff_not_linearIndependent

end CauchySchwarzOQ06

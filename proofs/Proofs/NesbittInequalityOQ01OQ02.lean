import Mathlib

/-
# A One-Parameter Weighted Nesbitt Inequality with a Parametrised SOS Certificate

The parent entry `NesbittInequalityOQ01` proves the classical Nesbitt inequality
`a/(b+c) + b/(c+a) + c/(a+b) ≥ 3/2` via an explicit sum-of-squares identity and
raises the open question:

> *Can the weighted Nesbitt inequality (with positive weights on the fractions)
>  be certified by a parametrised SOS family?*

This file answers it with the natural **one-parameter family** obtained by
weighting the two summands of each denominator:

`a/(t*b + c) + b/(t*c + a) + c/(t*a + b) ≥ 3/(t+1)`,

valid for all positive reals `a, b, c` and every weight `t > 0`, with equality
iff `a = b = c`. Specialising to `t = 1` recovers the classical statement.

## The parametrised SOS certificate

The engine is the three-term Cauchy–Schwarz (Engel / Titu) inequality, whose
*defect is itself a sum of squares*:

`(x₁²/y₁ + x₂²/y₂ + x₃²/y₃)·(y₁+y₂+y₃) − (x₁+x₂+x₃)²`
  `= y₃(x₁y₂ − x₂y₁)² + y₂(x₁y₃ − x₃y₁)² + y₁(x₂y₃ − x₃y₂)²`.

Writing `a/(t*b+c) = a²/(a(t*b+c))` puts the left-hand side into Titu form with
`yᵢ` the *weighted* denominators `a(t*b+c), b(t*c+a), c(t*a+b)`. These `yᵢ`
carry the parameter `t`, so the squares `(xᵢyⱼ − xⱼyᵢ)²` form a genuine
`t`-parametrised SOS family. The remaining ingredient is the (parameter-free)
estimate `(a+b+c)² ≥ 3(ab+bc+ca)`, equivalently
`½[(a−b)² + (b−c)² + (c−a)²] ≥ 0`, which fixes the sharp constant `3/(t+1)`
because the weighted denominators sum to `(t+1)(ab+bc+ca)`.

Mathlib has the abstract inner-product Cauchy–Schwarz but no ready three-term
Engel-form lemma with the explicit SOS remainder used here, so `titu3` is built
locally.
-/

namespace NesbittInequalityOQ01OQ02

/-- **Three-term Cauchy–Schwarz (Engel / Titu form).** For positive denominators,
`(x₁+x₂+x₃)²/(y₁+y₂+y₃) ≤ x₁²/y₁ + x₂²/y₂ + x₃²/y₃`. The proof clears
denominators and supplies the sum-of-squares remainder
`y₃(x₁y₂−x₂y₁)² + y₂(x₁y₃−x₃y₁)² + y₁(x₂y₃−x₃y₂)²` to `nlinarith`. -/
theorem titu3 (x₁ x₂ x₃ y₁ y₂ y₃ : ℝ) (h₁ : 0 < y₁) (h₂ : 0 < y₂) (h₃ : 0 < y₃) :
    (x₁ + x₂ + x₃) ^ 2 / (y₁ + y₂ + y₃) ≤ x₁ ^ 2 / y₁ + x₂ ^ 2 / y₂ + x₃ ^ 2 / y₃ := by
  have hsum : 0 < y₁ + y₂ + y₃ := by positivity
  rw [div_add_div _ _ (ne_of_gt h₁) (ne_of_gt h₂),
      div_add_div _ _ (by positivity) (ne_of_gt h₃),
      div_le_div_iff₀ hsum (by positivity)]
  nlinarith [mul_nonneg h₃.le (sq_nonneg (x₁ * y₂ - x₂ * y₁)),
             mul_nonneg h₂.le (sq_nonneg (x₁ * y₃ - x₃ * y₁)),
             mul_nonneg h₁.le (sq_nonneg (x₂ * y₃ - x₃ * y₂)),
             mul_pos h₁ h₂, mul_pos h₂ h₃, mul_pos h₁ h₃,
             mul_pos (mul_pos h₁ h₂) h₃]

/-- The weighted denominators sum to `(t+1)(ab+bc+ca)`. -/
theorem weighted_denoms_sum (a b c t : ℝ) :
    a * (t * b + c) + b * (t * c + a) + c * (t * a + b)
      = (t + 1) * (a * b + b * c + c * a) := by ring

/-- **Weighted Nesbitt inequality (one-parameter family).** For positive reals
`a, b, c` and weight `t > 0`,
`3/(t+1) ≤ a/(t*b+c) + b/(t*c+a) + c/(t*a+b)`. -/
theorem weighted_nesbitt (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : 0 < t) :
    3 / (t + 1) ≤ a / (t * b + c) + b / (t * c + a) + c / (t * a + b) := by
  have ht1 : 0 < t + 1 := by linarith
  have hca : 0 < a * b + b * c + c * a := by positivity
  set y₁ := a * (t * b + c) with hy₁
  set y₂ := b * (t * c + a) with hy₂
  set y₃ := c * (t * a + b) with hy₃
  have hy₁pos : 0 < y₁ := by rw [hy₁]; positivity
  have hy₂pos : 0 < y₂ := by rw [hy₂]; positivity
  have hy₃pos : 0 < y₃ := by rw [hy₃]; positivity
  have e₁ : a / (t * b + c) = a ^ 2 / y₁ := by
    rw [hy₁, pow_two, mul_div_mul_left _ _ (ne_of_gt ha)]
  have e₂ : b / (t * c + a) = b ^ 2 / y₂ := by
    rw [hy₂, pow_two, mul_div_mul_left _ _ (ne_of_gt hb)]
  have e₃ : c / (t * a + b) = c ^ 2 / y₃ := by
    rw [hy₃, pow_two, mul_div_mul_left _ _ (ne_of_gt hc)]
  have hT := titu3 a b c y₁ y₂ y₃ hy₁pos hy₂pos hy₃pos
  have hYsum : y₁ + y₂ + y₃ = (t + 1) * (a * b + b * c + c * a) := by
    rw [hy₁, hy₂, hy₃]; exact weighted_denoms_sum a b c t
  have hlow : 3 / (t + 1) ≤ (a + b + c) ^ 2 / (y₁ + y₂ + y₃) := by
    rw [hYsum, div_le_div_iff₀ ht1 (mul_pos ht1 hca)]
    nlinarith [mul_nonneg ht1.le (sq_nonneg (a - b)),
               mul_nonneg ht1.le (sq_nonneg (b - c)),
               mul_nonneg ht1.le (sq_nonneg (c - a))]
  calc 3 / (t + 1) ≤ (a + b + c) ^ 2 / (y₁ + y₂ + y₃) := hlow
    _ ≤ a ^ 2 / y₁ + b ^ 2 / y₂ + c ^ 2 / y₃ := hT
    _ = a / (t * b + c) + b / (t * c + a) + c / (t * a + b) := by
        rw [← e₁, ← e₂, ← e₃]

/-- **Specialisation to `t = 1` recovers classical Nesbitt.** -/
theorem weighted_nesbitt_one (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h := weighted_nesbitt a b c 1 ha hb hc one_pos
  simp only [one_mul] at h
  linarith [h]

/-- **Equality characterisation.** For weight `t > 0`, equality holds in the
weighted Nesbitt inequality iff `a = b = c`. The forward direction squeezes the
Cauchy–Schwarz and the `(a+b+c)² ≥ 3(ab+bc+ca)` steps to equalities; the latter
forces `a = b = c` through the sum-of-squares `(a−b)²+(b−c)²+(c−a)²`. -/
theorem weighted_nesbitt_eq_iff (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (ht : 0 < t) :
    a / (t * b + c) + b / (t * c + a) + c / (t * a + b) = 3 / (t + 1)
      ↔ a = b ∧ b = c := by
  have ht1 : 0 < t + 1 := by linarith
  have hca : 0 < a * b + b * c + c * a := by positivity
  constructor
  · intro heq
    set y₁ := a * (t * b + c) with hy₁
    set y₂ := b * (t * c + a) with hy₂
    set y₃ := c * (t * a + b) with hy₃
    have hy₁pos : 0 < y₁ := by rw [hy₁]; positivity
    have hy₂pos : 0 < y₂ := by rw [hy₂]; positivity
    have hy₃pos : 0 < y₃ := by rw [hy₃]; positivity
    have e₁ : a / (t * b + c) = a ^ 2 / y₁ := by
      rw [hy₁, pow_two, mul_div_mul_left _ _ (ne_of_gt ha)]
    have e₂ : b / (t * c + a) = b ^ 2 / y₂ := by
      rw [hy₂, pow_two, mul_div_mul_left _ _ (ne_of_gt hb)]
    have e₃ : c / (t * a + b) = c ^ 2 / y₃ := by
      rw [hy₃, pow_two, mul_div_mul_left _ _ (ne_of_gt hc)]
    have hT := titu3 a b c y₁ y₂ y₃ hy₁pos hy₂pos hy₃pos
    have hYsum : y₁ + y₂ + y₃ = (t + 1) * (a * b + b * c + c * a) := by
      rw [hy₁, hy₂, hy₃]; exact weighted_denoms_sum a b c t
    have hsumeq : a ^ 2 / y₁ + b ^ 2 / y₂ + c ^ 2 / y₃ = 3 / (t + 1) := by
      rw [← e₁, ← e₂, ← e₃]; exact heq
    have hlow : 3 / (t + 1) ≤ (a + b + c) ^ 2 / (y₁ + y₂ + y₃) := by
      rw [hYsum, div_le_div_iff₀ ht1 (mul_pos ht1 hca)]
      nlinarith [mul_nonneg ht1.le (sq_nonneg (a - b)),
                 mul_nonneg ht1.le (sq_nonneg (b - c)),
                 mul_nonneg ht1.le (sq_nonneg (c - a))]
    have hupper : (a + b + c) ^ 2 / (y₁ + y₂ + y₃) ≤ 3 / (t + 1) := by
      rw [← hsumeq]; exact hT
    have hmid : (a + b + c) ^ 2 / (y₁ + y₂ + y₃) = 3 / (t + 1) := le_antisymm hupper hlow
    rw [hYsum, div_eq_div_iff (mul_pos ht1 hca).ne' ht1.ne'] at hmid
    -- hmid : (a + b + c) ^ 2 * (t + 1) = 3 * ((t + 1) * (a * b + b * c + c * a))
    have hkey : (a + b + c) ^ 2 = 3 * (a * b + b * c + c * a) := by
      have h2 : (a + b + c) ^ 2 * (t + 1)
          = (3 * (a * b + b * c + c * a)) * (t + 1) := by rw [hmid]; ring
      exact mul_right_cancel₀ ht1.ne' h2
    have e1 : (a - b) ^ 2 = 0 :=
      le_antisymm (by nlinarith [hkey, sq_nonneg (b - c), sq_nonneg (c - a)]) (sq_nonneg _)
    have e2 : (b - c) ^ 2 = 0 :=
      le_antisymm (by nlinarith [hkey, sq_nonneg (a - b), sq_nonneg (c - a)]) (sq_nonneg _)
    have hab : a = b := sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp e1)
    have hbc : b = c := sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp e2)
    exact ⟨hab, hbc⟩
  · rintro ⟨hab, hbc⟩
    rw [hab, hbc]
    have hc0 : c ≠ 0 := ne_of_gt hc
    have ht0 : t + 1 ≠ 0 := ne_of_gt ht1
    have hd : t * c + c ≠ 0 := by
      rw [show t * c + c = c * (t + 1) by ring]; exact mul_ne_zero hc0 ht0
    field_simp
    ring

/-- **Strict weighted Nesbitt inequality.** Unless `a = b = c`, the bound is strict. -/
theorem weighted_nesbitt_lt (a b c t : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ht : 0 < t) (hne : ¬(a = b ∧ b = c)) :
    3 / (t + 1) < a / (t * b + c) + b / (t * c + a) + c / (t * a + b) := by
  rcases lt_or_eq_of_le (weighted_nesbitt a b c t ha hb hc ht) with h | h
  · exact h
  · exact absurd ((weighted_nesbitt_eq_iff a b c t ha hb hc ht).mp h.symm) hne

end NesbittInequalityOQ01OQ02

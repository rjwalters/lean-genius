import Mathlib

/-
# Nesbitt's Inequality

For positive reals `a, b, c`,
`a/(b+c) + b/(c+a) + c/(a+b) ≥ 3/2`,
with equality iff `a = b = c`.

The proof is built on the **sum-of-squares (SOS) identity**

`a/(b+c) + b/(c+a) + c/(a+b) - 3/2`
  `= (a-b)²/(2(b+c)(c+a)) + (b-c)²/(2(c+a)(a+b)) + (c-a)²/(2(a+b)(b+c))`,

obtained by pairing the three terms `a/(b+c) - 1/2 = ((a-b)+(a-c))/(2(b+c))`
and collecting equal differences. Each summand on the right is a nonnegative
number divided by a positive denominator, so the whole right-hand side is `≥ 0`,
giving the inequality; and the right-hand side vanishes exactly when all three
squares vanish, i.e. when `a = b = c`, giving the equality characterisation.

Nesbitt's inequality is absent from Mathlib (no single named lemma) and from the
gallery. It is distinct from the AM–GM family: it bounds a cyclic sum of
fractions rather than comparing a mean.
-/

namespace NesbittInequality

/-- **Sum-of-squares identity for Nesbitt's inequality.** The defect
`Σ a/(b+c) - 3/2` is a sum of three squares over positive denominators. -/
theorem nesbitt_sub_eq (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
      (a - b) ^ 2 / (2 * (b + c) * (c + a)) +
        (b - c) ^ 2 / (2 * (c + a) * (a + b)) +
        (c - a) ^ 2 / (2 * (a + b) * (b + c)) := by
  have hbc : (b + c) ≠ 0 := by positivity
  have hca : (c + a) ≠ 0 := by positivity
  have hab : (a + b) ≠ 0 := by positivity
  field_simp
  ring

/-- **Nesbitt's inequality.** For positive reals `a, b, c`,
`a/(b+c) + b/(c+a) + c/(a+b) ≥ 3/2`. -/
theorem nesbitt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  have h := nesbitt_sub_eq a b c ha hb hc
  have t1 : 0 ≤ (a - b) ^ 2 / (2 * (b + c) * (c + a)) := by positivity
  have t2 : 0 ≤ (b - c) ^ 2 / (2 * (c + a) * (a + b)) := by positivity
  have t3 : 0 ≤ (c - a) ^ 2 / (2 * (a + b) * (b + c)) := by positivity
  linarith

/-- **Equality characterisation.** Equality in Nesbitt's inequality holds iff
`a = b = c`. -/
theorem nesbitt_eq_iff (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (b + c) + b / (c + a) + c / (a + b) = 3 / 2 ↔ a = b ∧ b = c := by
  have h := nesbitt_sub_eq a b c ha hb hc
  constructor
  · intro heq
    have t1 : 0 ≤ (a - b) ^ 2 / (2 * (b + c) * (c + a)) := by positivity
    have t2 : 0 ≤ (b - c) ^ 2 / (2 * (c + a) * (a + b)) := by positivity
    have t3 : 0 ≤ (c - a) ^ 2 / (2 * (a + b) * (b + c)) := by positivity
    have z1 : (a - b) ^ 2 / (2 * (b + c) * (c + a)) = 0 := by linarith
    have z2 : (b - c) ^ 2 / (2 * (c + a) * (a + b)) = 0 := by linarith
    have hD1 : (2 * (b + c) * (c + a)) ≠ 0 := by positivity
    have hD2 : (2 * (c + a) * (a + b)) ≠ 0 := by positivity
    have e1 : (a - b) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp z1 with h' | h'
      · exact h'
      · exact absurd h' hD1
    have e2 : (b - c) ^ 2 = 0 := by
      rcases div_eq_zero_iff.mp z2 with h' | h'
      · exact h'
      · exact absurd h' hD2
    have hab : a = b := sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp e1)
    have hbc : b = c := sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num)).mp e2)
    exact ⟨hab, hbc⟩
  · rintro ⟨hab, hbc⟩
    have e1 : a - b = 0 := by rw [hab]; ring
    have e2 : b - c = 0 := by rw [hbc]; ring
    have e3 : c - a = 0 := by rw [hab, hbc]; ring
    have hrhs :
        (a - b) ^ 2 / (2 * (b + c) * (c + a)) +
            (b - c) ^ 2 / (2 * (c + a) * (a + b)) +
            (c - a) ^ 2 / (2 * (a + b) * (b + c)) = 0 := by
      rw [e1, e2, e3]; norm_num
    linarith [h, hrhs]

/-- **Strict Nesbitt inequality.** Unless `a = b = c`, the inequality is strict. -/
theorem nesbitt_lt (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hne : ¬(a = b ∧ b = c)) :
    3 / 2 < a / (b + c) + b / (c + a) + c / (a + b) := by
  rcases lt_or_eq_of_le (nesbitt a b c ha hb hc) with h | h
  · exact h
  · exact absurd ((nesbitt_eq_iff a b c ha hb hc).mp h.symm) hne

end NesbittInequality

/-
Ready-to-fire Aristotle submission for the n=4 sufficiency plumbing.
Self-contained: the two PROVED helpers are included with their proofs so Aristotle can use
them; the two open pieces are `sorry`. Submit via `mcp__aristotle__prove` (wait=false) with
this whole block as `code`, and the hint at the bottom. (Aristotle backend returned
"Resource not found" for sessions s02–s05; retry when it recovers.)
-/
import Mathlib.Tactic

open Polynomial

namespace VC4

theorem no_root_of_not_square_even {K : Type*} [Field K] {n : ℕ} (hn : Even n)
    {a : K} (h1 : ∀ b : K, b ^ 2 ≠ a) (r : K) :
    (X ^ n - C a : K[X]).eval r ≠ 0 := by
  simp only [eval_sub, eval_pow, eval_X, eval_C]
  intro h
  obtain ⟨m, hm⟩ := hn
  have hrn : r ^ n = a := sub_eq_zero.mp h
  exact h1 (r ^ m) (by rw [← hrn, hm]; ring)

theorem capelli_four_coeff_contra {K : Type*} [Field K] {a p q s t : K}
    (h1 : p + s = 0) (h2 : q + t + p * s = 0) (h3 : p * t + q * s = 0)
    (h4 : q * t = -a)
    (hsq : ∀ b : K, b ^ 2 ≠ a) (hcap : ∀ b : K, a ≠ -(4 * b ^ 4)) : False := by
  have hs : s = -p := by linear_combination h1
  subst hs
  by_cases hp : p = 0
  · subst hp
    have ht : t = -q := by linear_combination h2
    subst ht
    have hqa : q ^ 2 = a := by linear_combination -h4
    exact hsq q hqa
  · have htq : t = q := by
      have hp3 : p * (t - q) = 0 := by linear_combination h3
      rcases mul_eq_zero.mp hp3 with h | h
      · exact absurd h hp
      · linear_combination h
    subst htq
    have hp2 : p ^ 2 = 2 * q := by linear_combination -h2
    have hq2 : q ^ 2 = -a := by linear_combination h4
    have h2ne : (2 : K) ≠ 0 := by
      intro h20
      apply hp
      have hpp : p ^ 2 = 0 := by rw [hp2, h20]; ring
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpp
    obtain ⟨b, hb⟩ : ∃ b : K, p = 2 * b := ⟨p / 2, by field_simp⟩
    apply hcap b
    rw [hb] at hp2
    have hqb : q = 2 * b ^ 2 := by
      apply mul_left_cancel₀ h2ne
      linear_combination -hp2
    rw [hqb] at hq2
    linear_combination hq2

theorem quartic_two_two_coeffs {K : Type*} [Field K] {a p q s t : K}
    (hfac : (X ^ 4 - C a : K[X]) =
      (X ^ 2 + C p * X + C q) * (X ^ 2 + C s * X + C t)) :
    p + s = 0 ∧ q + t + p * s = 0 ∧ p * t + q * s = 0 ∧ q * t = -a := by
  sorry

theorem vahlen_capelli_four_suff {K : Type*} [Field K] {a : K}
    (hsq : ∀ b : K, b ^ 2 ≠ a) (hcap : ∀ b : K, a ≠ -(4 * b ^ 4)) :
    Irreducible (X ^ 4 - C a : K[X]) := by
  sorry

end VC4

/-
HINT for Aristotle:
- quartic_two_two_coeffs: expand the product distributing C via map_add/map_mul, then `ring`
  to X^4 + C(p+s)X^3 + C(q+t+ps)X^2 + C(pt+qs)X + C(qt); compare coefficients at 0..3 using
  coeff_X_pow, coeff_C_mul, coeff_C, coeff_add, coeff_sub.
- vahlen_capelli_four_suff: X^4 - C a is monic of degree 4 (monic_X_pow_sub_C,
  natDegree_X_pow_sub_C). Use the Irreducible constructor; over a field a nonzero non-unit
  has positive natDegree (natDegree_eq_zero ⟹ C c, isUnit_C, isUnit_iff_ne_zero). If
  X^4 - C a = g*h with neither a unit, natDegree_mul gives natDegree g + natDegree h = 4,
  so (1,3),(2,2),(3,1). A degree-1 factor has a root (eq_X_add_C_of_natDegree_le_one),
  contradicting no_root_of_not_square_even (Even 4). The (2,2) case normalises g,h to monic
  quadratics (leading coeffs multiply to 1) and applies quartic_two_two_coeffs then
  capelli_four_coeff_contra.
-/

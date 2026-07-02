import Mathlib

/-!
# Erdős #286, child OQ-01: Small-k Egyptian representations of 1

A child result of `erdos-286` (Erdős Problem #286, unit fractions in short
intervals). The parent asks, for the number `k` of terms, how narrow an interval
of denominators can represent `1` as a sum of `k` distinct unit fractions, and
already proves the **k = 2 impossibility** (`no_k2_representation`) via the
identity `(x-1)(y-1) = 1`.

This entry pins down the exact small-`k` picture with fully machine-checked,
denominator-free (no interval-width) statements:

* **k = 2**: there are **no** two distinct positive integers `a < b` with
  `1/a + 1/b = 1` (`no_two_distinct_unit_fractions`).
* **k = 3, existence**: `1/2 + 1/3 + 1/6 = 1` (`repr_236`).
* **k = 3, uniqueness**: the **only** three distinct positive integers
  `a < b < c` with `1/a + 1/b + 1/c = 1` are `(2, 3, 6)`
  (`three_distinct_unit_fractions_eq_one`).
* Combined characterisation `three_distinct_iff`.

Together these say: `1` has no 2-term distinct Egyptian representation and a
*unique* 3-term one, `{2, 3, 6}` — the smallest `k` for which a representation
exists, matching the parent's requirement that the problem needs `k ≥ 3`.

All results are `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).

## References
* P. Erdős, Problem #286 (unit fractions in short intervals).
* Egyptian fractions / the equation `1 = Σ 1/nᵢ` with distinct `nᵢ`.
-/

namespace Erdos286OQ01

open Finset

/-!
## Section 1: k = 2 — no two distinct unit fractions sum to 1
-/

/-- **k = 2 impossibility.** No two *distinct* positive integers `a < b` satisfy
    `1/a + 1/b = 1`. If `a = 1` the second term would have to vanish; if `a ≥ 2`
    then `b ≥ 3` and `1/a + 1/b ≤ 1/2 + 1/3 = 5/6 < 1`. -/
theorem no_two_distinct_unit_fractions (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (h : (1 : ℚ) / a + 1 / b = 1) : False := by
  have hb : 0 < b := ha.trans hab
  have hqb : (0 : ℚ) < b := by exact_mod_cast hb
  have hbpos : (0 : ℚ) < 1 / b := one_div_pos.mpr hqb
  by_cases ha1 : a = 1
  · subst ha1
    have h11 : (1 : ℚ) / (1 : ℕ) = 1 := by norm_num
    linarith [h, h11, hbpos]
  · have h2a : 2 ≤ a := by omega
    have hb3 : 3 ≤ b := by omega
    have hqa : (0 : ℚ) < a := by exact_mod_cast ha
    have e1 : (1 : ℚ) / a ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast h2a)
    have e2 : (1 : ℚ) / b ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hb3)
    linarith [h, e1, e2]

/-!
## Section 2: k = 3 — existence and uniqueness of {2, 3, 6}
-/

/-- **Existence for k = 3.** The representation `1 = 1/2 + 1/3 + 1/6`. -/
theorem repr_236 : (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 := by norm_num

/-- **Uniqueness for k = 3.** The only strictly increasing triple of positive
    integers `a < b < c` with `1/a + 1/b + 1/c = 1` is `(2, 3, 6)`.

    Proof: `a` is the smallest term so `1 < 3/a`, forcing `a < 3`; and `a = 1`
    is impossible (the other two terms are positive), so `a = 2`. Then
    `1/b + 1/c = 1/2` with `1/c < 1/b` gives `1/4 < 1/b`, i.e. `b < 4`, and
    `b > 2`, so `b = 3`. Finally `1/c = 1/2 - 1/3 = 1/6`, so `c = 6`. -/
theorem three_distinct_unit_fractions_eq_one (a b c : ℕ)
    (ha : 0 < a) (hab : a < b) (hbc : b < c)
    (h : (1 : ℚ) / a + 1 / b + 1 / c = 1) :
    a = 2 ∧ b = 3 ∧ c = 6 := by
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hqa : (0 : ℚ) < a := by exact_mod_cast ha
  have hqb : (0 : ℚ) < b := by exact_mod_cast hb
  have hqc : (0 : ℚ) < c := by exact_mod_cast hc
  have hbpos : (0 : ℚ) < 1 / b := one_div_pos.mpr hqb
  have hcpos : (0 : ℚ) < 1 / c := one_div_pos.mpr hqc
  have hba : (1 : ℚ) / b < 1 / a := one_div_lt_one_div_of_lt hqa (by exact_mod_cast hab)
  have hca : (1 : ℚ) / c < 1 / a := one_div_lt_one_div_of_lt hqa (by exact_mod_cast hab.trans hbc)
  -- upper bound a < 3
  have ha3 : a < 3 := by
    by_contra hcon
    push_neg at hcon
    have e1 : (1 : ℚ) / a ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hcon)
    linarith [h, hba, hca, e1]
  -- rule out a = 1
  have hane1 : a ≠ 1 := by
    intro hcon
    subst hcon
    have h11 : (1 : ℚ) / (1 : ℕ) = 1 := by norm_num
    linarith [h, h11, hbpos, hcpos]
  have ha2 : a = 2 := by omega
  subst ha2
  have h2c : ((2 : ℕ) : ℚ) = 2 := by norm_num
  rw [h2c] at h
  have hsum2 : (1 : ℚ) / b + 1 / c = 1 / 2 := by linarith [h]
  have hcb : (1 : ℚ) / c < 1 / b := one_div_lt_one_div_of_lt hqb (by exact_mod_cast hbc)
  have hb4 : b < 4 := by
    by_contra hcon
    push_neg at hcon
    have e : (1 : ℚ) / b ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hcon)
    linarith [hsum2, hcb, e]
  have hb3 : b = 3 := by omega
  subst hb3
  have h3c : ((3 : ℕ) : ℚ) = 3 := by norm_num
  rw [h3c] at hsum2
  have hc6 : (1 : ℚ) / c = 1 / 6 := by linear_combination hsum2
  simp only [one_div] at hc6
  have hc6' : (c : ℚ) = 6 := inv_inj.mp hc6
  have hc6n : c = 6 := by exact_mod_cast hc6'
  exact ⟨rfl, rfl, hc6n⟩

/-- **Characterisation for k = 3 (ordered).** For strictly increasing positive
    integers, `1/a + 1/b + 1/c = 1` holds *iff* `(a, b, c) = (2, 3, 6)`. -/
theorem three_distinct_iff (a b c : ℕ) (ha : 0 < a) (hab : a < b) (hbc : b < c) :
    (1 : ℚ) / a + 1 / b + 1 / c = 1 ↔ a = 2 ∧ b = 3 ∧ c = 6 := by
  constructor
  · exact three_distinct_unit_fractions_eq_one a b c ha hab hbc
  · rintro ⟨rfl, rfl, rfl⟩; exact repr_236

end Erdos286OQ01

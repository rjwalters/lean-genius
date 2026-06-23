import Mathlib

/-
# Erdős Problem 124 — Sharpness of the Completeness Condition at a Single Base

## What This Proves

The parent entry (`Erdos124CompleteSequences`) formalises the *sufficient*
direction of Erdős Problem 124: if `dᵢ ≥ 2` and `∑ᵢ 1/(dᵢ − 1) ≥ 1`, then every
natural number `n` can be written as a sum `∑ᵢ aᵢ` where each `aᵢ` has only the
digits `0` and `1` in base `dᵢ`.

It is natural to ask whether the hypothesis `∑ᵢ 1/(dᵢ − 1) ≥ 1` is *necessary*.
In full generality necessity is a delicate density statement, but at the
**single–base boundary** `k = 1` it becomes an exact characterisation, which is
what we prove here:

* For one base `d ≥ 2`, every natural number is `0/1`-representable in base `d`
  **iff** `d = 2` **iff** the Erdős sum `1/(d − 1)` is `≥ 1`.

So the parent's sufficient condition is, for a single base, *both* necessary and
sufficient. The obstruction is completely explicit: when `d ≥ 3` the number `2`
already fails to be `0/1`-representable, because its sole base-`d` digit is `2`.

This is the *converse* half that the parent leaves open in the `k = 1` case; it
does not attempt the general (`k ≥ 2`) necessity, which requires an asymptotic
density argument (Burr–Erdős–Graham–Li) and is genuinely harder.

## References
- Burr, Erdős, Graham, Li (1996): "Complete sequences of sets of integer powers"
- https://www.erdosproblems.com/124
-/

namespace Erdos124SingleBaseSharpness

open Nat Finset

/-- `a` is **`0/1`-representable in base `d`** when every base-`d` digit of `a`
equals `0` or `1`. This is exactly the per-base condition used in the parent
theorem `Erdos124.erdos_conjecture_true`, here applied to a single base. -/
def ZeroOne (d a : ℕ) : Prop := ((Nat.digits d a).toFinset ⊆ {0, 1})

/-- Membership criterion for a digit: a digit lies in `{0,1}` iff it is `< 2`. -/
lemma mem_zeroOne_iff (x : ℕ) : x ∈ ({0, 1} : Finset ℕ) ↔ x < 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ## Sufficiency at the boundary: base 2 is always `0/1` -/

/-- In base `2` every natural number is `0/1`-representable: its binary digits
are all `< 2`. This is the `k = 1`, `d = 2` instance of completeness. -/
theorem zeroOne_base_two (n : ℕ) : ZeroOne 2 n := by
  intro x hx
  rw [List.mem_toFinset] at hx
  have hlt : x < 2 := Nat.digits_lt_base (by norm_num) hx
  exact (mem_zeroOne_iff x).2 hlt

/-! ## The explicit obstruction for `d ≥ 3` -/

/-- For `d ≥ 3` the base-`d` digits of `2` are exactly `[2]`. -/
lemma digits_two_of_three_le {d : ℕ} (hd : 3 ≤ d) : Nat.digits d 2 = [2] := by
  rw [Nat.digits_def' (by omega : 2 ≤ d) (by norm_num : 0 < 2)]
  rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  simp

/-- **Obstruction.** For any base `d ≥ 3`, the number `2` is *not*
`0/1`-representable: its only base-`d` digit is `2 ∉ {0,1}`. This single
counterexample is what breaks completeness once `d ≥ 3`. -/
theorem not_zeroOne_two_of_three_le {d : ℕ} (hd : 3 ≤ d) : ¬ ZeroOne d 2 := by
  intro h
  have hmem : (2 : ℕ) ∈ (Nat.digits d 2).toFinset := by
    rw [digits_two_of_three_le hd]; simp
  have : (2 : ℕ) ∈ ({0, 1} : Finset ℕ) := h hmem
  rw [mem_zeroOne_iff] at this
  omega

/-! ## Completeness characterisation at a single base -/

/-- **Single-base completeness characterisation.** For one base `d ≥ 2`, every
natural number is `0/1`-representable in base `d` **iff** `d = 2`. The forward
direction uses the explicit obstruction at `n = 2`; the reverse is base-2
completeness. -/
theorem zeroOne_all_iff_two {d : ℕ} (hd : 2 ≤ d) :
    (∀ n, ZeroOne d n) ↔ d = 2 := by
  constructor
  · intro h
    by_contra hne
    exact not_zeroOne_two_of_three_le (by omega) (h 2)
  · rintro rfl
    exact zeroOne_base_two

/-! ## The Erdős sum condition at a single base -/

/-- At `k = 1` the Erdős sum `∑ᵢ 1/(dᵢ − 1)` is just `1/(d − 1)`, and the
threshold condition `1 ≤ 1/(d − 1)` holds **iff** `d = 2`. -/
theorem sum_cond_iff_two {d : ℕ} (hd : 2 ≤ d) :
    (1 : ℚ) ≤ 1 / ((d : ℚ) - 1) ↔ d = 2 := by
  have hdpos : (0 : ℚ) < (d : ℚ) - 1 := by
    have : (2 : ℚ) ≤ (d : ℚ) := by exact_mod_cast hd
    linarith
  rw [le_div_iff₀ hdpos]
  constructor
  · intro h
    have hle : (d : ℚ) ≤ 2 := by linarith
    have : d ≤ 2 := by exact_mod_cast hle
    omega
  · rintro rfl; norm_num

/-! ## Synthesis: sharpness of the Erdős condition at the boundary -/

/-- **Sharpness (main result).** For a single base `d ≥ 2`, the Erdős sum
condition that the parent proves *sufficient* is in fact *necessary and
sufficient* for completeness:

`(every n is 0/1-representable in base d)  ↔  1 ≤ 1/(d − 1)`.

Both sides are equivalent to `d = 2`. This pins down the threshold exactly at
the single-base boundary: relaxing `1/(d − 1) ≥ 1` to any base `d ≥ 3` destroys
completeness, with `n = 2` an explicit witness. -/
theorem single_base_complete_iff_sum_cond {d : ℕ} (hd : 2 ≤ d) :
    (∀ n, ZeroOne d n) ↔ (1 : ℚ) ≤ 1 / ((d : ℚ) - 1) := by
  rw [zeroOne_all_iff_two hd, sum_cond_iff_two hd]

/-! ## Concrete cross-checks -/

/-- Base 3 is incomplete, with `2` the explicit failing value. -/
theorem base_three_incomplete : ¬ (∀ n, ZeroOne 3 n) := by
  rw [zeroOne_all_iff_two (by norm_num)]; norm_num

/-- The failing digit string for `2` in base 3 is `[2]`. -/
example : Nat.digits 3 2 = [2] := digits_two_of_three_le (by norm_num)

/-- A positive cross-check in base 2: `5 = 101₂` has digits `[1,0,1] ⊆ {0,1}`. -/
example : Nat.digits 2 5 = [1, 0, 1] := by
  rw [Nat.digits_def' (by norm_num : 2 ≤ 2) (by norm_num : 0 < 5)]
  rw [Nat.digits_def' (by norm_num : 2 ≤ 2) (by norm_num : 0 < 5 / 2)]
  rw [Nat.digits_def' (by norm_num : 2 ≤ 2) (by norm_num : 0 < 5 / 2 / 2)]
  norm_num

/-- Base 2 completeness, restated as the `d = 2` instance of the characterisation. -/
theorem base_two_complete : ∀ n, ZeroOne 2 n := zeroOne_base_two

end Erdos124SingleBaseSharpness

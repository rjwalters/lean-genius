/-
  Aristotle targets for Erdős Problem #977: Greatest Prime Factor of 2^n - 1
  Routine supporting lemmas for automated proof search.
  See Erdos977Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main deep results (Stewart 2013, Schinzel 1962 bound, Zsygmondy)
  - Routine arithmetic about Mersenne numbers 2^n - 1
  - GPF definition lemmas derivable from Mathlib's primeFactors API
  - Conditional derivations given deep results as hypotheses
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings
-/
import Mathlib

namespace Erdos977Aristotle

open Nat Finset Filter Real

/-
## Section 1: Mersenne Number Arithmetic

Basic facts about Mersenne numbers M_n = 2^n - 1.
These are routine Nat arithmetic lemmas.
-/

/-- 2^n ≥ 1 for all n. -/
theorem two_pow_ge_one (n : ℕ) : 1 ≤ 2 ^ n :=
  Nat.one_le_two_pow

/-- For n ≥ 1, 2^n ≥ 2. -/
theorem two_pow_ge_two (n : ℕ) (hn : n ≥ 1) : 2 ≤ 2 ^ n := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- For n ≥ 2, 2^n ≥ 4. -/
theorem two_pow_ge_four (n : ℕ) (hn : n ≥ 2) : 4 ≤ 2 ^ n := by
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

/-- Mersenne number is positive: 2^n - 1 > 0 for n ≥ 1. -/
theorem mersenne_val_pos (n : ℕ) (hn : n ≥ 1) : 0 < 2 ^ n - 1 := by
  have h := two_pow_ge_two n hn; omega

/-- Mersenne number exceeds 1: 2^n - 1 > 1 for n ≥ 2. -/
theorem mersenne_val_gt_one (n : ℕ) (hn : n ≥ 2) : 1 < 2 ^ n - 1 := by
  have h := two_pow_ge_four n hn; omega

/-
## Section 2: Concrete Mersenne Values
-/

/-- M_2 = 3. -/
theorem mersenne_2 : 2 ^ 2 - 1 = 3 := by norm_num

/-- M_3 = 7. -/
theorem mersenne_3 : 2 ^ 3 - 1 = 7 := by norm_num

/-- M_5 = 31. -/
theorem mersenne_5 : 2 ^ 5 - 1 = 31 := by norm_num

/-- M_7 = 127. -/
theorem mersenne_7 : 2 ^ 7 - 1 = 127 := by norm_num

/-- M_11 = 2047. -/
theorem mersenne_11 : 2 ^ 11 - 1 = 2047 := by norm_num

/-- 2047 = 23 × 89. -/
theorem mersenne_11_factors : 2047 = 23 * 89 := by norm_num

/-- 3 is prime. -/
theorem three_prime : Nat.Prime 3 := by norm_num

/-- 7 is prime. -/
theorem seven_prime : Nat.Prime 7 := by norm_num

/-- 31 is prime. -/
theorem thirty_one_prime : Nat.Prime 31 := by norm_num

/-- 127 is prime. -/
theorem one_twenty_seven_prime : Nat.Prime 127 := by norm_num

/-- 89 is prime. -/
theorem eighty_nine_prime : Nat.Prime 89 := by norm_num

/-- 23 is prime. -/
theorem twenty_three_prime : Nat.Prime 23 := by norm_num

/-- Schinzel bound check at n = 11: 89 > 2 × 11. -/
theorem schinzel_check_11 : 2 * 11 < 89 := by norm_num

/-- M_2 is prime. -/
theorem mersenne_prime_n2 : Nat.Prime (2 ^ 2 - 1) := by norm_num

/-- M_3 is prime. -/
theorem mersenne_prime_n3 : Nat.Prime (2 ^ 3 - 1) := by norm_num

/-- M_5 is prime. -/
theorem mersenne_prime_n5 : Nat.Prime (2 ^ 5 - 1) := by norm_num

/-- M_7 is prime. -/
theorem mersenne_prime_n7 : Nat.Prime (2 ^ 7 - 1) := by norm_num

/-
## Section 3: primeFactors API Lemmas

These correspond to the custom greatestPrimeFactor goals in the main file.
-/

/-- n.primeFactors is nonempty for n > 1. -/
theorem primeFactors_nonempty_of_gt_one (n : ℕ) (hn : n > 1) : n.primeFactors.Nonempty :=
  Nat.primeFactors_nonempty hn

/-- Every element of n.primeFactors divides n. -/
theorem primeFactors_dvd (n p : ℕ) (hp : p ∈ n.primeFactors) : p ∣ n :=
  Nat.dvd_of_mem_primeFactors hp

/-- Every element of n.primeFactors is prime. -/
theorem primeFactors_prime (n p : ℕ) (hp : p ∈ n.primeFactors) : p.Prime :=
  Nat.prime_of_mem_primeFactors hp

/-- max' of primeFactors is a member of primeFactors. -/
theorem primeFactors_max_mem (n : ℕ) (hn : n > 1) :
    n.primeFactors.max' (Nat.primeFactors_nonempty hn) ∈ n.primeFactors :=
  Finset.max'_mem _ _

/-- max' of primeFactors divides n. -/
theorem primeFactors_max_dvd (n : ℕ) (hn : n > 1) :
    n.primeFactors.max' (Nat.primeFactors_nonempty hn) ∣ n :=
  Nat.dvd_of_mem_primeFactors (primeFactors_max_mem n hn)

/-- max' of primeFactors is prime. -/
theorem primeFactors_max_prime (n : ℕ) (hn : n > 1) :
    (n.primeFactors.max' (Nat.primeFactors_nonempty hn)).Prime :=
  Nat.prime_of_mem_primeFactors (primeFactors_max_mem n hn)

/-- max' of primeFactors is an upper bound for all prime divisors. -/
theorem primeFactors_max_ge (n p : ℕ) (hn : n > 1) (hp : p.Prime) (hdvd : p ∣ n) :
    p ≤ n.primeFactors.max' (Nat.primeFactors_nonempty hn) := by
  apply Finset.le_max'
  exact Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩

/-
## Section 4: Cast and Ratio Lemmas
-/

/-- Casting 2^n - 1 from ℕ to ℝ for n ≥ 1. -/
theorem cast_mersenne_val (n : ℕ) (hn : n ≥ 1) :
    ((2 ^ n - 1 : ℕ) : ℝ) = (2 : ℝ) ^ n - 1 := by
  sorry

/-- P > 2n (ℕ) implies P/n > 2 (ℝ) for n > 0. -/
theorem div_gt_two_of_gt_two_mul (p n : ℕ) (hn : 0 < n) (h : 2 * n < p) :
    2 < (p : ℝ) / n := by
  rw [gt_iff_lt, lt_div_iff (Nat.cast_pos.mpr hn)]
  push_cast
  linarith

/-- Mersenne ratio is positive for n ≥ 1. -/
theorem mersenne_ratio_pos (n : ℕ) (hn : n ≥ 1) :
    0 < ((2 ^ n - 1 : ℕ) : ℝ) / n := by
  apply div_pos
  · exact_mod_cast mersenne_val_pos n hn
  · exact Nat.cast_pos.mpr (by omega)

/-
## Section 5: Filter / Tendsto Lemmas
-/

/-- n^ε → ∞ for ε > 0 (as ℕ → ℝ). -/
theorem rpow_atTop_of_pos (ε : ℝ) (hε : ε > 0) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
  (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop

/-- Stewart's quantitative bound implies GPF(M_n)/n → ∞. -/
theorem stewart_bound_implies_div_atTop (f : ℕ → ℝ) (ε : ℝ) (hε : ε > 0)
    (hbound : ∀ᶠ n in atTop, f n ≥ (n : ℝ) ^ (1 + ε)) :
    Tendsto (fun n => f n / n) atTop atTop := by
  sorry

/-- (2^n - 1)/n → ∞ as n → ∞ (in ℝ). -/
theorem mersenne_ratio_atTop :
    Tendsto (fun n : ℕ => ((2 ^ n - 1 : ℕ) : ℝ) / n) atTop atTop := by
  sorry

/-
## Section 6: Utility Lemmas
-/

/-- n > 12 implies n > 1. -/
theorem gt12_gt1 (n : ℕ) (hn : n > 12) : n > 1 := by omega

/-- n > 12 implies n ≥ 2. -/
theorem gt12_ge2 (n : ℕ) (hn : n > 12) : n ≥ 2 := by omega

/-- n > 6 implies n ≥ 2. -/
theorem gt6_ge2 (n : ℕ) (hn : n > 6) : n ≥ 2 := by omega

/-- 2 * n < p implies p > n. -/
theorem gt_of_two_mul_lt (n p : ℕ) (h : 2 * n < p) : n < p := by omega

/-- For p prime, p ≥ 2. -/
theorem prime_ge_two (p : ℕ) (hp : p.Prime) : 2 ≤ p := hp.two_le

end Erdos977Aristotle

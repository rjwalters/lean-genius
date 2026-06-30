import Mathlib

/-!
# Sylvester's sequence: closed-form partial reciprocal sums and pairwise coprimality

Sylvester's sequence is defined by `a₀ = 2` and `a_{n+1} = aₙ² - aₙ + 1`, giving
`2, 3, 7, 43, 1807, 3263443, …`.

This file establishes two classical elementary facts, fully machine-checked:

* **Closed-form partial sums** (`syl_partial_sum`):
  `∑_{k=0}^{n} 1/aₖ = 1 - 1/(a_{n+1} - 1)`.
  Since `a_{n+1} - 1 → ∞`, the infinite sum of reciprocals equals `1`.

* **Pairwise coprimality** (`syl_coprime`): distinct terms are coprime, via the
  product formula `a_{n+1} = (∏_{k≤n} aₖ) + 1` (a Euclid-style identity).

The engine is the telescoping identity `1/aₙ = 1/(aₙ-1) - 1/(a_{n+1}-1)`, which holds
because `a_{n+1} - 1 = aₙ(aₙ - 1)`.

No axioms, no sorries.
-/

namespace SylvesterSequenceOQ01

/-- Sylvester's sequence: `a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`. -/
def syl : ℕ → ℕ
  | 0 => 2
  | (n + 1) => syl n ^ 2 - syl n + 1

@[simp] theorem syl_zero : syl 0 = 2 := rfl

theorem syl_succ (n : ℕ) : syl (n + 1) = syl n ^ 2 - syl n + 1 := rfl

/-- Every term is at least `2`. -/
theorem two_le_syl (n : ℕ) : 2 ≤ syl n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : syl k + 2 ≤ syl k ^ 2 := by nlinarith [ih]
    rw [syl_succ]
    omega

/-- The recurrence, lifted to `ℤ` (no truncated subtraction). -/
theorem syl_cast_succ (n : ℕ) :
    (syl (n + 1) : ℤ) = (syl n : ℤ) ^ 2 - (syl n : ℤ) + 1 := by
  have h1 : syl n ≤ syl n ^ 2 := by nlinarith [two_le_syl n]
  rw [syl_succ]
  push_cast [Nat.cast_sub h1]
  ring

/-- Telescoping per-term identity: `1/aₙ = 1/(aₙ-1) - 1/(a_{n+1}-1)`. -/
theorem syl_recip_term (n : ℕ) :
    (1 : ℚ) / (syl n : ℚ)
      = 1 / ((syl n : ℚ) - 1) - 1 / ((syl (n + 1) : ℚ) - 1) := by
  have ha : (2 : ℚ) ≤ (syl n : ℚ) := by exact_mod_cast two_le_syl n
  have hsucc : (syl (n + 1) : ℚ) = (syl n : ℚ) ^ 2 - (syl n : ℚ) + 1 := by
    exact_mod_cast syl_cast_succ n
  have h0 : (syl n : ℚ) ≠ 0 := by linarith
  have h1 : (syl n : ℚ) - 1 ≠ 0 := by linarith
  have h2 : (syl n : ℚ) ^ 2 - (syl n : ℚ) + 1 - 1 ≠ 0 := by nlinarith [ha]
  rw [hsucc]
  field_simp
  ring

/-- Closed form for partial sums of reciprocals: `∑_{k≤n} 1/aₖ = 1 - 1/(a_{n+1}-1)`. -/
theorem syl_partial_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (1 : ℚ) / (syl k : ℚ)
      = 1 - 1 / ((syl (n + 1) : ℚ) - 1) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    norm_num [show syl 0 = 2 from rfl, show syl (0 + 1) = 3 from rfl]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, syl_recip_term (m + 1)]
    ring

/-- Euclid-style product formula: `a_{n+1} = (∏_{k≤n} aₖ) + 1`. -/
theorem syl_eq_prod_add_one (n : ℕ) :
    syl (n + 1) = (∏ k ∈ Finset.range (n + 1), syl k) + 1 := by
  induction n with
  | zero => rw [Finset.prod_range_one]; rfl
  | succ m ih =>
    rw [Finset.prod_range_succ]
    have hp : (∏ k ∈ Finset.range (m + 1), syl k) = syl (m + 1) - 1 := by omega
    rw [hp, syl_succ, pow_two, Nat.sub_one_mul]

/-- Each term divides any later term minus one: `aᵢ ∣ a_{n+1} - 1` for `i ≤ n`. -/
theorem syl_dvd_succ_sub_one {i n : ℕ} (h : i ≤ n) : syl i ∣ syl (n + 1) - 1 := by
  rw [syl_eq_prod_add_one, Nat.add_sub_cancel]
  exact Finset.dvd_prod_of_mem syl (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-- Distinct terms of Sylvester's sequence are coprime. -/
theorem syl_coprime {i j : ℕ} (h : i < j) : Nat.Coprime (syl i) (syl j) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt h
  -- now `j = i + n + 1`
  have key : syl i ∣ syl (i + n + 1) - 1 := syl_dvd_succ_sub_one (Nat.le_add_right i n)
  have hge : (1 : ℕ) ≤ syl (i + n + 1) := le_trans (by norm_num) (two_le_syl _)
  have hd1 : Nat.gcd (syl i) (syl (i + n + 1)) ∣ syl i := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (syl i) (syl (i + n + 1)) ∣ syl (i + n + 1) := Nat.gcd_dvd_right _ _
  have hd3 : Nat.gcd (syl i) (syl (i + n + 1)) ∣ syl (i + n + 1) - 1 := hd1.trans key
  have hone : Nat.gcd (syl i) (syl (i + n + 1)) ∣ 1 := by
    have hsub := Nat.dvd_sub hd2 hd3
    rwa [Nat.sub_sub_self hge] at hsub
  exact Nat.dvd_one.mp hone

end SylvesterSequenceOQ01

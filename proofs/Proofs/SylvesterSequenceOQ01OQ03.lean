import Mathlib

/-!
# Sylvester's sequence: the arithmetic skeleton (residue and coprimality structure)

Sylvester's sequence is defined by `a₀ = 2` and `a_{n+1} = aₙ² - aₙ + 1`, giving
`2, 3, 7, 43, 1807, 3263443, …`.

Each term is one more than the product of all earlier terms, and this single
Euclid-style identity forces a rigid arithmetic skeleton. This file formalizes
that skeleton in full, machine-checked with no axioms and no sorries:

* **Multiplicative engine** (`syl_succ_sub_one`):
  `a_{n+1} - 1 = aₙ · (aₙ - 1)`, the consecutive-integer factorization.

* **Euclid product identity** (`syl_sub_one_eq_prod`):
  `a_{n+1} - 1 = ∏_{k≤n} aₖ`.

* **Residue mod earlier terms** (`syl_mod_earlier`):
  `aₙ ≡ 1 (mod aᵢ)` for every `i < n`; equivalently `aᵢ ∣ aₙ - 1`.

* **Pairwise coprimality** (`syl_coprime`): distinct terms are coprime — an
  immediate consequence of the residue structure.

* **Parity** (`syl_odd`): every term past the first is odd, because
  `aₙ · (aₙ - 1)` is a product of consecutive integers hence even.

* **Residue mod 6** (`syl_mod_six`): from `a₂ = 7` on, every term is `≡ 1 (mod 6)`,
  because `6 ∣ aₙ - 1` propagates through `a_{n+1} - 1 = aₙ · (aₙ - 1)`.

The product-formula and coprimality facts overlap with the companion file
`SylvesterSequenceOQ01`; they are reproved here (briefly) so the arithmetic
skeleton is a single self-contained package. The parity and `mod 6` residue
structure, and the `≡ 1 (mod aᵢ)` residue phrasing, are the new content.
-/

namespace SylvesterSequenceOQ01OQ03

/-- Sylvester's sequence: `a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`. -/
def syl : ℕ → ℕ
  | 0 => 2
  | (n + 1) => syl n ^ 2 - syl n + 1

@[simp] theorem syl_zero : syl 0 = 2 := rfl
@[simp] theorem syl_one : syl 1 = 3 := rfl
@[simp] theorem syl_two : syl 2 = 7 := rfl

theorem syl_succ (n : ℕ) : syl (n + 1) = syl n ^ 2 - syl n + 1 := rfl

/-- Every term is at least `2`. -/
theorem two_le_syl (n : ℕ) : 2 ≤ syl n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : syl k + 2 ≤ syl k ^ 2 := by nlinarith [ih]
    rw [syl_succ]
    omega

/-- The multiplicative engine: `a_{n+1} - 1 = aₙ · (aₙ - 1)`, a product of two
consecutive integers.  All later structure flows from this factorization. -/
theorem syl_succ_sub_one (n : ℕ) : syl (n + 1) - 1 = syl n * (syl n - 1) := by
  have h2 : 2 ≤ syl n := two_le_syl n
  -- Write `aₙ = p + 2` to eliminate all truncated subtraction, then compute.
  obtain ⟨p, hp⟩ : ∃ p, syl n = p + 2 := ⟨syl n - 2, by omega⟩
  have key : syl (n + 1) = p * p + 3 * p + 3 := by
    rw [syl_succ, hp, pow_two]
    have hexp : (p + 2) * (p + 2) = p * p + 4 * p + 4 := by ring
    rw [hexp]; omega
  have hrhs : (p + 2) * (p + 2 - 1) = p * p + 3 * p + 2 := by
    have h3 : p + 2 - 1 = p + 1 := by omega
    rw [h3]; ring
  rw [key, hp, hrhs]; omega

/-- Euclid-style product identity: `a_{n+1} - 1 = ∏_{k≤n} aₖ`. -/
theorem syl_sub_one_eq_prod (n : ℕ) :
    syl (n + 1) - 1 = ∏ k ∈ Finset.range (n + 1), syl k := by
  induction n with
  | zero => simp [Finset.prod_range_one]
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, syl_succ_sub_one (m + 1)]
    exact Nat.mul_comm _ _

/-- Each earlier term divides any later term minus one: `aᵢ ∣ aₙ - 1` for `i < n`. -/
theorem syl_dvd_sub_one {i n : ℕ} (h : i < n) : syl i ∣ syl n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [syl_sub_one_eq_prod]
  exact Finset.dvd_prod_of_mem syl (Finset.mem_range.mpr (by omega))

/-- Residue mod earlier terms: `aₙ ≡ 1 (mod aᵢ)` for `i < n`. -/
theorem syl_mod_earlier {i n : ℕ} (h : i < n) : syl n % syl i = 1 := by
  have hdvd : syl i ∣ syl n - 1 := syl_dvd_sub_one h
  have h1 : 1 ≤ syl n := le_trans (by norm_num) (two_le_syl n)
  have h2 : 2 ≤ syl i := two_le_syl i
  -- `1 ≡ aₙ (mod aᵢ)` since `aᵢ ∣ aₙ - 1`, then reduce `1 % aᵢ = 1`.
  have hmod : (1 : ℕ) ≡ syl n [MOD syl i] := (Nat.modEq_iff_dvd' h1).mpr hdvd
  have hswap : syl n % syl i = 1 % syl i := hmod.symm
  rw [hswap, Nat.mod_eq_of_lt (by omega : 1 < syl i)]

/-- Distinct terms (with `i < j`) of Sylvester's sequence are coprime. -/
theorem syl_coprime_of_lt {i j : ℕ} (h : i < j) : Nat.Coprime (syl i) (syl j) := by
  have key : syl i ∣ syl j - 1 := syl_dvd_sub_one h
  have hge : 1 ≤ syl j := le_trans (by norm_num) (two_le_syl j)
  have hd1 : Nat.gcd (syl i) (syl j) ∣ syl i := Nat.gcd_dvd_left _ _
  have hd2 : Nat.gcd (syl i) (syl j) ∣ syl j := Nat.gcd_dvd_right _ _
  have hd3 : Nat.gcd (syl i) (syl j) ∣ syl j - 1 := hd1.trans key
  have hone : Nat.gcd (syl i) (syl j) ∣ 1 := by
    have hsub := Nat.dvd_sub hd2 hd3
    rwa [Nat.sub_sub_self hge] at hsub
  exact Nat.dvd_one.mp hone

/-- Distinct terms of Sylvester's sequence are coprime. -/
theorem syl_coprime {i j : ℕ} (h : i ≠ j) : Nat.Coprime (syl i) (syl j) := by
  rcases Nat.lt_or_ge i j with hlt | hge
  · exact syl_coprime_of_lt hlt
  · exact (syl_coprime_of_lt (by omega : j < i)).symm

/-- Every term past the first is odd: `aₙ` is odd for `n ≥ 1`. -/
theorem syl_odd {n : ℕ} (hn : 1 ≤ n) : Odd (syl n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  -- `a_{m+1} - 1 = aₘ · (aₘ - 1)` is a product of consecutive integers, hence even.
  have heven : Even (syl m * (syl m - 1)) := by
    rcases Nat.even_or_odd (syl m) with he | ho
    · exact he.mul_right _
    · exact (Nat.Odd.sub_odd ho odd_one).mul_left _
  have hsub : syl (m + 1) - 1 = syl m * (syl m - 1) := syl_succ_sub_one m
  have hge : 1 ≤ syl (m + 1) := le_trans (by norm_num) (two_le_syl (m + 1))
  rcases heven with ⟨t, ht⟩
  exact ⟨t, by omega⟩

/-- The `mod 6` invariant propagates: `6 ∣ aₙ - 1` for `n ≥ 2`. -/
theorem six_dvd_syl_sub_one {n : ℕ} (hn : 2 ≤ n) : 6 ∣ syl n - 1 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m _ ih =>
    rw [syl_succ_sub_one m]
    exact ih.mul_left (syl m)

/-- Residue mod 6: `aₙ ≡ 1 (mod 6)` for `n ≥ 2`. -/
theorem syl_mod_six {n : ℕ} (hn : 2 ≤ n) : syl n % 6 = 1 := by
  have hdvd : 6 ∣ syl n - 1 := six_dvd_syl_sub_one hn
  have h1 : 1 ≤ syl n := le_trans (by norm_num) (two_le_syl n)
  obtain ⟨c, hc⟩ := hdvd
  omega

end SylvesterSequenceOQ01OQ03

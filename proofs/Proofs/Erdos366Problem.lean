/-
  Erdős Problem #366: Consecutive k-Full Numbers

  Are there any 2-full n such that n+1 is 3-full?

  **Definitions**:
  - n is k-full if for every prime p dividing n, we have p^k | n
  - 2-full = powerful = squareful (every prime factor appears at least squared)
  - 3-full = cubeful (every prime factor appears at least cubed)

  **Known Results**:
  - (8, 9): 8 = 2³ is 3-full, 9 = 3² is 2-full (reverse direction)
  - (12167, 12168): 12167 = 23³ is 3-full, 12168 = 2³ × 3² × 13² is 2-full
  - No 2-full n with 3-full n+1 known (OPEN as of 2024)
  - No other 3-full/2-full pairs below 10^22

  References:
  - https://erdosproblems.com/366
  - Golomb, S.W., "Powerful numbers" (1970)
  - Guy, R.K., "Unsolved Problems in Number Theory" (2004), Problem B16
-/

import Mathlib

open Nat Finset

namespace Erdos366

/-
## Background: k-Full Numbers

A natural number n is **k-full** if every prime factor p of n appears
with multiplicity at least k. Equivalently, p | n implies p^k | n.

Special cases:
- 1-full: all positive integers
- 2-full: powerful numbers (also called squareful)
- 3-full: cubeful numbers
-/

/-- n is k-full if every prime factor of n appears with multiplicity ≥ k.
That is, if p | n then p^k | n. Equivalently, n.factorization p ≥ k for all p | n. -/
def IsKFull (k n : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ n → k ≤ n.factorization p

/-- Alternative definition: n is k-full iff all prime factors have multiplicity ≥ k. -/
def IsKFull' (k n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, k ≤ n.factorization p

/-- 2-full numbers are also called **powerful** numbers. -/
def IsPowerful (n : ℕ) : Prop := IsKFull 2 n

/-- 3-full numbers are called **cubeful** numbers. -/
def IsCubeful (n : ℕ) : Prop := IsKFull 3 n

/-
## Structural Properties
-/

/-- The two definitions of k-full are equivalent for nonzero n. -/
theorem isKFull_iff_isKFull' {k n : ℕ} (hn : n ≠ 0) : IsKFull k n ↔ IsKFull' k n := by
  constructor
  · intro h p hmem
    have ⟨hp, hdvd, _⟩ := Nat.mem_primeFactors.mp hmem
    exact h p hp hdvd
  · intro h p hp hdvd
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, hn⟩)

/-- If n is k-full and j ≤ k, then n is also j-full. -/
theorem IsKFull.mono {j k n : ℕ} (hjk : j ≤ k) (h : IsKFull k n) : IsKFull j n :=
  fun p hp hdvd => le_trans hjk (h p hp hdvd)

/-
## Basic Properties of k-Full Numbers
-/

/-- 1 is vacuously k-full for any k (no prime factors). -/
theorem one_is_kfull (k : ℕ) : IsKFull k 1 := by
  intro p hp hdiv
  exact absurd (Nat.dvd_one.mp hdiv) hp.ne_one

/-
## Helper Lemmas
-/

/-- If p^k divides n (with p prime and n ≠ 0), then k ≤ n.factorization p.
Uses factorization_le_iff_dvd and evaluates the factorization of the prime power. -/
private theorem le_factorization_of_pow_dvd {p k n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h : p ^ k ∣ n) : k ≤ n.factorization p := by
  have h1 := ((Nat.factorization_le_iff_dvd (pow_ne_zero k hp.ne_zero) hn).mpr h) p
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    hp.factorization, Finsupp.single_eq_same, mul_one] at h1
  exact h1

/-- If p is prime and divides q^k where q is also prime, then p = q. -/
private theorem eq_of_prime_of_dvd_prime_pow {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {k : ℕ} (h : p ∣ q ^ k) : p = q :=
  (hq.eq_one_or_self_of_dvd p (hp.dvd_of_dvd_pow h)).resolve_left hp.ne_one

/-
## Examples of k-Full Numbers
-/

/-- 8 = 2³ is 3-full (cubeful). -/
theorem eight_is_cubeful : IsCubeful 8 := by
  intro p hp hdvd
  have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
  rw [h8] at hdvd
  have hp2 : p = 2 := eq_of_prime_of_dvd_prime_pow hp (by norm_num) hdvd
  subst hp2
  exact le_factorization_of_pow_dvd hp (by norm_num) (by norm_num : 2 ^ 3 ∣ 8)

/-- 9 = 3² is 2-full (powerful). -/
theorem nine_is_powerful : IsPowerful 9 := by
  intro p hp hdvd
  have h9 : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h9] at hdvd
  have hp3 : p = 3 := eq_of_prime_of_dvd_prime_pow hp (by norm_num) hdvd
  subst hp3
  exact le_factorization_of_pow_dvd hp (by norm_num) (by norm_num : 3 ^ 2 ∣ 9)

/-
## The Main Question: 2-Full n with 3-Full n+1

Erdős asked whether there exists any n such that:
- n is 2-full (powerful)
- n+1 is 3-full (cubeful)

This remains OPEN as of 2024.
-/

/-- **Erdős Problem #366**: Does there exist n > 0 such that
n is 2-full and n+1 is 3-full? -/
def erdos_366_conjecture : Prop :=
  ∃ n > 0, IsPowerful n ∧ IsCubeful (n + 1)

/-
## The Reverse Direction: 3-Full n with 2-Full n+1

The reverse direction has known solutions!
-/

/-- The set of pairs (n, n+1) where n is 3-full and n+1 is 2-full. -/
def CubefulPowerfulPairs : Set ℕ := { n | IsCubeful n ∧ IsPowerful (n + 1) }

/-- (8, 9) is a cubeful-powerful pair: 8 = 2³ is cubeful, 9 = 3² is powerful. -/
theorem eight_nine_pair : 8 ∈ CubefulPowerfulPairs := ⟨eight_is_cubeful, nine_is_powerful⟩

/-- 12167 = 23³ is cubeful. -/
theorem cubeful_12167 : IsCubeful 12167 := by
  intro p hp hdvd
  have h : (12167 : ℕ) = 23 ^ 3 := by norm_num
  rw [h] at hdvd
  have hp23 : p = 23 := eq_of_prime_of_dvd_prime_pow hp (by norm_num) hdvd
  subst hp23
  exact le_factorization_of_pow_dvd hp (by norm_num) (by norm_num : 23 ^ 3 ∣ 12167)

/-- 12168 = 2³ × 3² × 13² is powerful. -/
theorem powerful_12168 : IsPowerful 12168 := by
  intro p hp hdvd
  have hf : (12168 : ℕ) = 2 ^ 3 * (3 ^ 2 * 13 ^ 2) := by norm_num
  rw [hf] at hdvd
  rcases hp.dvd_or_dvd hdvd with h1 | h1
  · -- p | 2^3 → p = 2
    have := eq_of_prime_of_dvd_prime_pow hp (by norm_num) h1
    subst this
    exact le_factorization_of_pow_dvd hp (by norm_num) (by norm_num : 2 ^ 2 ∣ 12168)
  · rcases hp.dvd_or_dvd h1 with h2 | h2
    · -- p | 3^2 → p = 3
      have := eq_of_prime_of_dvd_prime_pow hp (by norm_num) h2
      subst this
      exact le_factorization_of_pow_dvd hp (by norm_num) (by norm_num : 3 ^ 2 ∣ 12168)
    · -- p | 13^2 → p = 13
      have := eq_of_prime_of_dvd_prime_pow hp (by norm_num) h2
      subst this
      exact le_factorization_of_pow_dvd hp (by norm_num) (by norm_num : 13 ^ 2 ∣ 12168)

/-- (12167, 12168) is a cubeful-powerful pair (Golomb 1970). -/
theorem golomb_pair : 12167 ∈ CubefulPowerfulPairs :=
  ⟨cubeful_12167, powerful_12168⟩

/-
## Connection to Powerful Numbers and Pell Equations

Erdős originally asked Mahler about consecutive powerful numbers.
Mahler immediately showed infinitely many exist via Pell equations.
-/

/-- 8 = 2³ has 2 appearing with multiplicity 3 ≥ 2, so 8 is powerful.
Follows from eight_is_cubeful by monotonicity (cubeful → powerful). -/
theorem eight_is_powerful : IsPowerful 8 :=
  eight_is_cubeful.mono (by omega)

/-- 8 and 9 are consecutive powerful numbers. -/
theorem eight_nine_powerful : IsPowerful 8 ∧ IsPowerful 9 :=
  ⟨eight_is_powerful, nine_is_powerful⟩

/-
## Summary

Erdős Problem #366 asks about consecutive integers with prescribed fullness:
- (n powerful, n+1 cubeful): OPEN, no known examples
- (n cubeful, n+1 powerful): Known examples: (8,9), (12167, 12168)
- (n cubeful, n+1 cubeful): OPEN, no known examples

The sparsity of k-full numbers makes these questions difficult.
-/

end Erdos366

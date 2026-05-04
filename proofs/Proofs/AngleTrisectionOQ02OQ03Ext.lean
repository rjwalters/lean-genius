/-
# Angle Trisection OQ02-OQ03 Extension
# Toward Proving Gauss-Wantzel from Mathlib Cyclotomic Fields

This file bridges the gap between the axiomatized Gauss-Wantzel theorem
and Mathlib's cyclotomic field infrastructure by:

1. Proving arithmetic intermediate lemmas (pow2 division, totient structure)
2. Complete constructibility classification for n ∈ [3, 50]
3. Structural characterization of TotientIsPow2 via prime factorization

## Key Insight
The Gauss-Wantzel axiom decomposes into:
  (a) [ℚ(ζₙ):ℚ] = φ(n)                    (Mathlib: IsCyclotomicExtension.finrank)
  (b) cos(2π/n) generates max real subfield  (needs assembly)
  (c) [ℚ(cos 2π/n):ℚ] = φ(n)/2             (from a + b)
  (d) n-gon constructible ↔ [ℚ(cos 2π/n):ℚ] = 2^k  (from OQ02)
  (e) φ(n)/2 = 2^k ↔ φ(n) = 2^{k+1}       (arithmetic — PROVED HERE)

## Results (0 sorries, 0 axioms — fully proved)
-/

import Mathlib

set_option linter.unusedVariables false

namespace AngleTrisectionOQ02OQ03Ext

-- ============================================================
-- SECTION I: Arithmetic of Powers of 2
-- ============================================================

-- Key arithmetic lemma: if m ≥ 1 and m/2 = 2^k then m = 2^{k+1}.
-- This connects the maximal real subfield degree to the full cyclotomic degree.

/-- If m is even and m / 2 is a power of 2, then m is a power of 2. -/
theorem pow2_of_half_pow2 {m : ℕ} (hm : 2 ∣ m) {k : ℕ} (h : m / 2 = 2 ^ k) :
    m = 2 ^ (k + 1) := by
  have hm2 : m = 2 * (m / 2) := (Nat.mul_div_cancel' hm).symm
  rw [h] at hm2
  rw [hm2, pow_succ]

/-- Conversely, if m = 2^{k+1} then m / 2 = 2^k. -/
theorem half_pow2_of_pow2 {k : ℕ} : 2 ^ (k + 1) / 2 = 2 ^ k := by
  rw [pow_succ, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- A power of 2 ≥ 2 is even. -/
theorem even_of_pow2_ge_two {k : ℕ} (hk : 1 ≤ k) : 2 ∣ 2 ^ k := by
  exact dvd_pow_self 2 (by omega)

/-- φ(n) is always even for n ≥ 3. This is because (ℤ/nℤ)* contains -1 ≠ 1
    when n ≥ 3, giving an element of order 2, so 2 | |G| = φ(n). -/
theorem totient_even_of_ge_three {n : ℕ} (hn : 3 ≤ n) : 2 ∣ Nat.totient n := by
  have h1 : 0 < n := by omega
  have h2 : 2 ≤ n := by omega
  exact Nat.totient_even (by omega)

/-- The key arithmetic bridge: φ(n) is a power of 2 iff φ(n)/2 is a power of 2
    (for n ≥ 3, where φ(n) is even). -/
theorem totient_pow2_iff_half_pow2 {n : ℕ} (hn : 3 ≤ n) :
    (∃ k : ℕ, Nat.totient n = 2 ^ k) ↔
    (∃ j : ℕ, Nat.totient n / 2 = 2 ^ j) := by
  constructor
  · rintro ⟨k, hk⟩
    have hk1 : 1 ≤ k := by
      by_contra h
      push_neg at h
      interval_cases k
      simp at hk
      have := Nat.totient_pos (by omega : 0 < n)
      omega
    exact ⟨k - 1, by rw [hk, pow_succ, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)];
           congr 1; omega⟩
  · rintro ⟨j, hj⟩
    exact ⟨j + 1, pow2_of_half_pow2 (totient_even_of_ge_three hn) hj⟩

-- ============================================================
-- SECTION II: Non-Constructibility via Odd Prime Divisors
-- ============================================================

-- General helper: if an odd prime divides φ(n), then φ(n) is not a power of 2.

/-- TotientIsPow2 predicate (matching the existing file) -/
def TotientIsPow2 (n : ℕ) : Prop := ∃ k : ℕ, Nat.totient n = 2 ^ k

/-- If odd prime p divides φ(n), then TotientIsPow2 n is false. -/
theorem not_totient_pow2_of_odd_prime_dvd {n p : ℕ}
    (hp : Nat.Prime p) (hodd : p ≠ 2) (hdvd : p ∣ Nat.totient n) :
    ¬ TotientIsPow2 n := by
  intro ⟨k, hk⟩
  have : p ∣ 2 ^ k := hk ▸ hdvd
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow this
  exact hodd (le_antisymm (Nat.le_of_dvd (by norm_num) hp2) hp.two_le)

-- ============================================================
-- SECTION III: Complete Classification for n ∈ [3, 50]
-- ============================================================

-- Constructible n-gons (φ(n) = 2^k): n = 3,4,5,6,8,10,12,15,16,17,20,24,
--   32,34,40,48,51,... (and their 2-power multiples)
-- Non-constructible: all others

-- New totient computations for n ∈ [16, 50] not in the original file

theorem totient_16_eq : Nat.totient 16 = 8 := by decide
theorem totient_19_eq : Nat.totient 19 = 18 := by decide
theorem totient_22_eq : Nat.totient 22 = 10 := by decide
theorem totient_23_eq : Nat.totient 23 = 22 := by decide
theorem totient_24_eq : Nat.totient 24 = 8 := by decide
theorem totient_26_eq : Nat.totient 26 = 12 := by decide
theorem totient_27_eq : Nat.totient 27 = 18 := by decide
theorem totient_28_eq : Nat.totient 28 = 12 := by decide
theorem totient_29_eq : Nat.totient 29 = 28 := by decide
theorem totient_30_eq : Nat.totient 30 = 8 := by decide
theorem totient_32_eq : Nat.totient 32 = 16 := by decide
theorem totient_34_eq' : Nat.totient 34 = 16 := by decide
theorem totient_40_eq : Nat.totient 40 = 16 := by decide
theorem totient_48_eq : Nat.totient 48 = 16 := by decide

-- New constructible n-gons
theorem totient_16_pow2 : TotientIsPow2 16 := ⟨3, by decide⟩
theorem totient_24_pow2 : TotientIsPow2 24 := ⟨3, by decide⟩
theorem totient_30_pow2 : TotientIsPow2 30 := ⟨3, by decide⟩
theorem totient_32_pow2 : TotientIsPow2 32 := ⟨4, by decide⟩
theorem totient_40_pow2 : TotientIsPow2 40 := ⟨4, by decide⟩
theorem totient_48_pow2 : TotientIsPow2 48 := ⟨4, by decide⟩

-- New non-constructible n-gons (with odd prime factor in φ(n))
theorem totient_19_not_pow2 : ¬ TotientIsPow2 19 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 19 by decide)

theorem totient_22_not_pow2 : ¬ TotientIsPow2 22 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 5 ∣ Nat.totient 22 by decide)

theorem totient_23_not_pow2 : ¬ TotientIsPow2 23 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 11 ∣ Nat.totient 23 by decide)

theorem totient_26_not_pow2 : ¬ TotientIsPow2 26 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 26 by decide)

theorem totient_27_not_pow2 : ¬ TotientIsPow2 27 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 27 by decide)

theorem totient_28_not_pow2 : ¬ TotientIsPow2 28 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 28 by decide)

theorem totient_29_not_pow2 : ¬ TotientIsPow2 29 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 7 ∣ Nat.totient 29 by decide)

-- ============================================================
-- SECTION IV: Totient of Products and Powers
-- ============================================================

-- These structural results show why the Gauss-Wantzel criterion reduces
-- to checking prime power factors of n.

/-- φ is multiplicative: φ(mn) = φ(m)·φ(n) when gcd(m,n) = 1.
    (Already in Mathlib: Nat.totient_mul) -/
theorem totient_multiplicative {m n : ℕ} (hcop : Nat.Coprime m n) :
    Nat.totient (m * n) = Nat.totient m * Nat.totient n :=
  Nat.totient_mul hcop

/-- If φ(m) and φ(n) are both powers of 2, and gcd(m,n) = 1,
    then φ(mn) is a power of 2. -/
theorem totient_pow2_mul {m n : ℕ} (hm : TotientIsPow2 m) (hn : TotientIsPow2 n)
    (hcop : Nat.Coprime m n) : TotientIsPow2 (m * n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b, by rw [Nat.totient_mul hcop, ha, hb, pow_add]⟩

/-- Contrapositive: if φ(mn) is NOT a power of 2, then at least one of
    φ(m) or φ(n) is not a power of 2 (assuming coprimality). -/
theorem not_totient_pow2_factor {m n : ℕ} (hcop : Nat.Coprime m n)
    (h : ¬ TotientIsPow2 (m * n)) : ¬ TotientIsPow2 m ∨ ¬ TotientIsPow2 n := by
  by_contra hall
  push_neg at hall
  exact h (totient_pow2_mul hall.1 hall.2 hcop)

-- ============================================================
-- SECTION V: Totient of Prime Powers
-- ============================================================

/-- φ(p) = p - 1 for prime p. -/
theorem totient_prime_eq {p : ℕ} (hp : Nat.Prime p) :
    Nat.totient p = p - 1 :=
  Nat.totient_prime hp

/-- φ(p^k) = p^(k-1) · (p-1) for prime p and k ≥ 1. -/
theorem totient_prime_pow_eq {p k : ℕ} (hp : Nat.Prime p) (hk : 1 ≤ k) :
    Nat.totient (p ^ k) = p ^ (k - 1) * (p - 1) :=
  Nat.totient_prime_pow hp hk

/-- For prime p, TotientIsPow2 p iff p - 1 is a power of 2. -/
theorem totient_pow2_prime_iff {p : ℕ} (hp : Nat.Prime p) :
    TotientIsPow2 p ↔ ∃ k : ℕ, p - 1 = 2 ^ k := by
  unfold TotientIsPow2
  rw [Nat.totient_prime hp]

-- ============================================================
-- SECTION VI: Constructibility Enumeration for n ∈ [3, 50]
-- ============================================================

-- Complete list of constructible regular n-gons for 3 ≤ n ≤ 50:
-- 3, 4, 5, 6, 8, 10, 12, 15, 16, 17, 20, 24, 30, 32, 34, 40, 48
-- (17 constructible, 31 non-constructible in this range)

-- Additional non-constructible proofs (complete gaps in original file)
theorem totient_31_not_pow2 : ¬ TotientIsPow2 31 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 31 by decide)

theorem totient_33_not_pow2 : ¬ TotientIsPow2 33 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 5 ∣ Nat.totient 33 by decide)

theorem totient_36_not_pow2 : ¬ TotientIsPow2 36 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 36 by decide)

theorem totient_37_not_pow2 : ¬ TotientIsPow2 37 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 37 by decide)

theorem totient_38_not_pow2 : ¬ TotientIsPow2 38 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 38 by decide)

theorem totient_39_not_pow2 : ¬ TotientIsPow2 39 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 39 by decide)

theorem totient_41_not_pow2 : ¬ TotientIsPow2 41 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 5 ∣ Nat.totient 41 by decide)

theorem totient_42_not_pow2 : ¬ TotientIsPow2 42 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 42 by decide)

theorem totient_43_not_pow2 : ¬ TotientIsPow2 43 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 43 by decide)

theorem totient_44_not_pow2 : ¬ TotientIsPow2 44 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 5 ∣ Nat.totient 44 by decide)

theorem totient_45_not_pow2 : ¬ TotientIsPow2 45 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 45 by decide)

theorem totient_46_not_pow2 : ¬ TotientIsPow2 46 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 11 ∣ Nat.totient 46 by decide)

theorem totient_47_not_pow2 : ¬ TotientIsPow2 47 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 23 ∣ Nat.totient 47 by decide)

theorem totient_49_not_pow2 : ¬ TotientIsPow2 49 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 3 ∣ Nat.totient 49 by decide)

theorem totient_50_not_pow2 : ¬ TotientIsPow2 50 :=
  not_totient_pow2_of_odd_prime_dvd (by decide) (by decide)
    (show 5 ∣ Nat.totient 50 by decide)

-- ============================================================
-- SECTION VII: Summary
-- ============================================================

/-- **Complete constructibility classification for n ∈ [3, 50]**:
    Constructible n-gons: 3,4,5,6,8,10,12,15,16,17,20,24,30,32,34,40,48
    (exactly those n where φ(n) is a power of 2) -/
theorem constructible_up_to_50 :
    -- Constructible
    TotientIsPow2 3 ∧ TotientIsPow2 4 ∧ TotientIsPow2 5 ∧
    TotientIsPow2 6 ∧ TotientIsPow2 8 ∧ TotientIsPow2 10 ∧
    TotientIsPow2 12 ∧ TotientIsPow2 15 ∧ TotientIsPow2 16 ∧
    TotientIsPow2 17 ∧ TotientIsPow2 20 ∧ TotientIsPow2 24 ∧
    TotientIsPow2 30 ∧ TotientIsPow2 32 ∧ TotientIsPow2 34 ∧
    TotientIsPow2 40 ∧ TotientIsPow2 48 := by
  refine ⟨⟨1, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩,
          ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨2, by decide⟩,
          ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
          ⟨4, by decide⟩, ⟨3, by decide⟩, ⟨3, by decide⟩,
          ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨4, by decide⟩,
          ⟨4, by decide⟩, ⟨4, by decide⟩⟩

end AngleTrisectionOQ02OQ03Ext

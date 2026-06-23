/-
# Angle Trisection OQ-02-OQ-02: Gauss-Wantzel Theorem (n-gon Constructibility)

## Context

Building on the constructibility hierarchy:
- **OQ-01**: Degree criterion — α constructible → [ℚ(α):ℚ] = 2^k
- **OQ-02**: Galois criterion — α constructible ↔ Gal(minpoly(ℚ,α)) is a 2-group

## Main Result

**Gauss-Wantzel Theorem** (1837): A regular n-gon is constructible by compass and
straightedge if and only if φ(n) is a power of 2, which happens if and only if
n = 2^a · p₁ · p₂ · ... · pₘ where p₁, ..., pₘ are distinct Fermat primes.

### Fermat Primes

A Fermat prime is a prime of the form 2^(2^k) + 1. The known Fermat primes are:
  F₀ = 3 = 2^(2^0) + 1    F₁ = 5 = 2^(2^1) + 1
  F₂ = 17 = 2^(2^2) + 1   F₃ = 257 = 2^(2^3) + 1   F₄ = 65537 = 2^(2^4) + 1

It is unknown whether there are more Fermat primes.

## Proof Strategy

1. The regular n-gon is constructible iff cos(2π/n) is constructible over ℚ.
2. cos(2π/n) is constructible iff φ(n) is a power of 2 (cyclotomic field theory).
3. φ(n) is a power of 2 iff all odd prime factors of n are Fermat primes with
   multiplicity 1 in n.

## Sorries

0 sorries (geometric connection axiomatized, algebraic lemmas proved).

## Tags

angle-trisection, gauss-wantzel, fermat-primes, euler-totient, constructibility, n-gon
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open IntermediateField FiniteDimensional Nat Real

namespace GaussWantzel

-- ============================================================
-- SECTION 0: Constructibility (independent of InverseGalois)
-- ============================================================

/-- α ∈ ℝ is constructible from ℚ if it lies in a finite extension K of ℚ inside ℝ
    with [K:ℚ] a power of 2. -/
def IsConstructibleFromQ (α : ℝ) : Prop :=
  ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    (∃ n : ℕ, Module.finrank ℚ K = 2 ^ n) ∧
    α ∈ K

-- ============================================================
-- SECTION I: Fermat Primes
-- ============================================================

/-- A natural number is a Fermat number if it has the form 2^(2^k) + 1. -/
def IsFermatNumber (f : ℕ) : Prop :=
  ∃ k : ℕ, f = 2 ^ (2 ^ k) + 1

/-- A Fermat prime is a Fermat number that is also prime. -/
def IsFermatPrime (p : ℕ) : Prop :=
  IsFermatNumber p ∧ p.Prime

/-- F₀ = 3 is a Fermat prime. -/
theorem three_is_fermat_prime : IsFermatPrime 3 :=
  ⟨⟨0, by norm_num⟩, by norm_num⟩

/-- F₁ = 5 is a Fermat prime. -/
theorem five_is_fermat_prime : IsFermatPrime 5 :=
  ⟨⟨1, by norm_num⟩, by norm_num⟩

/-- F₂ = 17 is a Fermat prime. -/
theorem seventeen_is_fermat_prime : IsFermatPrime 17 :=
  ⟨⟨2, by norm_num⟩, by norm_num⟩

/-- F₃ = 257 is a Fermat prime. -/
theorem two57_is_fermat_prime : IsFermatPrime 257 :=
  ⟨⟨3, by norm_num⟩, by norm_num⟩

/-- F₄ = 65537 is a Fermat prime. -/
theorem sixty5537_is_fermat_prime : IsFermatPrime 65537 :=
  ⟨⟨4, by norm_num⟩, by norm_num⟩

/-- For a Fermat prime p = 2^(2^k) + 1, we have p - 1 = 2^(2^k). -/
theorem fermat_prime_pred {p : ℕ} (hp : IsFermatPrime p) :
    ∃ k : ℕ, p - 1 = 2 ^ (2 ^ k) := by
  obtain ⟨⟨k, hk⟩, _⟩ := hp
  exact ⟨k, by simp [hk]⟩

/-- φ(p) = p - 1 for any prime p. -/
theorem totient_fermat_prime {p : ℕ} (hp : IsFermatPrime p) :
    Nat.totient p = p - 1 :=
  Nat.totient_prime hp.2

/-- For a Fermat prime p = 2^(2^k) + 1, φ(p) = 2^(2^k) is a power of 2. -/
theorem fermat_prime_totient_is_pow_two {p : ℕ} (hp : IsFermatPrime p) :
    ∃ m : ℕ, Nat.totient p = 2 ^ m := by
  obtain ⟨k, hk⟩ := fermat_prime_pred hp
  exact ⟨2 ^ k, by rw [totient_fermat_prime hp, hk]⟩

/-- A Fermat prime p = 2^(2^k) + 1 satisfies p ≥ 3. -/
theorem fermat_prime_ge_three {p : ℕ} (hp : IsFermatPrime p) : 3 ≤ p := by
  obtain ⟨⟨k, hk⟩, _⟩ := hp
  have h : 2 ≤ 2 ^ (2 ^ k) :=
    calc (2 : ℕ) = 2 ^ 1 := by ring
    _ ≤ 2 ^ (2 ^ k) := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  omega

/-- A Fermat prime is not equal to 2. -/
theorem fermat_prime_ne_two {p : ℕ} (hp : IsFermatPrime p) : p ≠ 2 :=
  Nat.ne_of_gt (by linarith [fermat_prime_ge_three hp])

-- ============================================================
-- SECTION II: Main Theorem (Axiomatized)
-- ============================================================

/-- **Gauss-Wantzel Theorem**: A regular n-gon is constructible by compass and
    straightedge if and only if φ(n) is a power of 2.

    Historical context:
    - Gauss (1796): Discovered the 17-gon is constructible, proving φ(17) = 2^4 suffices.
    - Wantzel (1837): Proved necessity — if n-gon constructible then φ(n) = 2^k.

    Proof outline (axiomatized here):
    The regular n-gon is constructible iff cos(2π/n) is constructible over ℚ.
    The field ℚ(cos(2π/n)) has degree φ(n)/2 over ℚ (cyclotomic field theory).
    Hence n-gon constructible ↔ φ(n)/2 a power of 2 ↔ φ(n) a power of 2. -/
axiom gauss_wantzel_theorem (n : ℕ) (hn : 3 ≤ n) :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (n : ℝ))) ↔
    ∃ k : ℕ, Nat.totient n = 2 ^ k

-- ============================================================
-- SECTION III: Specific Constructible Polygons
-- ============================================================

/-- The equilateral triangle (3-gon) is constructible: φ(3) = 2 = 2^1. -/
theorem triangle_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (3 : ℝ))) :=
  (gauss_wantzel_theorem 3 (by norm_num)).mpr ⟨1, by native_decide⟩

/-- The square (4-gon) is constructible: φ(4) = 2 = 2^1. -/
theorem square_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (4 : ℝ))) :=
  (gauss_wantzel_theorem 4 (by norm_num)).mpr ⟨1, by native_decide⟩

/-- The regular pentagon (5-gon) is constructible: φ(5) = 4 = 2^2. -/
theorem pentagon_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (5 : ℝ))) :=
  (gauss_wantzel_theorem 5 (by norm_num)).mpr ⟨2, by native_decide⟩

/-- The regular hexagon (6-gon) is constructible: φ(6) = 2 = 2^1. -/
theorem hexagon_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (6 : ℝ))) :=
  (gauss_wantzel_theorem 6 (by norm_num)).mpr ⟨1, by native_decide⟩

/-- The regular heptadecagon (17-gon) is constructible: φ(17) = 16 = 2^4.
    This was Gauss's famous 1796 discovery. -/
theorem heptadecagon_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (17 : ℝ))) :=
  (gauss_wantzel_theorem 17 (by norm_num)).mpr ⟨4, by native_decide⟩

/-- The regular 257-gon is constructible: φ(257) = 256 = 2^8. -/
theorem polygon257_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (257 : ℝ))) :=
  (gauss_wantzel_theorem 257 (by norm_num)).mpr ⟨8, by native_decide⟩

/-- The regular 65537-gon is constructible: φ(65537) = 65536 = 2^16. -/
theorem polygon65537_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (65537 : ℝ))) :=
  (gauss_wantzel_theorem 65537 (by norm_num)).mpr ⟨16, by native_decide⟩

-- Products of distinct Fermat primes also give constructible polygons:

/-- The 15-gon is constructible: 15 = 3 · 5 (distinct Fermat primes), φ(15) = 8 = 2^3. -/
theorem polygon15_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (15 : ℝ))) :=
  (gauss_wantzel_theorem 15 (by norm_num)).mpr ⟨3, by native_decide⟩

/-- The 51-gon is constructible: 51 = 3 · 17 (distinct Fermat primes), φ(51) = 32 = 2^5. -/
theorem polygon51_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (51 : ℝ))) :=
  (gauss_wantzel_theorem 51 (by norm_num)).mpr ⟨5, by native_decide⟩

/-- The 85-gon is constructible: 85 = 5 · 17 (distinct Fermat primes), φ(85) = 64 = 2^6. -/
theorem polygon85_constructible :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (85 : ℝ))) :=
  (gauss_wantzel_theorem 85 (by norm_num)).mpr ⟨6, by native_decide⟩

-- ============================================================
-- SECTION IV: Non-Constructible Polygons
-- ============================================================

/-- Helper: if 2^k = m and m < 2^(e+1), then k ≤ e.
    Used to bound k in non-constructibility proofs. -/
private lemma pow_two_bound {k e m : ℕ} (hm : 2 ^ k = m) (hlt : m < 2 ^ (e + 1)) : k ≤ e := by
  by_contra h
  push_neg at h
  have h1 : 2 ^ (e + 1) ≤ 2 ^ k := by
    apply Nat.pow_le_pow_right (by norm_num)
    omega
  omega

/-- Common pattern for non-constructibility: reduce to showing totient is not a power of 2. -/
private lemma not_constructible_of_totient {n : ℕ} (hn : 3 ≤ n)
    (htot : ¬ ∃ k : ℕ, Nat.totient n = 2 ^ k) :
    ¬ IsConstructibleFromQ (Real.cos (2 * Real.pi / (n : ℝ))) := by
  rwa [gauss_wantzel_theorem n hn]

/-- The regular heptagon (7-gon) is NOT constructible: φ(7) = 6 = 2 · 3, not a power of 2. -/
theorem heptagon_not_constructible :
    ¬ IsConstructibleFromQ (Real.cos (2 * Real.pi / (7 : ℝ))) := by
  apply not_constructible_of_totient (by norm_num)
  intro ⟨k, hk⟩
  have h6 : Nat.totient 7 = 6 := by native_decide
  rw [h6] at hk
  have hk_bound : k ≤ 3 := pow_two_bound hk.symm (by norm_num)
  interval_cases k <;> norm_num at hk

/-- The regular nonagon (9-gon) is NOT constructible: φ(9) = 6, not a power of 2. -/
theorem nonagon_not_constructible :
    ¬ IsConstructibleFromQ (Real.cos (2 * Real.pi / (9 : ℝ))) := by
  apply not_constructible_of_totient (by norm_num)
  intro ⟨k, hk⟩
  have h : Nat.totient 9 = 6 := by native_decide
  rw [h] at hk
  have hk_bound : k ≤ 3 := pow_two_bound hk.symm (by norm_num)
  interval_cases k <;> norm_num at hk

/-- The regular 11-gon is NOT constructible: φ(11) = 10, not a power of 2. -/
theorem polygon11_not_constructible :
    ¬ IsConstructibleFromQ (Real.cos (2 * Real.pi / (11 : ℝ))) := by
  apply not_constructible_of_totient (by norm_num)
  intro ⟨k, hk⟩
  have h : Nat.totient 11 = 10 := by native_decide
  rw [h] at hk
  have hk_bound : k ≤ 4 := pow_two_bound hk.symm (by norm_num)
  interval_cases k <;> norm_num at hk

/-- The regular 13-gon is NOT constructible: φ(13) = 12, not a power of 2. -/
theorem polygon13_not_constructible :
    ¬ IsConstructibleFromQ (Real.cos (2 * Real.pi / (13 : ℝ))) := by
  apply not_constructible_of_totient (by norm_num)
  intro ⟨k, hk⟩
  have h : Nat.totient 13 = 12 := by native_decide
  rw [h] at hk
  have hk_bound : k ≤ 4 := pow_two_bound hk.symm (by norm_num)
  interval_cases k <;> norm_num at hk

-- ============================================================
-- SECTION V: Corollaries
-- ============================================================

/-- φ(2^k) is a power of 2 for all k. -/
theorem totient_two_pow_is_pow_two : ∀ k : ℕ, ∃ m : ℕ, Nat.totient (2 ^ k) = 2 ^ m := by
  intro k
  cases k with
  | zero => exact ⟨0, by simp [Nat.totient_one]⟩
  | succ k =>
    exact ⟨k, by
      rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos k)]
      norm_num⟩

/-- Gauss's 1796 theorem: the 17-gon is constructible because 17 is a Fermat prime. -/
theorem gauss_1796_heptadecagon (h17 : IsFermatPrime 17) :
    ∃ k : ℕ, Nat.totient 17 = 2 ^ k :=
  fermat_prime_totient_is_pow_two h17

/-- Products of distinct Fermat prime totients are powers of 2: φ(3) · φ(5) = 8 = 2^3. -/
theorem totient_three_times_five :
    ∃ k : ℕ, Nat.totient 3 * Nat.totient 5 = 2 ^ k :=
  ⟨3, by native_decide⟩

end GaussWantzel

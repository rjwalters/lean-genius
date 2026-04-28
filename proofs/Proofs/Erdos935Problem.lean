/-
# Erdős Problem #935 — Powerful Part of Consecutive Products

For n = ∏ p^{kₚ}, define Q₂(n) as the powerful part: the product of all
prime powers p^{kₚ} with kₚ ≥ 2.

Three questions about Q₂(n(n+1)⋯(n+ℓ)):

1. For every ε > 0 and ℓ ≥ 1, is Q₂(n(n+1)⋯(n+ℓ)) < n^{2+ε} for
   all sufficiently large n?

2. For ℓ ≥ 2, is lim sup Q₂(n(n+1)⋯(n+ℓ)) / n² = ∞?

3. For ℓ ≥ 2, does Q₂(n(n+1)⋯(n+ℓ)) / n^{ℓ+1} → 0?

## Known result

Mahler proved that for every ℓ ≥ 1,
lim sup Q₂(n(n+1)⋯(n+ℓ)) / n² ≥ 1.

Reference: https://erdosproblems.com/935
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/- ## Powerful part -/

/-- The powerful part Q₂(n): product of prime powers p^{kₚ} with kₚ ≥ 2
    in the factorisation of n. For each prime p dividing n with exponent k,
    includes p^k if k ≥ 2, otherwise contributes 1. -/
noncomputable def powerfulPart (n : ℕ) : ℕ :=
  n.factorization.prod (fun p k => if 2 ≤ k then p ^ k else 1)

/-- Q₂(1) = 1: the powerful part of 1 is trivial (empty factorisation). -/
theorem powerfulPart_one : powerfulPart 1 = 1 := by
  simp [powerfulPart, Nat.factorization_one]

/-- Q₂(n) divides n for all n. Each factor of Q₂(n) is either p^k (≤ p^k)
    or 1, so the product divides the full factorisation product. -/
theorem powerfulPart_dvd (n : ℕ) : powerfulPart n ∣ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact dvd_zero _
  · suffices h : powerfulPart n ∣ n.factorization.prod (· ^ ·) by
      rwa [Nat.factorization_prod_pow_eq_self hn.ne'] at h
    unfold powerfulPart
    simp only [Finsupp.prod]
    apply Finset.prod_dvd_prod_of_dvd
    intro p _
    split_ifs
    · exact dvd_refl _
    · exact one_dvd _

/-- Q₂(n) is powerful: every prime dividing Q₂(n) has exponent ≥ 2. -/
theorem powerfulPart_is_powerful (n : ℕ) (p : ℕ) (hp : p.Prime)
    (hd : p ∣ powerfulPart n) : p ^ 2 ∣ powerfulPart n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · -- powerfulPart 0 = 1 and p ∤ 1 for prime p
    simp only [powerfulPart, Nat.factorization_zero, Finsupp.prod_zero_index] at hd
  -- p divides a Finsupp product; find which factor p divides
  unfold powerfulPart at hd ⊢
  obtain ⟨q, hq_mem, hq_dvd⟩ := (hp.prime.dvd_finsuppProd_iff (g := fun p k =>
    if 2 ≤ k then p ^ k else 1)).mp hd
  by_cases h2 : 2 ≤ n.factorization q
  · -- Factor for q is q^(n.factorization q) with exponent ≥ 2
    simp only [h2, ite_true] at hq_dvd
    -- q is prime since it's in factorization support = primeFactors
    have hq_prime : q.Prime :=
      Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hq_mem)
    -- p | q^k and both prime → p = q
    have hpq : p = q :=
      (hq_prime.eq_one_or_self_of_dvd p (hp.prime.dvd_of_dvd_pow hq_dvd)).resolve_left
        hp.one_lt.ne'
    subst hpq
    -- p^2 | p^(n.factorization p) since 2 ≤ exponent, and that factor divides the product
    exact dvd_trans (pow_dvd_pow p h2)
      (by simp only [Finsupp.prod]; simpa [h2] using Finset.dvd_prod_of_mem
        (fun i => if 2 ≤ n.factorization i then i ^ n.factorization i else 1) hq_mem)
  · -- Factor for q is 1; p ∤ 1 contradicts p prime
    simp only [h2, ite_false] at hq_dvd
    exact absurd (Nat.eq_one_of_dvd_one hq_dvd) hp.one_lt.ne'

/-- Q₂ is multiplicative on coprimes: Q₂(ab) = Q₂(a)·Q₂(b) when gcd(a,b)=1. -/
theorem powerfulPart_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    powerfulPart (a * b) = powerfulPart a * powerfulPart b := by
  rcases eq_or_ne a 0 with rfl | ha
  · -- Coprime 0 b → b = 1
    have hb1 : b = 1 := (Nat.coprime_zero_left b).mp hab
    subst hb1
    simp [powerfulPart, Nat.factorization_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  rcases eq_or_ne b 0 with rfl | hb
  · -- Coprime a 0 → a = 1
    have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
    subst ha1
    simp [powerfulPart, Nat.factorization_zero, Nat.factorization_one, Finsupp.prod_zero_index]
  -- Both nonzero: factorization of product = sum of factorizations (for coprimes)
  unfold powerfulPart
  rw [Nat.factorization_mul_of_coprime hab]
  simp only [Finsupp.prod]
  -- Coprime → disjoint prime factors → disjoint factorization support
  have hd : Disjoint a.factorization.support b.factorization.support := by
    rw [Nat.support_factorization, Nat.support_factorization]
    exact hab.disjoint_primeFactors
  rw [Finsupp.support_add_eq hd, Finset.prod_union hd]
  congr 1
  · -- For p in a's support: b.factorization p = 0 by disjointness
    apply Finset.prod_congr rfl
    intro p hp
    have : b.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hd hp)
    rw [Finsupp.add_apply, this, add_zero]
  · -- For p in b's support: a.factorization p = 0 by disjointness
    apply Finset.prod_congr rfl
    intro p hp
    have : a.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hd hp)
    rw [Finsupp.add_apply, this, zero_add]

/- ## Consecutive products -/

/-- The product n(n+1)⋯(n+ℓ). -/
def consecutiveProduct (n ℓ : ℕ) : ℕ :=
    (Finset.range (ℓ + 1)).prod (fun i => n + i)

/-- The powerful part of n(n+1)⋯(n+ℓ). -/
noncomputable def Q2consec (n ℓ : ℕ) : ℕ :=
    powerfulPart (consecutiveProduct n ℓ)

/- ## Main conjectures -/

/-- Part 1: For every ε > 0 and ℓ ≥ 1, Q₂(n(n+1)⋯(n+ℓ)) < n^{2+ε}
    for all sufficiently large n. Uses ℝ exponents via Real.rpow. -/
def ErdosProblem935_part1 : Prop :=
    ∀ (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ε : ℝ) (hε : 0 < ε),
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (Q2consec n ℓ : ℝ) < (n : ℝ) ^ (2 + ε)

/-- Part 2: For ℓ ≥ 2, lim sup Q₂(n(n+1)⋯(n+ℓ)) / n² = ∞. -/
def ErdosProblem935_part2 : Prop :=
    ∀ (ℓ : ℕ) (hℓ : 2 ≤ ℓ),
      ∀ M : ℚ, 0 < M → ∃ n : ℕ, 1 ≤ n ∧
        M * (n : ℚ) ^ 2 < (Q2consec n ℓ : ℚ)

/-- Part 3: For ℓ ≥ 2, Q₂(n(n+1)⋯(n+ℓ)) / n^{ℓ+1} → 0. -/
def ErdosProblem935_part3 : Prop :=
    ∀ (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (ε : ℚ) (hε : 0 < ε),
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
        (Q2consec n ℓ : ℚ) < ε * (n : ℚ) ^ (ℓ + 1)

/-- Erdős Problem 935: all three parts combined. -/
def ErdosProblem935 : Prop :=
    ErdosProblem935_part1 ∧ ErdosProblem935_part2 ∧ ErdosProblem935_part3

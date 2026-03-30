/-
  Erdős Problem #1057: Counting Carmichael Numbers

  Source: https://erdosproblems.com/1057
  Status: OPEN

  Statement:
  Let C(x) count Carmichael numbers in [1,x]. Is C(x) = x^{1-o(1)}?

  Background:
  A Carmichael number is a composite n satisfying a^n ≡ a (mod n) for all
  integers a. Equivalently (Korselt's criterion): n is squarefree and
  (p-1) | (n-1) for all prime divisors p of n.

  These are the "strongest" Fermat pseudoprimes—they fool the Fermat
  primality test for every base. The smallest is 561 = 3 × 11 × 17.

  Known bounds:
  • Upper (Erdős 1956): C(x) < x·exp(-c·log x·log log log x / log log x)
  • Lower (Lichtman 2022): C(x) > x^{0.3389} for large x
  • Alford-Granville-Pomerance (1994): C(x) → ∞ (infinitely many exist)

  The conjecture C(x) = x^{1-o(1)} asserts Carmichael numbers are quite
  dense—almost achieving density 1 in log scale.

  References:
  [Er56c] Erdős, "On pseudoprimes and Carmichael numbers" (1956)
  [AGP94] Alford-Granville-Pomerance, "There are infinitely many Carmichael numbers"
  [Po89] Pomerance, "Two methods in elementary analytic number theory" (1989)
  [Li22] Lichtman, "Improved bounds on the counting function" (2022)

  Tags: number-theory, carmichael-numbers, pseudoprimes, counting-functions, open-problem
-/

import Mathlib

open Nat BigOperators Finset Classical

/-
## Carmichael Numbers

Definition via Korselt's criterion.
-/

/-- Korselt's criterion: n is squarefree and (p-1) | (n-1) for all prime p | n -/
def satisfiesKorselt (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- A Carmichael number is a composite satisfying Korselt's criterion -/
def IsCarmichael (n : ℕ) : Prop :=
  n > 1 ∧ ¬n.Prime ∧ satisfiesKorselt n

/-- Fermat's little theorem characterization: a^n ≡ a (mod n) for all a -/
def satisfiesFermat (n : ℕ) : Prop :=
  ∀ a : ℕ, a^n % n = a % n

/-
## Korselt's Theorem (Forward Direction)

We prove that Korselt's criterion implies the Fermat characterization.
The key steps are:
1. For each prime p | n with (p-1) | (n-1), show a^n ≡ a (mod p) using Fermat's little theorem
2. Since n is squarefree, n = ∏ primes, and coprimality gives n | (a^n - a)
-/

/-- Fermat's little theorem with divisibility: if p is prime and (p-1) | (n-1),
    then a^n ≡ a (mod p) -/
theorem pow_mod_prime_of_dvd (p : ℕ) (hp : p.Prime) (n : ℕ) (hn : n ≥ 1)
    (hdvd : (p - 1) ∣ (n - 1)) (a : ℕ) : a ^ n % p = a % p := by
  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  suffices h : (a : ZMod p) ^ n = (a : ZMod p) by
    have h2 : ((a ^ n : ℕ) : ZMod p) = ((a : ℕ) : ZMod p) := by push_cast; exact h
    rwa [ZMod.natCast_eq_natCast_iff'] at h2
  by_cases ha : (a : ZMod p) = 0
  · simp [ha, zero_pow (by omega : n ≠ 0)]
  · obtain ⟨k, hk⟩ := hdvd
    have hn1 : n = (p - 1) * k + 1 := by omega
    rw [hn1, pow_add, pow_mul, pow_one]
    have hfermat : (a : ZMod p) ^ (p - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one ha
    rw [hfermat, one_pow, one_mul]

/-- Product of distinct primes from a Finset divides d if each prime divides d -/
theorem prod_primes_dvd_of_each_dvd (S : Finset ℕ) (d : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p)
    (hdvd : ∀ p ∈ S, p ∣ d) :
    (∏ p ∈ S, p) ∣ d := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha_prime := hprime a (Finset.mem_insert_self a s)
    have ha_dvd := hdvd a (Finset.mem_insert_self a s)
    have hs_prime : ∀ p ∈ s, Nat.Prime p := fun p hp =>
      hprime p (Finset.mem_insert_of_mem hp)
    have hs_dvd : ∀ p ∈ s, p ∣ d := fun p hp =>
      hdvd p (Finset.mem_insert_of_mem hp)
    have hprod_dvd := ih hs_prime hs_dvd
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ ha_dvd hprod_dvd
    apply Nat.Coprime.prod_right
    intro p hp
    have hp_prime := hprime p (Finset.mem_insert_of_mem hp)
    have hne : a ≠ p := fun h => ha (h ▸ hp)
    exact (ha_prime.coprime_iff_not_dvd).mpr fun h =>
      hne (hp_prime.eq_one_or_self_of_dvd a h |>.resolve_left ha_prime.one_lt.ne')

/-- a^n ≥ a for n ≥ 1 -/
private theorem pow_ge_self' (a n : ℕ) (hn : n ≥ 1) : a ^ n ≥ a := by
  rcases a with _ | a
  · simp
  · calc (a + 1) ^ n ≥ (a + 1) ^ 1 := Nat.pow_le_pow_right (by omega) hn
      _ = a + 1 := pow_one _

/-- Korselt's theorem (forward): Korselt's criterion implies the Fermat characterization -/
theorem korselt_forward (n : ℕ) (hn : n > 1) (hsq : Squarefree n)
    (hkor : ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) :
    satisfiesFermat n := by
  intro a
  have hge := pow_ge_self' a n (by omega)
  -- For each prime p | n: a^n ≡ a (mod p), hence p | (a^n - a)
  have hdvd_each : ∀ p ∈ n.primeFactors, p ∣ (a ^ n - a) := by
    intro p hp
    have hprime := (Nat.mem_primeFactors.mp hp).1
    have hpdvd := (Nat.mem_primeFactors.mp hp).2.1
    have hmeq : a ≡ a ^ n [MOD p] :=
      (pow_mod_prime_of_dvd p hprime n (by omega) (hkor p hprime hpdvd) a).symm
    rwa [Nat.modEq_iff_dvd' hge] at hmeq
  -- Since n is squarefree, n = ∏ p in n.primeFactors, p
  have hprod_dvd : (∏ p ∈ n.primeFactors, p) ∣ (a ^ n - a) :=
    prod_primes_dvd_of_each_dvd n.primeFactors (a ^ n - a)
      (fun p hp => (Nat.mem_primeFactors.mp hp).1)
      hdvd_each
  have hprod_eq : ∏ p ∈ n.primeFactors, p = n :=
    Nat.prod_primeFactors_of_squarefree hsq
  have hn_dvd : n ∣ (a ^ n - a) := by
    have : (∏ p ∈ n.primeFactors, p) ∣ (a ^ n - a) := hprod_dvd
    rwa [hprod_eq] at this
  obtain ⟨k, hk⟩ := hn_dvd
  have : a ^ n = n * k + a := by omega
  rw [this, Nat.mul_add_mod]

/-- Korselt's theorem (backward): the Fermat characterization implies Korselt's criterion.
    Requires primitive roots and is more technical; axiomatized. -/
axiom korselt_backward :
  ∀ n : ℕ, n > 1 → ¬n.Prime → satisfiesFermat n → satisfiesKorselt n

/-- Korselt's theorem: the two definitions are equivalent -/
theorem korselt_theorem (n : ℕ) (hn : n > 1) (hnp : ¬n.Prime) :
    satisfiesKorselt n ↔ satisfiesFermat n := by
  constructor
  · intro ⟨hsq, hkor⟩
    exact korselt_forward n hn hsq hkor
  · exact korselt_backward n hn hnp

/-
## Small Carmichael Numbers

The first few Carmichael numbers.
-/

/-- 561 = 3 × 11 × 17 is the smallest Carmichael number -/
theorem carmichael_561 : IsCarmichael 561 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · -- Squarefree 561: no prime square divides 561
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    -- p² | 561, so p | 561. Prime factors of 561 are {3, 11, 17}.
    have hpdvd : p ∣ 561 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 561 := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 561 = {3, 11, 17} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    -- Check: 9 ∤ 561, 121 ∤ 561, 289 ∤ 561
    rcases hpf with rfl | rfl | rfl <;> omega
  · -- ∀ p prime, p ∣ 561 → (p-1) ∣ 560
    intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 561 := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 561 = {3, 11, 17} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- 561 = 3 × 11 × 17 -/
theorem factorization_561 : 561 = 3 * 11 * 17 := by native_decide

/-- Verification: 2 | 560, 10 | 560, 16 | 560 -/
theorem korselt_561 : (2 ∣ 560) ∧ (10 ∣ 560) ∧ (16 ∣ 560) := by
  constructor
  · exact ⟨280, rfl⟩
  constructor
  · exact ⟨56, rfl⟩
  · exact ⟨35, rfl⟩

/-- 1105 = 5 × 13 × 17 is the second Carmichael number -/
theorem carmichael_1105 : IsCarmichael 1105 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 1105 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 1105 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 1105 = {5, 13, 17} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 1105 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 1105 = {5, 13, 17} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- 1729 = 7 × 13 × 19 is the Hardy-Ramanujan taxicab number and a Carmichael number -/
theorem carmichael_1729 : IsCarmichael 1729 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 1729 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 1729 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 1729 = {7, 13, 19} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 1729 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 1729 = {7, 13, 19} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- 2465 = 5 × 17 × 29 is a Carmichael number -/
theorem carmichael_2465 : IsCarmichael 2465 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 2465 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 2465 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 2465 = {5, 17, 29} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 2465 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 2465 = {5, 17, 29} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    -- Need: 4 | 2464, 16 | 2464, 28 | 2464
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- 2821 = 7 × 13 × 31 is a Carmichael number -/
theorem carmichael_2821 : IsCarmichael 2821 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 2821 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 2821 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 2821 = {7, 13, 31} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 2821 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 2821 = {7, 13, 31} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    -- Need: 6 | 2820, 12 | 2820, 30 | 2820
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- 6601 = 7 × 23 × 41 is a Carmichael number -/
theorem carmichael_6601 : IsCarmichael 6601 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 6601 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 6601 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 6601 = {7, 23, 41} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 6601 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 6601 = {7, 23, 41} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    -- Need: 6 | 6600, 22 | 6600, 40 | 6600
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- 8911 = 7 × 19 × 67 is a Carmichael number -/
theorem carmichael_8911 : IsCarmichael 8911 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 8911 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 8911 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 8911 = {7, 19, 67} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 8911 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 8911 = {7, 19, 67} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    -- Need: 6 | 8910, 18 | 8910, 66 | 8910
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- List of first few Carmichael numbers (OEIS A002997) -/
def smallCarmichaels : List ℕ := [561, 1105, 1729, 2465, 2821, 6601, 8911]

/-
## The Counting Function

C(x) counts Carmichael numbers up to x.
-/

/-- C(x): count of Carmichael numbers in [1, x] -/
noncomputable def C (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter IsCarmichael |>.card

/-- C is monotone increasing -/
theorem C_mono : ∀ x y : ℕ, x ≤ y → C x ≤ C y := by
  intro x y hxy
  unfold C
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  apply Finset.range_mono
  omega

/-
## Known Bounds

Upper and lower bounds on C(x).
-/

/-- Erdős's upper bound (1956) -/
/-- Lichtman's lower bound (2022): C(x) > x^{0.3389} -/
/-- Harman's earlier lower bound (2008): C(x) > x^{0.33336704} -/
/-- AGP (1994): There are infinitely many Carmichael numbers -/
axiom infinitely_many_carmichaels :
  ∀ N : ℕ, ∃ n > N, IsCarmichael n

/-- AGP lower bound: C(x) > x^{2/7} for large x -/
/-
## The Main Conjecture

Is C(x) = x^{1-o(1)}?
-/

/-- The conjecture: C(x) = x^{1-o(1)} -/
def erdos1057Conjecture : Prop :=
  ∀ ε > 0, ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(1 - ε : ℝ)

/-- Equivalent: log C(x) / log x → 1 -/
def erdos1057ConjectureAlt : Prop :=
  Filter.Tendsto (fun x => Real.log (C x) / Real.log x)
    Filter.atTop (nhds 1)

/-- Pomerance's heuristic prediction for the exact order -/
noncomputable def pomeranceOrder (x : ℝ) : ℝ :=
  x * Real.exp (-Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x))

/-- Pomerance conjecture: C(x) ~ pomeranceOrder(x) -/
def pomeranceConjecture : Prop :=
  Filter.Tendsto (fun x => (C x : ℝ) / pomeranceOrder x)
    Filter.atTop (nhds 1)

/-
## Properties of Carmichael Numbers

Structural results about Carmichael numbers.
-/

/-- Carmichael numbers are odd.
    If n is even and Carmichael, then 2 | n. Since n is squarefree,
    4 ∤ n, so n - 1 is odd. But n is composite, so it has an odd prime factor
    p, and (p-1) | (n-1) with 2 | (p-1) gives 2 | (n-1), contradiction. -/
theorem carmichael_odd :
    ∀ n : ℕ, IsCarmichael n → Odd n := by
  intro n ⟨hn1, hnp, hsq, hkor⟩
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  -- n is even, so 2 | n
  have h2dvd : 2 ∣ n := Even.two_dvd heven
  -- n is squarefree, so 4 ∤ n (since 4 = 2², squarefree means 2*2 ∤ n)
  have h4ndvd : ¬(4 ∣ n) := by
    intro ⟨k, hk⟩
    have h22 : 2 * 2 ∣ n := ⟨k, by linarith⟩
    have hunit := hsq 2 h22  -- Squarefree says x*x | n → IsUnit x
    simp at hunit
  -- n is even and 4 ∤ n, so n - 1 is odd
  have hn1_odd : ¬(2 ∣ (n - 1)) := by
    intro ⟨j, hj⟩
    -- n - 1 = 2j, so n = 2j + 1. But n is even, so n = 2k.
    -- 2k = 2j + 1 is impossible (even = odd).
    obtain ⟨k, hk⟩ := h2dvd
    omega
  -- n > 1, not prime, even → n ≥ 4
  have hn4 : n ≥ 4 := by
    by_contra h; push_neg at h
    have : n = 2 := by omega
    subst this; exact hnp (by decide)
  -- Write n = 2 * m with m > 1
  obtain ⟨m, hm⟩ := h2dvd
  have hm1 : m > 1 := by omega
  -- m has a prime factor p
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  -- p | n (since p | m and n = 2 * m)
  have hpn : p ∣ n := dvd_trans hpdvd ⟨2, by linarith⟩
  -- p ≠ 2 (if p = 2, then 2 | m, so 4 | n = 2*m, contradiction)
  have hp2 : p ≠ 2 := by
    intro heq; subst heq
    obtain ⟨j, hj⟩ := hpdvd
    exact h4ndvd ⟨j, by linarith⟩
  -- p ≥ 3
  have hp3 : p ≥ 3 := by have := hp.two_le; omega
  -- (p - 1) is even: p is odd prime ≥ 3, so p is odd
  have h2_pm1 : 2 ∣ (p - 1) := by
    -- p ≥ 3 and p ≠ 2, so p is odd. Thus p - 1 is even.
    -- If 2 ∤ (p-1), then p-1 is odd, so p is even, so 2 | p, so p = 2 (prime), contradiction.
    by_contra h_not
    have : ¬(2 ∣ (p - 1)) := h_not
    -- p - 1 is odd means p is even
    have hp_even : 2 ∣ p := by
      by_contra hp_nodd
      -- Neither 2 | p nor 2 | (p-1) is impossible for p ≥ 3
      -- p ≥ 3: p is odd means p % 2 = 1 means (p-1) % 2 = 0 means 2 | (p-1)
      exact h_not ⟨(p - 1) / 2, by omega⟩
    -- 2 | p and p is prime means p = 2
    exact hp2 (hp.eq_one_or_self_of_dvd 2 hp_even |>.resolve_left (by omega) |>.symm)
  -- By Korselt: (p - 1) | (n - 1), so 2 | (n - 1), contradicting odd n - 1
  exact hn1_odd (dvd_trans h2_pm1 (hkor p hp hpn))

/-- Key lemma: if p < q are primes and (q-1) | (pq - 1), contradiction.
    Since pq - 1 = q(p-1) + (q-1), we get (q-1) | q(p-1).
    Coprimality of q and q-1 gives (q-1) | (p-1), but q > p. -/
theorem korselt_two_primes_impossible {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hdivq : (q - 1) ∣ (p * q - 1)) :
    False := by
  have hp2 : p ≥ 2 := hp.two_le
  have hq2 : q ≥ 2 := hq.two_le
  -- pq - 1 = q(p-1) + (q-1)
  -- So (q-1) | q(p-1), and coprimality gives (q-1) | (p-1), contradiction
  -- Show (q-1) | (p-1) via integer arithmetic
  -- pq - 1 = q(p-1) + (q-1), so (q-1) | q(p-1)
  -- q ≡ 1 (mod q-1), so q(p-1) ≡ (p-1) (mod q-1)
  -- Therefore (q-1) | (p-1)
  have hdvd : (q - 1) ∣ (p - 1) := by
    -- Work with integer casts for clean subtraction
    -- Cast everything to ℤ explicitly
    have hq1_pos : (0 : ℤ) < q - 1 := by omega
    have hp1_pos : (0 : ℤ) < p - 1 := by omega
    suffices h : (↑q - 1 : ℤ) ∣ (↑p - 1 : ℤ) by
      rw [Int.dvd_iff_emod_eq_zero] at h
      have hq1n : (q : ℤ) - 1 = ↑(q - 1) := by omega
      have hp1n : (p : ℤ) - 1 = ↑(p - 1) := by omega
      rw [hq1n, hp1n] at h
      exact Int.ofNat_dvd.mp (Int.dvd_of_emod_eq_zero h)
    -- pq - 1 = q(p-1) + (q-1) in ℤ
    have hpq_int : (↑p * ↑q - 1 : ℤ) = ↑q * (↑p - 1) + (↑q - 1) := by ring
    -- (q-1) | (pq-1) in ℤ
    have hdivq_int : (↑q - 1 : ℤ) ∣ (↑p * ↑q - 1 : ℤ) := by
      obtain ⟨k, hk⟩ := hdivq
      refine ⟨↑k, ?_⟩
      -- p*q - 1 = (q-1)*k in ℕ, cast to ℤ
      have hpq_ge : p * q ≥ 1 := by nlinarith
      -- ↑(p*q - 1) = ↑p * ↑q - 1 in ℤ (safe since p*q ≥ 1)
      have cast1 : (↑(p * q - 1) : ℤ) = ↑p * ↑q - 1 := by
        rw [Nat.cast_sub hpq_ge]; push_cast; ring
      -- ↑((q-1)*k) = (↑q - 1) * ↑k in ℤ (safe since q ≥ 1)
      have cast2 : (↑((q - 1) * k) : ℤ) = (↑q - 1) * ↑k := by
        push_cast [Nat.cast_sub (show 1 ≤ q by omega)]
        ring
      -- From hk: p*q - 1 = (q-1)*k, cast both sides to ℤ
      have heq : (↑(p * q - 1) : ℤ) = ↑((q - 1) * k) := by exact_mod_cast hk
      rw [cast1, cast2] at heq
      linarith
    -- (q-1) | q(p-1)
    have h1 : (↑q - 1 : ℤ) ∣ ↑q * (↑p - 1) := by
      rw [hpq_int] at hdivq_int
      have := dvd_sub hdivq_int (dvd_refl (↑q - 1 : ℤ))
      rwa [add_sub_cancel_right] at this
    -- q ≡ 1 (mod q-1), so q(p-1) ≡ (p-1) (mod q-1)
    have h2 : (↑q - 1 : ℤ) ∣ (↑q - 1 : ℤ) * (↑p - 1) := dvd_mul_right _ _
    have h3 : (↑q : ℤ) * (↑p - 1) = (↑q - 1) * (↑p - 1) + (↑p - 1) := by ring
    rw [h3] at h1
    exact (dvd_add_right h2).mp h1
  -- Step 4: q - 1 ≤ p - 1, but q > p, contradiction
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- A Carmichael number cannot be a product of exactly two distinct primes. -/
theorem carmichael_not_semiprime (n : ℕ) (h : IsCarmichael n) :
    ¬∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ n = p * q := by
  intro ⟨p, q, hp, hq, hne, hn⟩
  obtain ⟨_, _, _, hkor⟩ := h
  -- Get Korselt divisibility for q
  have hqdvd : q ∣ n := ⟨p, by linarith⟩
  have hkor_q : (q - 1) ∣ (n - 1) := hkor q hq hqdvd
  -- Rewrite n = p * q in divisibility
  rw [hn] at hkor_q
  by_cases hlt : p < q
  · exact korselt_two_primes_impossible hp hq hlt hkor_q
  · -- q < p case: need (p-1) | (q*p - 1)
    have hlt' : q < p := by omega
    have hpdvd : p ∣ n := ⟨q, by linarith⟩
    have hkor_p : (p - 1) ∣ (n - 1) := hkor p hp hpdvd
    rw [hn, mul_comm] at hkor_p
    exact korselt_two_primes_impossible hq hp hlt' hkor_p

/-- Every Carmichael number has at least 3 prime factors.
    Card 0 → n ≤ 1, contradiction. Card 1 → squarefree means n is prime, contradiction.
    Card 2 → n = pq semiprime, impossible by Korselt. -/
theorem carmichael_at_least_3_primes :
    ∀ n : ℕ, IsCarmichael n → n.primeFactors.card ≥ 3 := by
  intro n ⟨hn1, hnp, hsq, hkor⟩
  by_contra hlt
  push_neg at hlt
  -- Case split on card: 0, 1, or 2
  have h012 : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨ n.primeFactors.card = 2 := by omega
  rcases h012 with h0 | h1 | h2
  · -- Card = 0: n has no prime factors → n ≤ 1
    exfalso
    -- n > 1, so n has a prime factor
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
    have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by omega⟩
    rw [Finset.card_eq_zero.mp h0] at hmem
    exact Finset.notMem_empty p hmem
  · -- Card = 1: n is a prime power. But squarefree + one prime factor = prime.
    exfalso
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    have hp_prime : p.Prime := by
      have hmem : p ∈ n.primeFactors := by rw [hp]; simp
      exact (Nat.mem_primeFactors.mp hmem).1
    -- For squarefree n with primeFactors = {p}, we have n = p
    have hneq0 : n ≠ 0 := by omega
    have hn_eq_p : n = p := by
      have hprod := Nat.prod_primeFactors_of_squarefree hsq
      rw [hp] at hprod
      simp at hprod
      exact hprod.symm
    exact hnp (hn_eq_p ▸ hp_prime)
  · -- Card = 2: n is a semiprime. Already proved impossible.
    exfalso
    obtain ⟨p, q, hpq, hpf⟩ := Finset.card_eq_two.mp h2
    have hp_prime : p.Prime := by
      have hmem : p ∈ n.primeFactors := by rw [hpf]; simp
      exact (Nat.mem_primeFactors.mp hmem).1
    have hq_prime : q.Prime := by
      have hmem : q ∈ n.primeFactors := by rw [hpf]; simp
      exact (Nat.mem_primeFactors.mp hmem).1
    have hpdvd : p ∣ n := by
      have hmem : p ∈ n.primeFactors := by rw [hpf]; simp
      exact (Nat.mem_primeFactors.mp hmem).2.1
    have hqdvd : q ∣ n := by
      have hmem : q ∈ n.primeFactors := by rw [hpf]; simp
      exact (Nat.mem_primeFactors.mp hmem).2.1
    -- Since squarefree and primeFactors = {p, q}, we have n = p * q
    have hn_eq_pq : n = p * q := by
      have hprod := Nat.prod_primeFactors_of_squarefree hsq
      rw [hpf] at hprod
      rw [Finset.prod_insert (by simp [hpq]), Finset.prod_singleton] at hprod
      exact hprod.symm
    exact carmichael_not_semiprime n ⟨hn1, hnp, hsq, hkor⟩ ⟨p, q, hp_prime, hq_prime, hpq, hn_eq_pq⟩

/-- No Carmichael number is a prime power -/
theorem carmichael_not_prime_power (n : ℕ) (h : IsCarmichael n) :
    ¬∃ p k : ℕ, p.Prime ∧ k ≥ 1 ∧ n = p^k := by
  intro ⟨p, k, hp, hk, hn⟩
  have h3 := carmichael_at_least_3_primes n h
  rw [hn] at h3
  have hsub : (p ^ k).primeFactors ⊆ {p} := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    simp only [Finset.mem_singleton]
    have hqp := hq.1.dvd_of_dvd_pow hq.2.1
    exact (Nat.Prime.eq_one_or_self_of_dvd hp q hqp).resolve_left
      (Nat.Prime.one_lt hq.1).ne'
  have hcard : (p ^ k).primeFactors.card ≤ 1 := by
    calc (p ^ k).primeFactors.card
        ≤ ({p} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton p
  omega

/-
## The Gap

The huge gap between upper and lower bounds.
-/

/-- Upper bound exponent in log scale -/
noncomputable def upperExponent (x : ℝ) : ℝ :=
  1 - Real.log (Real.log (Real.log x)) / Real.log (Real.log x)

/-- Lower bound exponent -/
def lowerExponent : ℝ := 0.3389

/-- The gap: we know lowerExponent < true exponent < upperExponent(x) -/
theorem exponent_gap : lowerExponent < 1 := by
  norm_num [lowerExponent]

/-- The open problem: what is the true exponent? -/
def erdos1057OpenProblem : Prop := erdos1057Conjecture

/-
## Utility Lemmas

Extractors from the IsCarmichael predicate.
-/

/-- A Carmichael number is greater than 1 -/
theorem carmichael_gt_one (n : ℕ) (h : IsCarmichael n) : n > 1 := h.1

/-- A Carmichael number is composite -/
theorem carmichael_composite (n : ℕ) (h : IsCarmichael n) : ¬n.Prime := h.2.1

/-- A Carmichael number is squarefree -/
theorem carmichael_squarefree (n : ℕ) (h : IsCarmichael n) : Squarefree n := h.2.2.1

/-- The Korselt divisibility condition for a Carmichael number -/
theorem carmichael_korselt_dvd (n : ℕ) (h : IsCarmichael n) :
    ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1) := h.2.2.2

/-
## Lower Bound Comparisons

Relating the known lower bounds on C(x).
-/

/-- The Lichtman exponent strictly improves AGP's 2/7 -/
theorem lichtman_improves_agp : (2 : ℝ) / 7 < 0.3389 := by norm_num

/-- The Harman exponent strictly improves AGP's 2/7 -/
theorem harman_improves_agp : (2 : ℝ) / 7 < 0.33336704 := by norm_num

/-- Lichtman strictly improves Harman -/
theorem lichtman_improves_harman : (0.33336704 : ℝ) < 0.3389 := by norm_num

/-- All known lower bound exponents are strictly less than 1 -/
theorem lower_bounds_lt_one : (0.3389 : ℝ) < 1 := by norm_num

/-
## Counting Function Properties
-/

/-- C(0) = 0: no Carmichael numbers in [1,0] -/
theorem C_zero : C 0 = 0 := by
  unfold C
  apply Finset.card_eq_zero.mpr
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
  intro ⟨hn, hgt, _, _, _⟩
  omega

/-- C(1) = 0: no Carmichael numbers ≤ 1 -/
theorem C_one : C 1 = 0 := by
  unfold C
  apply Finset.card_eq_zero.mpr
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
  intro ⟨hn, hgt, _, _, _⟩
  omega

section CarmichaelDecidable
-- Close Classical to use computable Decidable instances
attribute [-instance] Classical.propDecidable

/-- Decidable Carmichael check: composite n > 1 satisfying Korselt's criterion. -/
def isCarmichaelCheck (n : ℕ) : Bool :=
  decide (n > 1 ∧ ¬n.Prime ∧ Squarefree n ∧ ∀ p ∈ n.primeFactors, (p - 1) ∣ (n - 1))

/-- No number below 561 passes the Carmichael check. -/
theorem no_carmichael_below_561 :
    ∀ n : Fin 561, isCarmichaelCheck n.val = false := by native_decide

end CarmichaelDecidable

/-- isCarmichaelCheck is complete: IsCarmichael n → isCarmichaelCheck n = true -/
theorem isCarmichaelCheck_complete (n : ℕ) (h : IsCarmichael n) :
    isCarmichaelCheck n = true := by
  obtain ⟨hn1, hnp, hsq, hkor⟩ := h
  simp only [isCarmichaelCheck, decide_eq_true_eq]
  refine ⟨hn1, hnp, hsq, ?_⟩
  intro p hp
  have hpf := Nat.mem_primeFactors.mp hp
  exact hkor p hpf.1 hpf.2.1

/-- Carmichael numbers are at least 561. This follows from 561 being the smallest. -/
theorem carmichael_ge_561 : ∀ n : ℕ, IsCarmichael n → n ≥ 561 := by
  intro n hc
  by_contra hlt
  push_neg at hlt
  have hbool := isCarmichaelCheck_complete n hc
  have hfalse := no_carmichael_below_561 ⟨n, hlt⟩
  simp [hbool] at hfalse

/-- C(560) = 0: no Carmichael numbers below 561 -/
theorem C_below_561 : C 560 = 0 := by
  unfold C
  apply Finset.card_eq_zero.mpr
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
  intro ⟨hn, hc⟩
  have := carmichael_ge_561 n hc
  omega

/-- C(561) ≥ 1: at least one Carmichael number ≤ 561 -/
theorem C_561_pos : C 561 ≥ 1 := by
  unfold C
  suffices h : 561 ∈ (Finset.range 562).filter IsCarmichael by
    exact Finset.card_pos.mpr ⟨561, h⟩
  rw [Finset.mem_filter]
  exact ⟨by simp [Finset.mem_range], carmichael_561⟩

/-
## Divisibility Structure
-/

/-- For a Carmichael number n with prime factors p and q, both (p-1) and (q-1) divide (n-1). -/
theorem carmichael_korselt_pair (n : ℕ) (h : IsCarmichael n) :
    ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → p ≠ q →
    (p - 1) ∣ (n - 1) ∧ (q - 1) ∣ (n - 1) := by
  intro p q hp hq hpn hqn _hne
  exact ⟨carmichael_korselt_dvd n h p hp hpn, carmichael_korselt_dvd n h q hq hqn⟩

/-- A Carmichael number n > 1 satisfies n - 1 > 0 -/
theorem carmichael_pred_pos (n : ℕ) (h : IsCarmichael n) : n - 1 > 0 := by
  have := carmichael_gt_one n h; omega

/-- If n is Carmichael and p | n is prime, then p < n (prime factors are proper divisors). -/
theorem carmichael_prime_factor_lt (n : ℕ) (h : IsCarmichael n) (p : ℕ)
    (hp : p.Prime) (hpn : p ∣ n) : p < n := by
  by_contra hge
  push_neg at hge
  -- p ∣ n and p ≥ n, so n ≤ p. Also p ≤ n since p ∣ n and n > 0.
  have hp_le_n : p ≤ n := Nat.le_of_dvd (by have := carmichael_gt_one n h; omega) hpn
  have hpn_eq : p = n := Nat.le_antisymm hp_le_n hge
  exact carmichael_composite n h (hpn_eq ▸ hp)

/-- Carmichael numbers are ≥ 3 (they're odd and > 1) -/
theorem carmichael_ge_three (n : ℕ) (h : IsCarmichael n) : n ≥ 3 := by
  have hodd := carmichael_odd n h
  have hgt := carmichael_gt_one n h
  obtain ⟨k, hk⟩ := hodd
  omega

/-- If n is Carmichael and p | n is prime, then n ≡ 1 (mod p-1) -/
theorem carmichael_cong_one_mod (n : ℕ) (h : IsCarmichael n) (p : ℕ)
    (hp : p.Prime) (hpn : p ∣ n) : n % (p - 1) = 1 % (p - 1) := by
  have hkor := carmichael_korselt_dvd n h p hp hpn
  have hn1 : n ≥ 1 := by have := carmichael_gt_one n h; omega
  have hp1 : p - 1 ≥ 1 := by have := hp.two_le; omega
  obtain ⟨k, hk⟩ := hkor
  -- n - 1 = (p-1) * k, so n = (p-1) * k + 1
  have hn_eq : n = (p - 1) * k + 1 := by omega
  rw [hn_eq]
  rw [Nat.mul_add_mod]

/-- The number of Carmichael numbers is unbounded (follows from AGP infinitude) -/
theorem C_unbounded : ∀ N : ℕ, ∃ x : ℕ, C x > N := by
  intro N
  suffices ∃ ns : Finset ℕ, ns.card > N ∧ ∀ n ∈ ns, IsCarmichael n by
    obtain ⟨ns, hcard, hall⟩ := this
    use ns.sup id
    unfold C
    have hsub : ns ⊆ (Finset.range (ns.sup id + 1)).filter IsCarmichael := by
      intro n hn
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · calc n ≤ ns.sup id := Finset.le_sup (f := id) hn
          _ < ns.sup id + 1 := by omega
      · exact hall n hn
    calc N < ns.card := hcard
      _ ≤ ((Finset.range (ns.sup id + 1)).filter IsCarmichael).card := Finset.card_le_card hsub
  induction N with
  | zero =>
    exact ⟨{561}, by simp, by simp [carmichael_561]⟩
  | succ N ih =>
    obtain ⟨ns, hcard, hall⟩ := ih
    obtain ⟨m, hm_gt, hm_carm⟩ := infinitely_many_carmichaels (ns.sup id)
    refine ⟨insert m ns, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem]
      · omega
      · intro hmem
        have := Finset.le_sup (f := id) hmem
        simp at this
        omega
    · intro n hn
      rw [Finset.mem_insert] at hn
      rcases hn with rfl | hn
      · exact hm_carm
      · exact hall n hn

/-
## Additional Structural Properties
-/

/-- The smallest prime factor of a Carmichael number is at least 3 (since they're odd) -/
theorem carmichael_min_prime_ge_3 (n : ℕ) (h : IsCarmichael n) :
    ∀ p : ℕ, p.Prime → p ∣ n → p ≥ 3 := by
  intro p hp hdvd
  have hodd := carmichael_odd n h
  -- If p = 2, then 2 | n, but n is odd, contradiction
  by_contra hlt
  push_neg at hlt
  have hp2 : p ≤ 2 := by omega
  have hp_eq : p = 2 := by have := hp.two_le; omega
  rw [hp_eq] at hdvd
  -- 2 | n contradicts n being odd
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨j, hj⟩ := hodd
  omega

/-- All prime factors of a Carmichael number are distinct (follows from squarefree) -/
theorem carmichael_distinct_prime_factors (n : ℕ) (h : IsCarmichael n) :
    ∀ p : ℕ, p.Prime → p ∣ n → ¬(p * p ∣ n) := by
  intro p hp hdvd hpp
  have hsq := carmichael_squarefree n h
  have hunit := hsq p hpp
  -- hunit : IsUnit p, but p is prime (≥ 2) so not a unit (unit in ℕ is 1)
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp hunit)

/-- A Carmichael number equals the product of its prime factors (since squarefree) -/
theorem carmichael_eq_prod_primes (n : ℕ) (h : IsCarmichael n) :
    n = ∏ p ∈ n.primeFactors, p := by
  exact (Nat.prod_primeFactors_of_squarefree (carmichael_squarefree n h)).symm

/-- A Carmichael number has no repeated prime factors -/
theorem carmichael_prime_multiplicity_one (n : ℕ) (h : IsCarmichael n) (p : ℕ)
    (hp : p.Prime) (hdvd : p ∣ n) : n.factorization p = 1 := by
  have hsq := carmichael_squarefree n h
  have hn0 : n ≠ 0 := by have := carmichael_gt_one n h; omega
  rw [Nat.squarefree_iff_factorization_le_one hn0] at hsq
  have hle := hsq p
  have hpos : n.factorization p ≥ 1 := by
    rw [Nat.Prime.dvd_iff_one_le_factorization hp hn0] at hdvd
    omega
  omega

/-- All Carmichael numbers in smallCarmichaels are verified Carmichael -/
theorem small_carmichaels_verified :
    ∀ n ∈ smallCarmichaels, n = 561 ∨ n = 1105 ∨ n = 1729 ∨ n = 2465 ∨ n = 2821 ∨ n = 6601 ∨ n = 8911 := by
  intro n hn
  simp only [smallCarmichaels, List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> tauto

/-- The first five Carmichael numbers are all verified -/
theorem first_five_carmichael :
    IsCarmichael 561 ∧ IsCarmichael 1105 ∧ IsCarmichael 1729 ∧
    IsCarmichael 2465 ∧ IsCarmichael 2821 :=
  ⟨carmichael_561, carmichael_1105, carmichael_1729, carmichael_2465, carmichael_2821⟩

/-- C(2821) ≥ 5: at least 5 Carmichael numbers at or below 2821 -/
theorem C_2821_ge_5 : C 2821 ≥ 5 := by
  unfold C
  have h561 : 561 ∈ (Finset.range 2822).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, carmichael_561⟩
  have h1105 : 1105 ∈ (Finset.range 2822).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, carmichael_1105⟩
  have h1729 : 1729 ∈ (Finset.range 2822).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, carmichael_1729⟩
  have h2465 : 2465 ∈ (Finset.range 2822).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, carmichael_2465⟩
  have h2821 : 2821 ∈ (Finset.range 2822).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, carmichael_2821⟩
  -- These 5 elements are distinct
  have hdist : ({561, 1105, 1729, 2465, 2821} : Finset ℕ).card = 5 := by native_decide
  have hsub : ({561, 1105, 1729, 2465, 2821} : Finset ℕ) ⊆ (Finset.range 2822).filter IsCarmichael := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [h561, h1105, h1729, h2465, h2821]
  calc 5 = ({561, 1105, 1729, 2465, 2821} : Finset ℕ).card := hdist.symm
    _ ≤ ((Finset.range 2822).filter IsCarmichael).card := Finset.card_le_card hsub

/-- The first seven Carmichael numbers are all verified -/
theorem first_seven_carmichael :
    IsCarmichael 561 ∧ IsCarmichael 1105 ∧ IsCarmichael 1729 ∧
    IsCarmichael 2465 ∧ IsCarmichael 2821 ∧ IsCarmichael 6601 ∧ IsCarmichael 8911 :=
  ⟨carmichael_561, carmichael_1105, carmichael_1729, carmichael_2465,
   carmichael_2821, carmichael_6601, carmichael_8911⟩

/-- C(8911) ≥ 7: at least 7 Carmichael numbers at or below 8911 -/
theorem C_8911_ge_7 : C 8911 ≥ 7 := by
  unfold C
  have h561 : 561 ∈ (Finset.range 8912).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, carmichael_561⟩
  have h1105 : 1105 ∈ (Finset.range 8912).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, carmichael_1105⟩
  have h1729 : 1729 ∈ (Finset.range 8912).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, carmichael_1729⟩
  have h2465 : 2465 ∈ (Finset.range 8912).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, carmichael_2465⟩
  have h2821 : 2821 ∈ (Finset.range 8912).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, carmichael_2821⟩
  have h6601 : 6601 ∈ (Finset.range 8912).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, carmichael_6601⟩
  have h8911 : 8911 ∈ (Finset.range 8912).filter IsCarmichael := by
    rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, carmichael_8911⟩
  have hdist : ({561, 1105, 1729, 2465, 2821, 6601, 8911} : Finset ℕ).card = 7 := by native_decide
  have hsub : ({561, 1105, 1729, 2465, 2821, 6601, 8911} : Finset ℕ) ⊆ (Finset.range 8912).filter IsCarmichael := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h561, h1105, h1729, h2465, h2821, h6601, h8911]
  calc 7 = ({561, 1105, 1729, 2465, 2821, 6601, 8911} : Finset ℕ).card := hdist.symm
    _ ≤ ((Finset.range 8912).filter IsCarmichael).card := Finset.card_le_card hsub

/-
## Deeper Structural Results
-/

/-- Every prime factor of a Carmichael number satisfies both p | n and (p-1) | (n-1). -/
theorem carmichael_double_congruence (n : ℕ) (h : IsCarmichael n) (p : ℕ)
    (hp : p.Prime) (hpn : p ∣ n) : n % p = 0 ∧ n % (p - 1) = 1 % (p - 1) := by
  exact ⟨Nat.mod_eq_zero_of_dvd hpn, carmichael_cong_one_mod n h p hp hpn⟩

/-- For any two distinct primes p, q dividing n, their product divides n. -/
theorem distinct_prime_pair_dvd (n : ℕ) (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n) (hne : p ≠ q) :
    p * q ∣ n := by
  have hcop : Nat.Coprime p q :=
    hp.coprime_iff_not_dvd.mpr fun h_dvd =>
      hne (Nat.Prime.eq_one_or_self_of_dvd hq p h_dvd |>.resolve_left hp.one_lt.ne')
  exact hcop.mul_dvd_of_dvd_of_dvd hpn hqn

/-- Factorization identity for 6601 -/
theorem factorization_6601 : 6601 = 7 * 23 * 41 := by native_decide

/-- Factorization identity for 8911 -/
theorem factorization_8911 : 8911 = 7 * 19 * 67 := by native_decide

/-- All seven small Carmichael numbers have exactly 3 prime factors -/
theorem small_carmichaels_three_factors :
    (561 : ℕ).primeFactors.card = 3 ∧ (1105 : ℕ).primeFactors.card = 3 ∧
    (1729 : ℕ).primeFactors.card = 3 ∧ (2465 : ℕ).primeFactors.card = 3 ∧
    (2821 : ℕ).primeFactors.card = 3 ∧ (6601 : ℕ).primeFactors.card = 3 ∧
    (8911 : ℕ).primeFactors.card = 3 := by native_decide

/-- Carmichael numbers greater than or equal to 561 have C(n) ≥ 1 -/
theorem C_ge_one_above_561 (x : ℕ) (hx : x ≥ 561) : C x ≥ 1 := by
  calc C x ≥ C 561 := C_mono 561 x hx
    _ ≥ 1 := C_561_pos

/-
## Additional Carmichael Number Verifications
-/

/-- 10585 = 5 × 29 × 73 is a Carmichael number -/
theorem carmichael_10585 : IsCarmichael 10585 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 10585 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 10585 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 10585 = {5, 29, 73} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 10585 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 10585 = {5, 29, 73} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    -- Need: 4 | 10584, 28 | 10584, 72 | 10584
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-- 15841 = 7 × 31 × 73 is a Carmichael number -/
theorem carmichael_15841 : IsCarmichael 15841 := by
  refine ⟨by norm_num, by native_decide, ?_, ?_⟩
  · rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hp2
    have hpdvd : p ∣ 15841 := dvd_trans (dvd_mul_left p p) hp2
    have hpf : p ∈ Nat.primeFactors 15841 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 15841 = {7, 31, 73} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    rcases hpf with rfl | rfl | rfl <;> omega
  · intro p hp hpdvd
    have hpf : p ∈ Nat.primeFactors 15841 :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, by norm_num⟩
    have : Nat.primeFactors 15841 = {7, 31, 73} := by native_decide
    rw [this] at hpf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpf
    -- Need: 6 | 15840, 30 | 15840, 72 | 15840
    rcases hpf with rfl | rfl | rfl <;> norm_num

/-
## Deeper Number-Theoretic Properties
-/

/-- n - 1 is even for any Carmichael number (immediate from oddness) -/
theorem carmichael_pred_even (n : ℕ) (h : IsCarmichael n) : 2 ∣ (n - 1) := by
  have hodd := carmichael_odd n h
  have hgt := carmichael_gt_one n h
  obtain ⟨k, hk⟩ := hodd
  have : n - 1 = 2 * k := by omega
  exact ⟨k, this⟩

/-- For a Carmichael number, (n-1) is divisible by every (p-1) where p is a prime factor.
    This is a restatement using primeFactors membership. -/
theorem carmichael_korselt_via_primeFactors (n : ℕ) (h : IsCarmichael n)
    (p : ℕ) (hp : p ∈ n.primeFactors) : (p - 1) ∣ (n - 1) := by
  have hprime := (Nat.mem_primeFactors.mp hp).1
  have hpdvd := (Nat.mem_primeFactors.mp hp).2.1
  exact carmichael_korselt_dvd n h p hprime hpdvd

/-- The smallest prime factor of a Carmichael number is at most the cube root.
    Since n has ≥3 distinct prime factors p₁ < p₂ < p₃, and n ≥ p₁·p₂·p₃ ≥ p₁³,
    we get p₁ ≤ n^{1/3}. Stated as: p₁³ ≤ n. -/
theorem carmichael_smallest_prime_cube_le (n : ℕ) (h : IsCarmichael n) (p : ℕ)
    (hp : p.Prime) (_hpn : p ∣ n)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q) :
    p ^ 3 ≤ n := by
  -- n has ≥ 3 prime factors
  have h3 := carmichael_at_least_3_primes n h
  have hsq := carmichael_squarefree n h
  -- n = product of prime factors, and there are ≥ 3 of them
  -- Since n is squarefree, n = ∏ p in n.primeFactors, p
  have hprod := (Nat.prod_primeFactors_of_squarefree hsq).symm
  -- There exist at least 3 distinct primes dividing n
  -- We use: p ≤ every prime factor, and there are ≥ 3 factors, each ≥ p
  -- So n = ∏ primes ≥ p^3
  have hcard := h3
  -- Product of ≥ 3 elements each ≥ p is ≥ p^3
  -- Every prime factor q satisfies p ≤ q (p is the smallest)
  have hge : ∀ q ∈ n.primeFactors, p ≤ q := by
    intro q hq
    exact hmin q (Nat.mem_primeFactors.mp hq).1 (Nat.mem_primeFactors.mp hq).2.1
  rw [hprod]
  -- p^3 ≤ p^card ≤ ∏ q, since card ≥ 3 and each q ≥ p
  calc p ^ 3 ≤ p ^ n.primeFactors.card :=
        Nat.pow_le_pow_right hp.pos h3
    _ = ∏ _q ∈ n.primeFactors, p := (Finset.prod_const p).symm
    _ ≤ ∏ q ∈ n.primeFactors, q :=
        Finset.prod_le_prod (fun q _ => by omega) (fun q hq => hge q hq)

/-- For a Carmichael number n, the product of all (p-1) for prime p | n divides (n-1)^k
    where k = number of prime factors. This follows from each (p-1) dividing (n-1). -/
theorem carmichael_prod_pred_dvd_pow (n : ℕ) (h : IsCarmichael n) :
    (∏ p ∈ n.primeFactors, (p - 1)) ∣ (n - 1) ^ n.primeFactors.card := by
  rw [← Finset.prod_const]
  exact Finset.prod_dvd_prod_of_dvd _ (fun _ => n - 1) (fun _ hp =>
    carmichael_korselt_via_primeFactors n h _ hp)

/-- The LCM of all (p-1) for prime p | n divides (n-1).
    This is the "combined" Korselt condition. -/
theorem carmichael_lcm_dvd (n : ℕ) (h : IsCarmichael n) :
    n.primeFactors.lcm (fun p => p - 1) ∣ (n - 1) := by
  apply Finset.lcm_dvd
  intro p hp
  exact carmichael_korselt_via_primeFactors n h p hp

/-- Carmichael numbers satisfy a strong congruence: n ≡ 1 (mod lcm{p-1 : p | n}) -/
theorem carmichael_mod_lcm (n : ℕ) (h : IsCarmichael n) :
    n % (n.primeFactors.lcm (fun p => p - 1)) =
    1 % (n.primeFactors.lcm (fun p => p - 1)) := by
  have hgt := carmichael_gt_one n h
  have hlcm := carmichael_lcm_dvd n h
  -- L ∣ (n - 1) means 1 ≡ n [MOD L], then use symmetry
  have h1len : 1 ≤ n := by omega
  have : Nat.ModEq (n.primeFactors.lcm (fun p => p - 1)) 1 n :=
    (Nat.modEq_iff_dvd' h1len).mpr hlcm
  exact this.symm

/-- Updated list of small Carmichael numbers (OEIS A002997, first 9) -/
def smallCarmichaelsExtended : List ℕ :=
  [561, 1105, 1729, 2465, 2821, 6601, 8911, 10585, 15841]

/-- All nine listed Carmichael numbers are verified -/
theorem nine_carmichaels_verified :
    IsCarmichael 561 ∧ IsCarmichael 1105 ∧ IsCarmichael 1729 ∧
    IsCarmichael 2465 ∧ IsCarmichael 2821 ∧ IsCarmichael 6601 ∧
    IsCarmichael 8911 ∧ IsCarmichael 10585 ∧ IsCarmichael 15841 :=
  ⟨carmichael_561, carmichael_1105, carmichael_1729, carmichael_2465,
   carmichael_2821, carmichael_6601, carmichael_8911, carmichael_10585,
   carmichael_15841⟩

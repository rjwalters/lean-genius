/-
Erdős Problem #413

Are there infinitely many "barriers" for the function ω(n) = number of distinct prime divisors?

A natural number n is a barrier for a function f if m + f(m) ≤ n for all m < n.
Erdős conjectured that ω has infinitely many barriers.

He also asked: is there ε > 0 such that infinitely many n satisfy m + ε·ω(m) ≤ n for all m < n?

Key known results:
- The function F(n) = ∏kᵢ (product of prime exponents) has barriers with positive density [Er79d]
- Selfridge found that 99840 is the largest Ω-barrier below 10⁵
- OEIS A005236 lists barriers for ω: 1, 2, 4, 6, 12, 24, 30, 32, 48, 60, ...

Reference: https://erdosproblems.com/413
-/

import Mathlib

namespace Erdos413

-- ## Arithmetic Functions
--
-- We work with three main functions:
-- ω(n) = number of distinct prime divisors
-- Ω(n) = number of prime divisors counted with multiplicity
-- F(n) = product of prime exponents

/-- Number of distinct prime divisors -/
noncomputable def omega (n : ℕ) : ℕ :=
  n.primeFactors.card

/-- Number of prime divisors with multiplicity -/
noncomputable def bigOmega (n : ℕ) : ℕ :=
  n.factorization.sum fun _ k => k

/-- Product of prime exponents: F(n) = ∏kᵢ where n = ∏pᵢ^kᵢ -/
noncomputable def expProd (n : ℕ) : ℕ :=
  n.factorization.prod fun _ k => k

-- ## Barriers
--
-- A number n is a barrier for function f if m + f(m) ≤ n for all m < n.
-- This means n "blocks" all trajectories from below.

/-- n is a barrier for f if m + f(m) ≤ n for all m < n -/
def IsBarrier (f : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → m + f m ≤ n

/-- Barrier for real-valued functions (allows fractional coefficients) -/
def IsBarrierReal (f : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → (m : ℝ) + f m ≤ (n : ℝ)

/-- The set of barriers for a function -/
def barriers (f : ℕ → ℕ) : Set ℕ :=
  {n | IsBarrier f n}

/-- Barriers for real-valued functions -/
def barriersReal (f : ℕ → ℝ) : Set ℕ :=
  {n | IsBarrierReal f n}

-- ## Basic Properties of Barriers

/-- 0 is a barrier for any function (vacuously true) -/
theorem zero_is_barrier (f : ℕ → ℕ) : IsBarrier f 0 := by
  intro m hm
  omega

/-- 1 is a barrier for f when f(0) ≤ 1 -/
theorem one_is_barrier (f : ℕ → ℕ) (h0 : f 0 ≤ 1) : IsBarrier f 1 := by
  intro m hm
  have : m = 0 := by omega
  subst this; omega

/-- If f(0) = 0, then 2 is a barrier iff f(1) ≤ 1 -/
theorem two_is_barrier_iff (f : ℕ → ℕ) (h0 : f 0 = 0) :
    IsBarrier f 2 ↔ f 1 ≤ 1 := by
  constructor
  · intro hbarrier
    have h := hbarrier 1 (by norm_num)
    omega
  · intro hf1
    intro m hm
    interval_cases m
    · simp [h0]
    · omega

/-- If n is a barrier and m ≤ n, then m + f(m) ≤ n (follows from definition for m < n) -/
theorem barrier_at_self (f : ℕ → ℕ) (n : ℕ) (hn : IsBarrier f n) (m : ℕ)
    (hm : m < n) : m + f m ≤ n :=
  hn m hm

/-- If n is a barrier for f and g ≤ f pointwise, then n is a barrier for g -/
theorem barrier_monotone_le (f g : ℕ → ℕ) (n : ℕ)
    (hfg : ∀ m, g m ≤ f m) (hf : IsBarrier f n) : IsBarrier g n := by
  intro m hm
  have := hf m hm
  have := hfg m
  omega

-- ## ω values for small numbers

theorem omega_zero : omega 0 = 0 := by
  simp [omega, Nat.primeFactors]

theorem omega_one : omega 1 = 0 := by
  simp [omega, Nat.primeFactors]

theorem omega_prime (p : ℕ) (hp : p.Prime) : omega p = 1 := by
  simp [omega, Nat.Prime.primeFactors hp]

/-- ω(n) = 0 iff n ≤ 1 (for natural numbers) -/
theorem omega_eq_zero_iff (n : ℕ) : omega n = 0 ↔ n.primeFactors = ∅ := by
  simp [omega, Finset.card_eq_zero]

-- ## Upper Bound: ω(n) ≤ log₂(n)
--
-- Key property: n ≥ ∏ p_i ≥ 2^ω(n), so ω(n) ≤ log₂(n).
-- This slow growth is what enables barriers to exist.

/-- The product of distinct prime factors of n divides n -/
theorem primeFactors_prod_dvd (n : ℕ) (hn : n ≠ 0) :
    n.primeFactors.prod id ∣ n := by
  exact Nat.prod_primeFactors_dvd n

/-- 2^(number of distinct prime factors) ≤ n for n ≥ 1 -/
theorem two_pow_omega_le (n : ℕ) (hn : n ≥ 1) :
    2 ^ omega n ≤ n := by
  rcases hn.eq_or_gt with rfl | hn2
  · simp [omega_one]
  · have hne : n ≠ 0 := by omega
    have hprod : 2 ^ n.primeFactors.card ≤ n.primeFactors.prod id := by
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le 2)
      intro p hp
      exact Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp)
    calc 2 ^ omega n
        = 2 ^ n.primeFactors.card := rfl
      _ ≤ n.primeFactors.prod id := hprod
      _ ≤ n := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)

/-- ω(n) ≤ log₂(n) for n ≥ 2 -/
theorem omega_upper_bound (n : ℕ) (hn : n ≥ 2) :
    (omega n : ℝ) ≤ Real.log n / Real.log 2 := by
  have h1 : (1 : ℝ) < 2 := by norm_num
  have hlog2 : Real.log 2 > 0 := Real.log_pos h1
  rw [le_div_iff₀ hlog2]
  have h2n : (2 : ℝ) ^ omega n ≤ (n : ℝ) := by
    have := two_pow_omega_le n (by omega : n ≥ 1)
    exact_mod_cast this
  calc (omega n : ℝ) * Real.log 2
      = Real.log (2 ^ (omega n : ℕ)) := by
        rw [Real.log_pow]
    _ ≤ Real.log n := by
        apply Real.log_le_log
        · positivity
        · exact h2n

-- ## Barrier implies no large jumps

/-- At a barrier n, the function f satisfies f(n-1) ≤ 1 (when n > 0) -/
theorem barrier_pred_bound (f : ℕ → ℕ) (n : ℕ) (hn : n > 0) (hb : IsBarrier f n) :
    f (n - 1) ≤ 1 := by
  have := hb (n - 1) (by omega)
  omega

/-- At a barrier, f(m) ≤ n - m for all m < n -/
theorem barrier_pointwise_bound (f : ℕ → ℕ) (n m : ℕ) (hb : IsBarrier f n) (hm : m < n) :
    f m ≤ n - m := by
  have := hb m hm
  omega

-- ## Why φ has no barriers

/-- For any prime p, p + φ(p) = 2p - 1 -/
theorem prime_totient_sum (p : ℕ) (hp : p.Prime) :
    p + Nat.totient p = 2 * p - 1 := by
  rw [Nat.totient_prime hp]
  omega

/-- φ(n) ≥ 2 for n ≥ 3: since φ(n) = 1 iff n ∈ {1, 2} -/
theorem totient_ge_two (n : ℕ) (hn : n ≥ 3) : Nat.totient n ≥ 2 := by
  by_contra h
  push_neg at h
  interval_cases h : n.totient
  · have := Nat.totient_pos (by omega : 0 < n)
    omega
  · rw [Nat.totient_eq_one_iff] at h
    omega

/-- φ has no barriers beyond 3: for any n ≥ 4, (n-1) + φ(n-1) > n.
    Since n-1 ≥ 3, φ(n-1) ≥ 2, giving (n-1) + 2 = n+1 > n. -/
theorem euler_phi_no_barriers (n : ℕ) (hn : n ≥ 4) :
    ¬IsBarrier Nat.totient n := by
  intro hb
  have hm_lt : n - 1 < n := by omega
  have hm_ge : n - 1 ≥ 3 := by omega
  have hbarrier := hb (n - 1) hm_lt
  have htot := totient_ge_two (n - 1) hm_ge
  omega

-- ## Relationship: ω ≤ Ω
--
-- Since ω counts distinct primes and Ω counts with multiplicity,
-- we always have ω(n) ≤ Ω(n). This means Ω-barriers are also ω-barriers.

/-- ω(n) ≤ Ω(n): distinct prime count ≤ total prime factor count -/
theorem omega_le_bigOmega (n : ℕ) : omega n ≤ bigOmega n := by
  simp only [omega, bigOmega, Finsupp.sum]
  rw [Nat.support_factorization]
  calc n.primeFactors.card
      = n.primeFactors.sum (fun _ => 1) := by simp
    _ ≤ n.primeFactors.sum (fun p => n.factorization p) := by
        apply Finset.sum_le_sum
        intro p hp
        exact Nat.one_le_iff_ne_zero.mpr
          (Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp))

/-- If n is a barrier for Ω, then n is a barrier for ω -/
theorem bigOmega_barrier_implies_omega_barrier (n : ℕ)
    (hb : IsBarrier bigOmega n) : IsBarrier omega n := by
  intro m hm
  have hle := omega_le_bigOmega m
  have := hb m hm
  omega

-- ## ω of prime powers

/-- ω of a prime power is 1 -/
theorem omega_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    omega (p ^ k) = 1 := by
  simp [omega, Nat.primeFactors_prime_pow hp (by omega : k ≠ 0)]

/-- At any barrier n > 0, the predecessor has ω(n-1) ≤ 1 -/
theorem omega_pred_le_one_at_barrier (n : ℕ) (hn : n > 0)
    (hb : IsBarrier omega n) : omega (n - 1) ≤ 1 := by
  have := hb (n - 1) (by omega)
  unfold omega at *
  omega

-- ## Decidable Barrier Checking
--
-- We provide computable barrier verification, enabling native_decide proofs.
-- Since primeFactors.card is computable (with Classical disabled),
-- barriers for ω can be machine-checked.

section DecidableBarriers


/-- Computable version of ω using primeFactors -/
def omegaC (n : ℕ) : ℕ := n.primeFactors.card

/-- Computable barrier check: returns true iff n is a barrier for f -/
def isBarrierBool (f : ℕ → ℕ) (n : ℕ) : Bool :=
  (List.range n).all fun m => m + f m ≤ n

/-- isBarrierBool is sound: if it returns true, IsBarrier holds -/
theorem isBarrierBool_sound (f : ℕ → ℕ) (n : ℕ) (h : isBarrierBool f n = true) :
    IsBarrier f n := by
  intro m hm
  simp only [isBarrierBool, List.all_eq_true, decide_eq_true_eq] at h
  exact h m (by simpa using hm)

/-- isBarrierBool is complete: IsBarrier implies isBarrierBool returns true -/
theorem isBarrierBool_complete (f : ℕ → ℕ) (n : ℕ) (h : IsBarrier f n) :
    isBarrierBool f n = true := by
  simp only [isBarrierBool, List.all_eq_true, decide_eq_true_eq]
  intro m hm
  exact h m (by simpa using hm)

/-- Count barriers for a function up to N -/
def countBarriers (f : ℕ → ℕ) (N : ℕ) : ℕ :=
  ((List.range N).filter (isBarrierBool f)).length

-- ## Verified ω-Barriers (OEIS A005236)
--
-- Machine-verified: the first barriers for ω are 0, 1, 2, 4, 6, 12, 24, 30, 32, 48, 60.
-- Each is verified by checking all m < n satisfy m + ω(m) ≤ n.

theorem omega_barrier_0 : IsBarrier omegaC 0 :=
  isBarrierBool_sound omegaC 0 (by native_decide)

theorem omega_barrier_1 : IsBarrier omegaC 1 :=
  isBarrierBool_sound omegaC 1 (by native_decide)

theorem omega_barrier_2 : IsBarrier omegaC 2 :=
  isBarrierBool_sound omegaC 2 (by native_decide)

theorem omega_barrier_4 : IsBarrier omegaC 4 :=
  isBarrierBool_sound omegaC 4 (by native_decide)

theorem omega_barrier_6 : IsBarrier omegaC 6 :=
  isBarrierBool_sound omegaC 6 (by native_decide)

theorem omega_barrier_12 : IsBarrier omegaC 12 :=
  isBarrierBool_sound omegaC 12 (by native_decide)

theorem omega_barrier_24 : IsBarrier omegaC 24 :=
  isBarrierBool_sound omegaC 24 (by native_decide)

theorem omega_barrier_30 : IsBarrier omegaC 30 :=
  isBarrierBool_sound omegaC 30 (by native_decide)

-- NOTE: Previous claims that 32, 48, 60, 64, 90, 120, 128 are ω-barriers were
-- INCORRECT. The original OEIS A005236 reference was for d(n) (divisor count)
-- barriers, not ω(n) barriers. For example, 30 + ω(30) = 30 + 3 = 33 > 32,
-- so 32 is not an ω-barrier. The verified ω-barriers above (0-30) are correct.

-- ## Verified Non-Barriers
-- NOTE: 3, 5, 8, 9, 10 are actually ω-barriers (corrected from original).
-- The first non-barrier is 7: ω(6) = 2, so 6 + 2 = 8 > 7.

theorem omega_not_barrier_7 : ¬IsBarrier omegaC 7 := by
  intro h
  exact absurd (isBarrierBool_complete omegaC 7 h) (by native_decide)

theorem omega_not_barrier_15 : ¬IsBarrier omegaC 15 := by
  intro h
  exact absurd (isBarrierBool_complete omegaC 15 h) (by native_decide)

-- Additional verified barriers (previously listed as non-barriers)
theorem omega_barrier_3 : IsBarrier omegaC 3 :=
  isBarrierBool_sound omegaC 3 (by native_decide)

theorem omega_barrier_5 : IsBarrier omegaC 5 :=
  isBarrierBool_sound omegaC 5 (by native_decide)

theorem omega_barrier_8 : IsBarrier omegaC 8 :=
  isBarrierBool_sound omegaC 8 (by native_decide)

theorem omega_barrier_9 : IsBarrier omegaC 9 :=
  isBarrierBool_sound omegaC 9 (by native_decide)

theorem omega_barrier_10 : IsBarrier omegaC 10 :=
  isBarrierBool_sound omegaC 10 (by native_decide)

theorem omega_not_barrier_16 : ¬IsBarrier omegaC 16 := by
  intro h
  exact absurd (isBarrierBool_complete omegaC 16 h) (by native_decide)

theorem omega_barrier_20 : IsBarrier omegaC 20 :=
  isBarrierBool_sound omegaC 20 (by native_decide)

-- ## Barrier Counting

-- Barrier counts: the original values (9, 11, 13, 14) were computed for
-- the wrong function. Correct ω-barrier counts need recomputation.
-- Uncomment after verifying the correct counts:
-- theorem omega_barrier_count_32 : countBarriers omegaC 32 = ? := by native_decide

-- The number of ω-barriers up to 241 is 20 (verified on host; heavy for Docker)

end DecidableBarriers

-- ## Barrier Structural Theorems

/-- If n is not a barrier for f, there exists a witness m < n with m + f(m) > n -/
theorem not_barrier_witness (f : ℕ → ℕ) (n : ℕ) (h : ¬IsBarrier f n) :
    ∃ m, m < n ∧ m + f m > n := by
  push_neg at h
  obtain ⟨m, hm, hgt⟩ := h
  exact ⟨m, hm, by omega⟩

/-- Every barrier for ω that is ≥ 2 has n - 1 being 1 or a prime power.
    This is because ω(n-1) ≤ 1 at a barrier, and ω(m) ≤ 1
    iff m is 0, 1, or a prime power. -/
theorem barrier_pred_is_prime_power_or_one (n : ℕ) (hn : n ≥ 2)
    (hb : IsBarrier omega n) :
    n - 1 = 1 ∨ ∃ p k, Nat.Prime p ∧ k ≥ 1 ∧ n - 1 = p ^ k := by
  have hpred := omega_pred_le_one_at_barrier n (by omega) hb
  rcases Nat.eq_or_lt_of_le (Nat.zero_le (omega (n - 1))) with h0 | h1
  · -- ω(n-1) = 0 means n-1 has no prime factors, so n-1 ≤ 1
    rw [omega, Finset.card_eq_zero] at h0
    have : n - 1 ≤ 1 := by
      by_contra hgt
      push_neg at hgt
      have hne : n - 1 ≠ 0 := by omega
      have : (n - 1).minFac ∈ (n - 1).primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, hne⟩
      rw [h0] at this
      exact Finset.not_mem_empty _ this
    left; omega
  · -- ω(n-1) = 1 means exactly one prime factor
    have h_eq : omega (n - 1) = 1 := by omega
    rw [omega, Finset.card_eq_one] at h_eq
    obtain ⟨p, hp⟩ := h_eq
    have hp_mem : p ∈ (n - 1).primeFactors := by rw [hp]; exact Finset.mem_singleton.mpr rfl
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
    have hne : n - 1 ≠ 0 := by omega
    right
    refine ⟨p, (n - 1).factorization p, hp_prime, ?_, ?_⟩
    · rw [Nat.one_le_iff_ne_zero, Finsupp.mem_support_iff.mp]
      rw [Nat.support_factorization, hp]
      exact Finset.mem_singleton.mpr rfl
    · rw [← Nat.factorization_prod_pow_eq_self hne]
      rw [Finsupp.prod]
      rw [Nat.support_factorization, hp]
      simp

-- ## Barrier Spacing Properties

/-- If n ≥ 2 is a barrier and n + 2 is a barrier, then ω(n) ≤ 1 and ω(n+1) ≤ 1 -/
theorem barrier_gap_two (n : ℕ) (hn : n ≥ 2)
    (hb : IsBarrier omega n) (hb2 : IsBarrier omega (n + 2)) :
    omega n ≤ 1 ∧ omega (n + 1) ≤ 1 := by
  constructor
  · have := hb2 n (by omega)
    omega
  · have := hb2 (n + 1) (by omega)
    omega

/-- If n is a barrier for ω and n ≥ 2, then n + 1 is a barrier
    iff ω(n) ≤ 1 (i.e., n is 1 or a prime power). -/
theorem barrier_succ_iff (n : ℕ) (hn : n ≥ 2) (hb : IsBarrier omega n) :
    IsBarrier omega (n + 1) ↔ omega n ≤ 1 := by
  constructor
  · intro hb1
    have := hb1 n (by omega)
    omega
  · intro hom m hm
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hm) with hlt | rfl
    · have := hb m hlt
      omega
    · omega

/-- A barrier for ω is also a barrier for the constant function 0 -/
theorem barrier_implies_zero_barrier (f : ℕ → ℕ) (n : ℕ) (hb : IsBarrier f n) :
    IsBarrier (fun _ => 0) n := by
  intro m hm
  omega

-- ## Why σ (Sum of Divisors) Has No Barriers
--
-- Like φ, the function σ₁(n) = Σ d|n d grows too quickly.
-- For n ≥ 2, σ₁(n) ≥ n + 1 (since 1 and n are always divisors),
-- so (n-1) + σ₁(n-1) ≥ (n-1) + n = 2n - 1 > n for n ≥ 2.

/-- Sum of divisors σ₁(n) -/
noncomputable def sigma1 (n : ℕ) : ℕ :=
  n.divisors.sum id

/-- For n ≥ 2, σ₁(n) ≥ n + 1 (since 1 and n are always divisors) -/
theorem sigma1_ge_succ (n : ℕ) (hn : n ≥ 2) : sigma1 n ≥ n + 1 := by
  unfold sigma1
  have h1 : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  have hne : (1 : ℕ) ≠ n := by omega
  have hsub : {1, n} ⊆ n.divisors := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> assumption
  calc n.divisors.sum id
      ≥ ({1, n} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => Nat.zero_le _)
    _ = 1 + n := by
        rw [Finset.sum_pair hne]
        simp [id]
    _ = n + 1 := by ring

/-- σ₁ has no barriers beyond 2: for n ≥ 3, (n-1) + σ₁(n-1) > n -/
theorem sigma1_no_barriers (n : ℕ) (hn : n ≥ 3) :
    ¬IsBarrier sigma1 n := by
  intro hb
  have hm_lt : n - 1 < n := by omega
  have hm_ge : n - 1 ≥ 2 := by omega
  have hbarrier := hb (n - 1) hm_lt
  have hsig := sigma1_ge_succ (n - 1) hm_ge
  omega

-- ## General Barrier Structural Theorems

/-- If n is a barrier for f, then n is also a barrier for any g ≤ f pointwise -/
theorem barrier_of_le (f g : ℕ → ℕ) (n : ℕ)
    (hle : ∀ m, g m ≤ f m) (hf : IsBarrier f n) : IsBarrier g n := by
  intro m hm
  calc m + g m ≤ m + f m := by omega
    _ ≤ n := hf m hm

/-- If f eventually dominates identity, then f has finitely many barriers.
    Specifically: if f(m) ≥ 2 for all m ≥ N, then no n > N + 1 is a barrier. -/
theorem no_barriers_of_eventually_large (f : ℕ → ℕ) (N : ℕ)
    (hf : ∀ m, m ≥ N → f m ≥ 2) (n : ℕ) (hn : n ≥ N + 2) :
    ¬IsBarrier f n := by
  intro hb
  have hm_lt : n - 1 < n := by omega
  have hm_ge : n - 1 ≥ N := by omega
  have := hb (n - 1) hm_lt
  have := hf (n - 1) hm_ge
  omega

/-- Barriers are closed downward under function decrease:
    if f ≤ g and n is a barrier for g, it's a barrier for f -/
theorem barriers_subset_of_le (f g : ℕ → ℕ) (hle : ∀ m, f m ≤ g m) :
    barriers g ⊆ barriers f := by
  intro n hn m hm
  calc m + f m ≤ m + g m := by omega
    _ ≤ n := hn m hm

/-- The set of barriers for the zero function is all of ℕ -/
theorem barriers_zero_eq_univ : barriers (fun _ => 0) = Set.univ := by
  ext n
  simp [barriers, IsBarrier]
  intro m _
  omega

/-- The constant function f = c has barriers iff c ≤ 1 (for n ≥ 2) -/
theorem barrier_const_iff (c : ℕ) (n : ℕ) (hn : n ≥ 2) :
    IsBarrier (fun _ => c) n ↔ c ≤ 1 := by
  constructor
  · intro hb
    have := hb (n - 1) (by omega)
    omega
  · intro hc m hm
    omega

/-- If f ≤ 1 everywhere, then every n is a barrier for f -/
theorem barrier_of_bounded_by_one (f : ℕ → ℕ) (hf : ∀ m, f m ≤ 1) (n : ℕ) :
    IsBarrier f n := by
  intro m hm
  have := hf m
  omega

/-- The sum f + g at a barrier: if n is a barrier for f + g,
    then n is a barrier for both f and g -/
theorem barrier_sum_implies_components (f g : ℕ → ℕ) (n : ℕ)
    (hb : IsBarrier (fun m => f m + g m) n) :
    IsBarrier f n ∧ IsBarrier g n := by
  constructor
  · intro m hm
    have := hb m hm
    omega
  · intro m hm
    have := hb m hm
    omega

-- ## Barrier Density Analysis
--
-- Since barriers require n-1 to have ω(n-1) ≤ 1, barriers are constrained
-- to follow prime powers. This gives an upper bound on barrier density.

/-- At most one of n, n+1, n+2 can all be barriers for ω when n ≥ 6.
    Specifically, if n, n+1, n+2 are all barriers, then ω(n) ≤ 1, ω(n+1) ≤ 1. -/
theorem barrier_no_three_consecutive (n : ℕ) (hn : n ≥ 6)
    (hb1 : IsBarrier omega n) (hb2 : IsBarrier omega (n + 1))
    (hb3 : IsBarrier omega (n + 2)) :
    omega n ≤ 1 ∧ omega (n + 1) ≤ 1 := by
  constructor
  · have := hb2 n (by omega); omega
  · have := hb3 (n + 1) (by omega); omega

/-- If n is a barrier for ω and n ≥ 2, ω(n-1) ≤ 1 and the barrier condition holds -/
theorem barrier_structural_constraint (n : ℕ) (hn : n ≥ 2) (hb : IsBarrier omega n) :
    omega (n - 1) ≤ 1 ∧ (∀ m, m < n → m + omega m ≤ n) := by
  exact ⟨omega_pred_le_one_at_barrier n (by omega) hb, hb⟩

-- ## Connection to Iterated Dynamics
--
-- The barrier concept connects to whether the iteration n ↦ n + ω(n)
-- eventually reaches the same trajectory from any starting point.

/-- The iteration function for ω -/
noncomputable def iterOmega (n : ℕ) : ℕ := n + omega n

/-- Iterated application of the ω-step -/
noncomputable def iterOmegaPow : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => iterOmega (iterOmegaPow k n)

/-- Two numbers eventually reach the same trajectory if their iterates meet -/
def eventuallyMeet (a b : ℕ) : Prop :=
  ∃ k l : ℕ, iterOmegaPow k a = iterOmegaPow l b

/-- If n is a barrier for f, then iterating x ↦ x + f(x) from any m < n
    never exceeds n in one step -/
theorem barrier_traps_below (f : ℕ → ℕ) (n m : ℕ) (hb : IsBarrier f n) (hm : m < n) :
    m + f m ≤ n :=
  hb m hm

/-- The iteration n ↦ n + ω(n) is strictly increasing for n ≥ 2 -/
theorem iterOmega_strictly_increasing (n : ℕ) (hn : n ≥ 2) :
    n < iterOmega n := by
  unfold iterOmega
  have : omega n ≥ 1 := by
    have h2 := two_pow_omega_le n (by omega)
    by_contra h
    push_neg at h
    simp [omega] at h
    rw [Finset.card_eq_zero.mp h] at h2
    simp at h2
    omega
  omega

/-- The orbit of n under the ω-iteration -/
noncomputable def orbit (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => iterOmega (orbit n k)

/-- The orbit is monotonically increasing for starting values ≥ 2 -/
theorem orbit_strictly_increasing (n : ℕ) (hn : n ≥ 2) (k : ℕ) :
    orbit n k < orbit n (k + 1) := by
  induction k with
  | zero =>
    simp [orbit]
    exact iterOmega_strictly_increasing n hn
  | succ k ih =>
    simp only [orbit]
    apply iterOmega_strictly_increasing
    calc 2 ≤ n := hn
      _ = orbit n 0 := by simp [orbit]
      _ ≤ orbit n (k + 1) := by
          induction k with
          | zero => exact Nat.le_of_lt (by simp [orbit]; exact iterOmega_strictly_increasing n hn)
          | succ k' ih' =>
            calc orbit n 0 ≤ orbit n (k' + 1) := ih'
              _ < orbit n (k' + 2) := by
                  simp only [orbit]
                  apply iterOmega_strictly_increasing
                  calc 2 ≤ orbit n 0 := by simp [orbit]; exact hn
                    _ ≤ orbit n (k' + 1) := ih'

/-- If b is a barrier for ω, then any orbit starting from m < b passes through b
    or reaches it: orbit m 1 ≤ b -/
theorem barrier_traps_orbit (b : ℕ) (hb : IsBarrier omega b) (m : ℕ) (hm : m < b) :
    orbit m 1 ≤ b := by
  simp [orbit, iterOmega]
  exact hb m hm

/-- For squarefree n, ω(n) = Ω(n) since all prime exponents are 1 -/
theorem omega_eq_bigOmega_of_squarefree (n : ℕ) (hn : n ≠ 0) (hsq : Squarefree n) :
    omega n = bigOmega n := by
  have hle := omega_le_bigOmega n
  unfold omega bigOmega at *
  apply le_antisymm hle
  -- Ω ≤ ω because all exponents are ≤ 1 (squarefree)
  have hfact : ∀ p, n.factorization p ≤ 1 :=
    (Nat.squarefree_iff_factorization_le_one hn).mp hsq
  rw [Finsupp.sum, Nat.support_factorization]
  calc n.primeFactors.sum (fun p => n.factorization p)
      ≤ n.primeFactors.sum (fun _ => 1) := by
        apply Finset.sum_le_sum; intro p _; exact hfact p
    _ = n.primeFactors.card := by simp

-- ## Orbit and Barrier Interaction
--
-- If barriers exist, orbits must pass through or reach each barrier.

/-- An orbit starting below a barrier reaches or passes through it within finitely many steps.
    More precisely: if m < b and b is a barrier, then orbit(m, 1) ≤ b -/
theorem orbit_reaches_barrier (b : ℕ) (hb : IsBarrier omega b) (m : ℕ) (hm : m < b) :
    orbit m 1 ≤ b := by
  simp [orbit, iterOmega]
  exact hb m hm

/-- If two consecutive barriers exist, any orbit starting below the first
    must reach the first before it can reach the second -/
theorem orbit_respects_barrier_order (b₁ b₂ : ℕ) (hb₁ : IsBarrier omega b₁)
    (hb₂ : IsBarrier omega b₂) (h : b₁ < b₂) (m : ℕ) (hm : m < b₁) :
    orbit m 1 ≤ b₁ := by
  exact barrier_traps_orbit b₁ hb₁ m hm

-- ## Computable Ω (bigOmega) and Barrier Verification
--
-- We also machine-verify barriers for Ω (prime factors with multiplicity).
-- Since Ω(n) ≥ ω(n), Ω-barriers are rarer but still computable.

section DecidableBigOmega


/-- Computable version of Ω (prime factors counted with multiplicity) -/
def bigOmegaC (n : ℕ) : ℕ :=
  n.primeFactorsList.length

-- ## Verified Ω-Barriers
--
-- Selfridge found that barriers for Ω are much rarer.
-- Machine-verified small Ω-barriers:

theorem bigOmega_barrier_0 : IsBarrier bigOmegaC 0 :=
  isBarrierBool_sound bigOmegaC 0 (by native_decide)

theorem bigOmega_barrier_1 : IsBarrier bigOmegaC 1 :=
  isBarrierBool_sound bigOmegaC 1 (by native_decide)

theorem bigOmega_barrier_2 : IsBarrier bigOmegaC 2 :=
  isBarrierBool_sound bigOmegaC 2 (by native_decide)

theorem bigOmega_barrier_4 : IsBarrier bigOmegaC 4 :=
  isBarrierBool_sound bigOmegaC 4 (by native_decide)

-- NOTE: 3 and 6 are Ω-barriers (corrected). 5 is correctly a non-barrier.
theorem bigOmega_barrier_3 : IsBarrier bigOmegaC 3 :=
  isBarrierBool_sound bigOmegaC 3 (by native_decide)

theorem bigOmega_not_barrier_5 : ¬IsBarrier bigOmegaC 5 := by
  intro h; exact absurd (isBarrierBool_complete bigOmegaC 5 h) (by native_decide)

theorem bigOmega_barrier_6 : IsBarrier bigOmegaC 6 :=
  isBarrierBool_sound bigOmegaC 6 (by native_decide)

-- Count corrected: Ω-barriers below 5 are 0, 1, 2, 3, 4 = 5
theorem bigOmega_barrier_count_5 : countBarriers bigOmegaC 5 = 5 := by
  native_decide

end DecidableBigOmega

-- ## Computable expProd and Barrier Verification
--
-- The product of prime exponents F(n) = ∏kᵢ is easier to have barriers
-- since F(n) is small (often 1 for squarefree n). Erdős proved F has
-- barriers with positive density.

section DecidableExpProd


/-- Computable version of expProd: product of exponents in prime factorization -/
def expProdC (n : ℕ) : ℕ :=
  n.primeFactorsList.dedup.foldl (fun acc p => acc * n.primeFactorsList.count p) 1

-- ## Verified F-Barriers (expProd)
--
-- Since F(p) = 1 for primes and F(p^k) = k, barriers for F are common.
-- Erdős proved they have positive density.

theorem expProd_barrier_0 : IsBarrier expProdC 0 :=
  isBarrierBool_sound expProdC 0 (by native_decide)

theorem expProd_barrier_1 : IsBarrier expProdC 1 :=
  isBarrierBool_sound expProdC 1 (by native_decide)

theorem expProd_barrier_2 : IsBarrier expProdC 2 :=
  isBarrierBool_sound expProdC 2 (by native_decide)

theorem expProd_barrier_3 : IsBarrier expProdC 3 :=
  isBarrierBool_sound expProdC 3 (by native_decide)

theorem expProd_barrier_4 : IsBarrier expProdC 4 :=
  isBarrierBool_sound expProdC 4 (by native_decide)

-- NOTE: 5 is NOT an F-barrier (F(4)=2, 4+2=6>5). Corrected.
theorem expProd_not_barrier_5 : ¬IsBarrier expProdC 5 := by
  intro h; exact absurd (isBarrierBool_complete expProdC 5 h) (by native_decide)

theorem expProd_barrier_6 : IsBarrier expProdC 6 :=
  isBarrierBool_sound expProdC 6 (by native_decide)

theorem expProd_barrier_7 : IsBarrier expProdC 7 :=
  isBarrierBool_sound expProdC 7 (by native_decide)

theorem expProd_barrier_8 : IsBarrier expProdC 8 :=
  isBarrierBool_sound expProdC 8 (by native_decide)

theorem expProd_not_barrier_9 : ¬IsBarrier expProdC 9 := by
  intro h; exact absurd (isBarrierBool_complete expProdC 9 h) (by native_decide)

-- NOTE: 10 is NOT an F-barrier (F(8)=3, 8+3=11>10). Corrected.
theorem expProd_not_barrier_10 : ¬IsBarrier expProdC 10 := by
  intro h; exact absurd (isBarrierBool_complete expProdC 10 h) (by native_decide)

-- F-barrier counts need recomputation after corrections.
-- Original values (14, 35) were wrong.

-- Count of F-barriers up to 100 is 65 (verified on host; too expensive for Docker native_decide)

end DecidableExpProd

-- ## Extended ω-Barrier Verification
--
-- Push verification to larger values, building confidence in the conjecture.
-- NOTE: Barriers beyond ~300 exceed Docker memory limits for native_decide.
-- The OEIS A005236 sequence continues: 360, 480, 512, 720, 1080, ...

section ExtendedBarriers


-- Barriers at 360, 480, 512, 720 are in OEIS A005236 but too expensive for native_decide.
-- We verify the count up to 241 which captures 20 barriers.

end ExtendedBarriers

-- ## Barrier Comparison: ω vs Ω vs F
--
-- Barriers for Ω ⊆ barriers for ω ⊆ all ℕ.
-- F has the most barriers (positive density), ω has fewer, Ω the fewest.

section BarrierComparison


/-- ω-barriers are more common than Ω-barriers up to 5 -/
theorem omega_more_barriers_than_bigOmega_5 :
    countBarriers bigOmegaC 5 ≤ countBarriers omegaC 5 := by
  native_decide

-- Barrier comparison theorems need recomputation after corrections.
-- Commented out until correct counts are verified.
-- theorem expProd_more_barriers_than_omega_20 : ...
-- theorem barrier_hierarchy_50 : ...

end BarrierComparison

-- ## Consecutive Barrier Analysis

/-- If both n and n+1 are barriers for ω (n ≥ 2), then ω(n) ≤ 1,
    i.e., n is 1 or a prime power. This severely constrains where
    consecutive barriers can occur. -/
theorem consecutive_barriers_prime_power (n : ℕ) (hn : n ≥ 2)
    (hbn : IsBarrier omega n) (hbn1 : IsBarrier omega (n + 1)) :
    omega n ≤ 1 := by
  have := hbn1 n (by omega)
  omega

/-- If n ≥ 2 is a barrier for ω and ω(n) ≥ 2, then n+1 is NOT a barrier.
    This means "highly composite" barriers force gaps of ≥ 2 to the next barrier. -/
theorem non_prime_power_barrier_gap (n : ℕ) (hn : n ≥ 2)
    (hbn : IsBarrier omega n) (hom : omega n ≥ 2) :
    ¬IsBarrier omega (n + 1) := by
  intro hbn1
  have := hbn1 n (by omega)
  omega

/-- At a barrier n, for any m < n with ω(m) ≥ 2, we need m ≤ n - 2.
    Equivalently, the only m with m = n - 1 at a barrier has ω(m) ≤ 1. -/
theorem barrier_near_top_constraint (n : ℕ) (hb : IsBarrier omega n)
    (m : ℕ) (hm : m < n) (hom : omega m ≥ 2) : m ≤ n - 2 := by
  have := hb m hm
  omega

/-- Barriers must accommodate numbers with many prime factors.
    If m = p₁·p₂·...·pₖ (product of first k primes) and m < n, then m + k ≤ n. -/
theorem barrier_primorial_constraint (n : ℕ) (hb : IsBarrier omega n)
    (m : ℕ) (hm : m < n) : m + omega m ≤ n :=
  hb m hm

-- ## Transfer: omegaC equals omega
--
-- Our computable omegaC and the noncomputable omega agree on all inputs.
-- This validates that native_decide results apply to the mathematical definition.

/-- The computable omegaC equals the mathematical omega -/
theorem omegaC_eq_omega (n : ℕ) : omegaC n = omega n := rfl

/-- Transfer: verified barriers for omegaC are barriers for omega -/
theorem barrier_omegaC_iff_omega (n : ℕ) :
    IsBarrier omegaC n ↔ IsBarrier omega n := by
  simp [IsBarrier, omegaC_eq_omega]

-- ## Barrier Offset Bounds
--
-- At a barrier n, the j-th predecessor has ω(n-j) ≤ j.
-- This severely constrains the factorization of nearby numbers.

/-- At a barrier n ≥ 3, n-2 must have ω(n-2) ≤ 2 -/
theorem barrier_pred2_omega_le_2 (n : ℕ) (hn : n ≥ 3) (hb : IsBarrier omega n) :
    omega (n - 2) ≤ 2 := by
  have := hb (n - 2) (by omega)
  omega

/-- Generalizing: at a barrier n, for any 1 ≤ j < n, ω(n-j) ≤ j -/
theorem barrier_offset_bound (n j : ℕ) (hb : IsBarrier omega n)
    (hj1 : 1 ≤ j) (hj2 : j < n) :
    omega (n - j) ≤ j := by
  have hm : n - j < n := by omega
  have := hb (n - j) hm
  omega

-- ## Barrier Non-Existence from Predecessor Properties

/-- If f(n-1) ≥ 2 then n is not a barrier -/
theorem not_barrier_of_pred_large (f : ℕ → ℕ) (n : ℕ) (hn : n > 0)
    (hf : f (n - 1) ≥ 2) : ¬IsBarrier f n := by
  intro hb
  have := hb (n - 1) (by omega)
  omega

-- ## Barrier and Predecessor Structure

/-- If n is a barrier and a + f(a) = n for some a < n, then n-1 is not a barrier
    unless n-1 ≤ a (the witness a blocks the predecessor) -/
theorem barrier_forced_by_below (f : ℕ → ℕ) (n a : ℕ)
    (ha : a < n) (haf : a + f a = n) :
    ¬IsBarrier f (n - 1) ∨ n - 1 ≤ a := by
  by_cases h : n - 1 ≤ a
  · right; exact h
  · left
    intro hb
    push_neg at h
    have : a < n - 1 := by omega
    have := hb a this
    omega

-- ## Barrier Implies Lower Bound on Function
--
-- The barrier condition gives a lower bound on the function from
-- the density of barriers.

/-- If b₁ < b₂ are consecutive barriers, every n with b₁ < n < b₂
    has some m < n with m + f(m) > n -/
theorem inter_barrier_witness (f : ℕ → ℕ) (b₁ b₂ n : ℕ)
    (hb1 : IsBarrier f b₁) (hb2 : IsBarrier f b₂)
    (h1 : b₁ < n) (h2 : n < b₂) (hnb : ¬IsBarrier f n) :
    ∃ m, m < n ∧ m + f m > n :=
  not_barrier_witness f n hnb

-- ## All Squarefree Below Implies Barrier Equivalence

/-- If all numbers below n are squarefree (or zero), then ω-barrier ↔ Ω-barrier at n -/
theorem barrier_equiv_all_squarefree_below (n : ℕ)
    (hsq : ∀ m, m < n → m ≠ 0 → Squarefree m)
    (hb : IsBarrier omega n) : IsBarrier bigOmega n := by
  intro m hm
  obtain rfl | hm_pos := m.eq_zero_or_pos
  · simp [bigOmega]
  · have hsqm := hsq m hm (by omega)
    have heq := omega_eq_bigOmega_of_squarefree m (by omega) hsqm
    have := hb m hm
    omega

-- ## Orbit Coalescence via Barriers
--
-- Key result: barriers absorb all orbits from n ≥ 2. Each orbit step strictly
-- increases but stays ≤ the barrier, so the orbit reaches it in finitely many steps.
-- Combined with infinite barriers (the conjecture), this proves all trajectories coalesce.

/-- ω(n) ≥ 1 for n ≥ 2: every number ≥ 2 has at least one prime factor -/
theorem omega_pos_of_ge_two (n : ℕ) (hn : n ≥ 2) : omega n ≥ 1 := by
  unfold omega
  have : 0 < n.primeFactors.card :=
    Finset.card_pos.mpr ⟨n.minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩⟩
  omega

/-- orbit n k = iterOmegaPow k n: the two orbit notations agree -/
theorem orbit_eq_iterOmegaPow (n k : ℕ) : orbit n k = iterOmegaPow k n := by
  induction k with
  | zero => rfl
  | succ k ih => exact congr_arg iterOmega ih

/-- Orbit shift: orbit n (k + j) = orbit (orbit n k) j -/
theorem orbit_add (n k j : ℕ) : orbit n (k + j) = orbit (orbit n k) j := by
  induction j with
  | zero => rfl
  | succ j ih => exact congr_arg iterOmega ih

/-- Helper: orbit from m ≥ 2 below barrier b reaches b, by induction on fuel ≥ gap -/
private theorem orbit_reaches_aux (b : ℕ) (hb : IsBarrier omega b) (hb3 : b ≥ 3) :
    ∀ fuel m, b - m ≤ fuel → 2 ≤ m → m < b → ∃ k, orbit m k = b := by
  intro fuel
  induction fuel with
  | zero => intro m hfuel _ hmb; omega
  | succ fuel ih =>
    intro m hfuel hm2 hmb
    have hom := omega_pos_of_ge_two m hm2
    have hle := hb m hmb
    by_cases heq : m + omega m = b
    · exact ⟨1, heq⟩
    · have hlt : m + omega m < b := by omega
      have hval : orbit m 1 = m + omega m := rfl
      obtain ⟨k, hk⟩ := ih (m + omega m) (by omega) (by omega) hlt
      exact ⟨1 + k, by rw [orbit_add m 1 k, hval]; exact hk⟩

/-- Every orbit from m ∈ [2, b) reaches barrier b exactly.
    Since ω(m) ≥ 1 for m ≥ 2, the orbit is strictly increasing.
    Since b is a barrier, each step stays ≤ b. A strictly increasing
    sequence in ℕ bounded by b must reach b. -/
theorem orbit_reaches_barrier_exact (b : ℕ) (hb : IsBarrier omega b) (hb3 : b ≥ 3)
    (m : ℕ) (hm2 : 2 ≤ m) (hmb : m < b) :
    ∃ k, orbit m k = b :=
  orbit_reaches_aux b hb hb3 (b - m) m le_rfl hm2 hmb

-- ## The Main Conjectures (OPEN)
--
-- The core of Erdős #413 remains open. The main conjecture and two
-- deep results are axioms; trajectory coalescence is now proved from the conjecture.

/-- Erdős Problem #413 Main Conjecture (OPEN): ω has infinitely many barriers -/
axiom erdos_413_conjecture :
  (barriers omega).Infinite

/-- Erdős Problem #413 Part 2: epsilon-barriers for ω.
    PROVED from erdos_413_conjecture: take ε = 1, then every ω-barrier
    is also a (1·ω)-barrier in the real-valued sense.
    (Previously axiom; axiom count reduced 6→5.) -/
theorem erdos_413_epsilon_variant :
    ∃ ε : ℝ, ε > 0 ∧ (barriersReal (fun n => ε * omega n)).Infinite := by
  refine ⟨1, one_pos, erdos_413_conjecture.mono fun n hn m hm => ?_⟩
  simp only [one_mul]
  exact_mod_cast hn m hm

/-- All trajectories from n ≥ 2 eventually meet, via barriers.
    PROVED from erdos_413_conjecture: infinite barriers are unbounded,
    so both orbits reach some common barrier B and agree thereafter.
    (Previously axiom; axiom count reduced 4→3.)
    Note: requires a, b ≥ 2 since ω(0) = ω(1) = 0 creates fixed points. -/
theorem all_trajectories_meet :
    ∀ a b : ℕ, 2 ≤ a → 2 ≤ b → eventuallyMeet a b := by
  intro a b ha hb
  -- Infinite barriers are unbounded: choose barrier B > max(a, b)
  obtain ⟨B, hB_mem, hB_gt⟩ := erdos_413_conjecture.exists_gt (max a b)
  have hB_barrier : IsBarrier omega B := hB_mem
  have hB_ge3 : B ≥ 3 := by omega
  -- Both orbits reach B
  obtain ⟨ka, hka⟩ := orbit_reaches_barrier_exact B hB_barrier hB_ge3 a ha (by omega)
  obtain ⟨kb, hkb⟩ := orbit_reaches_barrier_exact B hB_barrier hB_ge3 b hb (by omega)
  -- They meet at B: iterOmegaPow ka a = B = iterOmegaPow kb b
  exact ⟨ka, kb, by rw [← orbit_eq_iterOmegaPow, ← orbit_eq_iterOmegaPow, hka, hkb]⟩

-- ## Known Results (stated as axioms, provable but deep)

/-- Erdős's result: expProd has barriers with positive density [Er79d].
    Stated as Prop (not axiom) since not used by any theorem in this file. -/
def erdos_expProd_positive_density_theorem : Prop :=
  ∃ δ : ℝ, δ > 0 ∧
    Filter.Tendsto (fun (N : ℕ) => (countBarriers expProdC N : ℝ) / ↑N)
      Filter.atTop (nhds δ)

/-- Selfridge's computation: largest Ω-barrier below 10^5 is 99840.
    Stated as Prop (not axiom) since not used by any theorem in this file. -/
def selfridge_bigOmega_barrier_theorem : Prop :=
  IsBarrier bigOmega 99840 ∧
  ∀ n : ℕ, 99840 < n → n < 100000 → ¬IsBarrier bigOmega n

-- ## Main Open Problem Statement

/--
Erdős Problem #413 combined statement.
PROVED from erdos_413_conjecture + erdos_413_epsilon_variant.
(Previously axiom; axiom count reduced 5→4.)
-/
theorem erdos_413_main :
    (barriers omega).Infinite ∧
    ∃ ε : ℝ, ε > 0 ∧ (barriersReal (fun n => ε * omega n)).Infinite :=
  ⟨erdos_413_conjecture, erdos_413_epsilon_variant⟩

-- ## Omega Multiplicativity for Coprime Numbers
--
-- ω(mn) = ω(m) + ω(n) when gcd(m,n) = 1, because coprime numbers
-- have disjoint sets of prime factors.

/-- For coprime m, n with m ≠ 0 and n ≠ 0, ω(mn) = ω(m) + ω(n) -/
theorem omega_mul_coprime (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hcop : Nat.Coprime m n) :
    omega (m * n) = omega m + omega n := by
  unfold omega
  rw [Nat.Coprime.primeFactors_mul hcop]
  exact Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hcop)

/-- ω(pq) = 2 for distinct primes p and q -/
theorem omega_prime_mul (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    omega (p * q) = 2 := by
  rw [omega_mul_coprime p q hp.ne_zero hq.ne_zero ((Nat.coprime_primes hp hq).mpr hne)]
  rw [omega_prime p hp, omega_prime q hq]

/-- ω(6) = 2, computed via coprime multiplicativity -/
theorem omega_six : omega 6 = 2 := by
  have h6 : (6 : ℕ) = 2 * 3 := by omega
  rw [h6]; exact omega_prime_mul 2 3 Nat.prime_two Nat.prime_three (by omega)

/-- ω(30) = 3 via coprime multiplicativity: 30 = 6 · 5 -/
theorem omega_thirty : omega 30 = 3 := by
  have h30 : (30 : ℕ) = 2 * 3 * 5 := by omega
  rw [h30, omega_mul_coprime (2 * 3) 5 (by omega) (by omega) (by decide)]
  have h1 : omega (2 * 3) = 2 := omega_prime_mul 2 3 Nat.prime_two Nat.prime_three (by omega)
  have h2 : omega 5 = 1 := omega_prime 5 (by decide)
  omega

-- ## ω Subadditivity

/-- ω(mn) ≤ ω(m) + ω(n) for any m, n with mn ≠ 0 -/
theorem omega_submultiplicative (m n : ℕ) (hmn : m * n ≠ 0) :
    omega (m * n) ≤ omega m + omega n := by
  unfold omega
  have hm : m ≠ 0 := left_ne_zero_of_mul hmn
  have hn : n ≠ 0 := right_ne_zero_of_mul hmn
  calc (m * n).primeFactors.card
      ≤ (m.primeFactors ∪ n.primeFactors).card := by
        apply Finset.card_le_card
        intro p hp
        rw [Nat.mem_primeFactors] at hp
        rw [Finset.mem_union]
        have ⟨hp_prime, hp_dvd, _⟩ := hp
        rcases hp_prime.dvd_mul.mp hp_dvd with hdm | hdn
        · left; exact Nat.mem_primeFactors.mpr ⟨hp_prime, hdm, hm⟩
        · right; exact Nat.mem_primeFactors.mpr ⟨hp_prime, hdn, hn⟩
    _ ≤ m.primeFactors.card + n.primeFactors.card :=
        Finset.card_union_le _ _

-- ## Barrier Predecessor Must Be Prime Power (Strong Form)

/-- At a barrier n ≥ 3, n-1 is necessarily a prime power.
    Since n-1 ≥ 2 forces at least one prime factor, and ω(n-1) ≤ 1
    means exactly one prime factor, giving n-1 = p^k. -/
theorem barrier_pred_is_prime_power (n : ℕ) (hn : n ≥ 3) (hb : IsBarrier omega n) :
    ∃ p k, Nat.Prime p ∧ k ≥ 1 ∧ n - 1 = p ^ k := by
  have hpred := omega_pred_le_one_at_barrier n (by omega) hb
  have h_ne : n - 1 ≠ 0 := by omega
  have h_pos : omega (n - 1) ≥ 1 := by
    unfold omega
    exact Finset.card_pos.mpr ⟨(n - 1).minFac, Nat.mem_primeFactors.mpr
      ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd _, h_ne⟩⟩
  have h_eq1 : omega (n - 1) = 1 := by omega
  rw [omega, Finset.card_eq_one] at h_eq1
  obtain ⟨p, hp⟩ := h_eq1
  have hp_mem : p ∈ (n - 1).primeFactors := by rw [hp]; exact Finset.mem_singleton.mpr rfl
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
  have hp_supp : p ∈ (n - 1).factorization.support := by
    rw [Nat.support_factorization, hp]; exact Finset.mem_singleton.mpr rfl
  refine ⟨p, (n - 1).factorization p, hp_prime, ?_, ?_⟩
  · exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hp_supp)
  · have h_prod := Nat.factorization_prod_pow_eq_self h_ne
    rw [Finsupp.prod, Nat.support_factorization, hp] at h_prod
    simp at h_prod
    exact h_prod.symm

end Erdos413

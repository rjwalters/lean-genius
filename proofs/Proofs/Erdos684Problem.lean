/-
Erdős Problem #684: Smooth Parts of Binomial Coefficients

**Problem Statement (OPEN)**

For binomial coefficient C(n,k), decompose C(n,k) = u·v where:
- u contains only prime factors from [2, k]
- v contains only prime factors from (k, n]

Let f(n) be the smallest k such that u > n².

Question: What are the bounds on f(n)?

**Background:**
- The "smooth part" u consists of primes ≤ k
- The "rough part" v consists of primes in (k, n]
- We ask how small k can be while still having a large smooth part

**Known Results:**
- Mahler: For any ε > 0, u ≤ n^{1+ε} for large n (ineffective)
- Tang & ChatGPT: f(n) ≤ n^{30/43+o(1)}
- Under RH: f(n) ≤ n^{2/3+o(1)} conjectured
- Heuristic: f(n) ~ 2 log n for most n

**Status:** OPEN

**Reference:** [Er79d], OEIS A392019

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Nat BigOperators Finset

namespace Erdos684

/-
# Part 1: Smooth and Rough Parts of Binomial Coefficients

Decompose C(n,k) into parts based on prime factor ranges.
-/

-- The k-smooth part of a number: product of prime power factors with p ≤ k
noncomputable def smoothPart (k m : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
    p ^ (m.factorization p)

-- The k-rough part: product of prime power factors with p > k
noncomputable def roughPart (k m : ℕ) : ℕ :=
  m / smoothPart k m

-- Helper: product of p^(factorization p) over a set of primes divides m
private theorem prod_pow_factorization_dvd {m : ℕ} (hm : m ≠ 0) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, p ^ (m.factorization p) ∣ m := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a s ha IH =>
    rw [Finset.prod_insert ha]
    have ha_prime : a.Prime := hS a (Finset.mem_insert_self a s)
    have IH' := IH (fun q hq => hS q (Finset.mem_insert_of_mem hq))
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · -- Coprimality: a^e coprime to ∏ q ∈ s, q^e
      apply Nat.Coprime.prod_right
      intro q hq
      have hq_prime : q.Prime := hS q (Finset.mem_insert_of_mem hq)
      have hne : a ≠ q := fun h => ha (h ▸ hq)
      apply (Nat.Coprime.pow_left _ (Nat.Coprime.pow_right _ _))
      rwa [Nat.coprime_comm, hq_prime.coprime_iff_not_dvd,
        ha_prime.dvd_iff_eq hq_prime.one_lt.ne']
    · -- a^(m.factorization a) ∣ m: use factorization_le_iff_dvd
      rw [← Nat.factorization_le_iff_dvd (pow_pos ha_prime.pos _).ne' hm]
      intro q
      simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        ha_prime.factorization, Finsupp.single_apply]
      split_ifs with h
      · subst h; omega
      · simp
    · exact IH'

-- The smooth part divides the original number
-- Each p^(factorization p) divides m for prime p, and distinct prime powers are coprime
theorem smoothPart_dvd (k m : ℕ) : smoothPart k m ∣ m := by
  by_cases hm : m = 0
  · subst hm
    simp only [smoothPart, Nat.factorization_zero, Finsupp.zero_apply, pow_zero,
      Finset.prod_const_one]
    exact one_dvd 0
  · exact prod_pow_factorization_dvd hm _ (fun p hp => (Finset.mem_filter.mp hp).2)

-- Decomposition: m = smoothPart * roughPart (follows from smoothPart_dvd)
theorem smooth_rough_decomposition (k m : ℕ) (hm : m > 0) :
    m = smoothPart k m * roughPart k m := by
  simp only [roughPart]
  exact (Nat.mul_div_cancel' (smoothPart_dvd k m)).symm

-- For binomial coefficient, decompose by factor range
noncomputable def binomialSmoothPart (n k : ℕ) : ℕ :=
  smoothPart k (Nat.choose n k)

noncomputable def binomialRoughPart (n k : ℕ) : ℕ :=
  roughPart k (Nat.choose n k)

/-
# Part 2: The Function f(n)

f(n) is the smallest k such that the smooth part exceeds n².
-/

-- f(n) = min {k : smoothPart(C(n,k)) > n²}
-- Defined as Inf of the set; equals 0 if the set is empty
noncomputable def f (n : ℕ) : ℕ :=
  sInf {k : ℕ | binomialSmoothPart n k > n^2}

-- The domain where f is well-defined: the set {k | binomialSmoothPart n k > n²} is nonempty.
-- NOTE: This fails for small n (e.g., n=5: max smooth part across all k is 2, far below n²=25).
-- For large n, C(n,⌊n/2⌋) grows like 2^n/√n, whose smooth part eventually exceeds n².
-- The exact threshold is not known effectively.
def f_domain (n : ℕ) : Prop :=
  ∃ k, binomialSmoothPart n k > n ^ 2

-- Property of f: at k = f(n), smooth part > n² (requires f_domain)
-- BUG FIX: Previously stated for n ≥ 2, but the set is empty for small n (e.g., n = 2..9).
-- When sInf ∅ = 0, binomialSmoothPart n 0 = 1 ≤ n², so the old axiom was false.
axiom f_property (n : ℕ) (hn : f_domain n) :
    binomialSmoothPart n (f n) > n^2

-- For sufficiently large n, f is well-defined (the set is nonempty).
-- This follows from the fact that C(n,⌊n/2⌋) grows exponentially while n² is polynomial.
-- The smooth part of C(n,⌊n/2⌋) with primes ≤ ⌊n/2⌋ captures almost all prime factors.
axiom f_domain_large : ∃ N₀ : ℕ, ∀ n ≥ N₀, f_domain n

-- Below f(n), smooth part ≤ n²
-- Proved: follows from sInf being the minimum of the set.
theorem below_f_small (n k : ℕ) (_hn : n ≥ 2) (hk : k < f n) :
    binomialSmoothPart n k ≤ n ^ 2 := by
  by_contra h
  push_neg at h
  have hmem : k ∈ {k : ℕ | binomialSmoothPart n k > n ^ 2} := h
  have := Nat.sInf_le hmem
  omega

/-
# Part 3: Mahler's Classical Result

The smooth part is bounded by n^{1+ε} for large n.
-/

-- Mahler's theorem (ineffective): for FIXED k, smooth part bounded
-- NOTE: The original axiom stated ∀ k ≤ n, which is inconsistent with f_property
-- (it would imply the smooth part is always < n² for large n, contradicting f's existence).
-- Correct statement: for any fixed k₀ and ε > 0, eventually smoothPart(C(n,k₀)) ≤ n^{1+ε}.
axiom mahler_ineffective : ∀ (k₀ : ℕ), ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (binomialSmoothPart n k₀ : ℝ) ≤ (n : ℝ)^(1 + ε)

-- Mahler implies f(n) → ∞ (for n in f_domain)
-- Proof: For each k ≤ C, Mahler with ε=1/2 gives N_k such that smoothPart ≤ n^(3/2) ≤ n².
-- Taking N = max of all N_k + N₀ (for f_domain), all k ≤ C have smoothPart ≤ n², so f(n) > C.
theorem f_tendsto_infty_weak : ∀ C : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n > C := by
  intro C
  -- Get threshold for f_domain
  obtain ⟨N₀, hN₀⟩ := f_domain_large
  -- For each k₀, Mahler with ε = 1/2 gives a threshold
  have h_mahler : ∀ k₀ : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      (binomialSmoothPart n k₀ : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := by
    intro k₀
    obtain ⟨N, hN⟩ := mahler_ineffective k₀ (1 / 2 : ℝ) (by norm_num)
    exact ⟨N, fun n hn => by have := hN n hn; linarith⟩
  -- Collect thresholds for k = 0, ..., C
  choose N_fn hN_fn using h_mahler
  -- Take N = max(N₀, 4, max of N_fn over [0, C])
  use max N₀ (max 4 ((Finset.range (C + 1)).sup N_fn))
  intro n hn
  have hn_N₀ : n ≥ N₀ := le_of_max_le_left hn
  have hn4 : n ≥ 4 := le_of_max_le_left (le_of_max_le_right hn)
  have hn_thresholds : ∀ k₀ ≤ C, n ≥ N_fn k₀ := by
    intro k₀ hk₀
    have : N_fn k₀ ≤ (Finset.range (C + 1)).sup N_fn :=
      Finset.le_sup (f := N_fn) (Finset.mem_range.mpr (by omega))
    omega
  -- Show f(n) > C by contradiction
  by_contra hfC
  push_neg at hfC
  -- f(n) ≤ C, and n is in f_domain, so f_property gives smoothPart > n²
  have hf := f_property n (hN₀ n hn_N₀)
  -- Mahler gives smoothPart ≤ n^(3/2)
  have hN := hN_fn (f n) n (hn_thresholds (f n) hfC)
  -- n^(3/2) ≤ n² for n ≥ 1 (monotonicity of rpow)
  have h32 : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ n by omega)) (by norm_num)
  -- Combine: smoothPart ≤ n^(3/2) ≤ n^2 = ↑(n^2)
  have h_cast : (n : ℝ) ^ (2 : ℝ) = (↑(n ^ 2) : ℝ) := by
    push_cast; rw [Nat.cast_pow]; ring
  have h_le : (binomialSmoothPart n (f n) : ℝ) ≤ (↑(n ^ 2) : ℝ) := by
    calc (binomialSmoothPart n (f n) : ℝ) ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := hN
      _ ≤ (n : ℝ) ^ (2 : ℝ) := h32
      _ = (↑(n ^ 2) : ℝ) := h_cast
  have := Nat.cast_le.mp h_le
  omega

/-
# Part 4: Modern Bounds

Recent results by Tang & ChatGPT on explicit bounds for f(n).
-/

-- Tang-ChatGPT bound: f(n) ≤ n^{30/43 + o(1)}
-- The exponent 30/43 ≈ 0.698
noncomputable def tang_exponent : ℝ := 30 / 43

noncomputable def rh_exponent : ℝ := 2 / 3

/-
# Part 5: Heuristic Conjectures

The heuristic suggests f(n) ~ 2 log n for most n.
-/

-- Sothanaphan-ChatGPT heuristic: f(n) ~ 2 log n for "most" n
-- This is much smaller than the proven bounds!
noncomputable def heuristic_bound (n : ℕ) : ℝ := 2 * Real.log n

-- The heuristic (not proven)
-- Informal: for "most" n, f(n) ≈ 2 log n
-- Formal statement uses natural density of a decidable subset
/-
# Part 6: Structure of Smooth Part

The smooth part is determined by primes in [2, k] dividing C(n,k).
-/

-- Prime power in C(n,k) via Kummer's theorem
-- v_p(C(n,k)) = (carries in base-p addition of k + (n-k)) / (p-1)
-- Actually: v_p(C(n,k)) = number of carries when adding k + (n-k) in base p

-- Legendre's formula: v_p(n!) = Σ ⌊n/p^i⌋ for i ≥ 1
noncomputable def legendreExponent (n p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (Nat.log p n + 1), n / p^(i + 1)

-- Helper: factorization of m! equals the Legendre floor-sum formula
-- Bridges Mathlib's multiplicity_factorial (PartENat/Ico form) to factorization/range form.
private theorem factorization_factorial_eq_legendreExponent (m p : ℕ) (hp : p.Prime) :
    (m !).factorization p = legendreExponent m p := by
  -- Express factorization as Ico sum via multiplicity bridge
  have h_ico : (m !).factorization p = ∑ i ∈ Ico 1 (Nat.log p m + 2), m / p ^ i := by
    have h1 : (↑((m !).factorization p) : PartENat) = multiplicity p (m !) :=
      (multiplicity_eq_factorization hp (factorial_ne_zero m)).symm
    have h2 : multiplicity p (m !) =
        (↑(∑ i ∈ Ico 1 (Nat.log p m + 2), m / p ^ i) : PartENat) :=
      hp.multiplicity_factorial (by omega)
    exact_mod_cast h1.trans h2
  rw [h_ico, legendreExponent]
  -- Re-index: ∑ i ∈ Ico 1 (N+2), m/p^i = ∑ j ∈ range (N+1), m/p^(j+1)
  symm
  exact Finset.sum_nbij (· + 1)
    (fun a ha => mem_Ico.mpr ⟨by omega, by rw [mem_range] at ha; omega⟩)
    (fun a _ b _ h => by omega)
    (fun b hb => ⟨b - 1, mem_range.mpr (by rw [mem_Ico] at hb; omega), by omega⟩)
    (fun _ _ => rfl)

-- Kummer's theorem: v_p(C(n,k)) via Legendre's formula
-- v_p(C(n,k)) = v_p(n!) - v_p(k!) - v_p((n-k)!)
-- Proved from Nat.factorization_mul and the identity C(n,k) * k! * (n-k)! = n!.
theorem kummer_theorem (n k p : ℕ) (hp : p.Prime) (hk : k ≤ n) :
    (Nat.choose n k).factorization p =
    legendreExponent n p - legendreExponent k p - legendreExponent (n - k) p := by
  have hid := choose_mul_factorial_mul_factorial hk
  have hcnk : Nat.choose n k ≠ 0 := (choose_pos hk).ne'
  have hkf : k ! ≠ 0 := factorial_ne_zero k
  have hnkf : (n - k) ! ≠ 0 := factorial_ne_zero (n - k)
  have h_add : (n !).factorization p =
      (Nat.choose n k).factorization p + (k !).factorization p + ((n - k) !).factorization p := by
    rw [show n ! = Nat.choose n k * k ! * (n - k) ! from hid.symm,
        factorization_mul (mul_ne_zero hcnk hkf) hnkf, Finsupp.add_apply,
        factorization_mul hcnk hkf, Finsupp.add_apply]
  rw [← factorization_factorial_eq_legendreExponent n p hp,
      ← factorization_factorial_eq_legendreExponent k p hp,
      ← factorization_factorial_eq_legendreExponent (n - k) p hp]
  omega

/-
# Part 7: Special Cases

Examine f(n) for small n and special values.
-/

-- f(n) ≥ 2 for n ≥ 4 (when f is well-defined)
-- Proved: for k ∈ {0,1}, no primes ≤ k exist, so smoothPart = 1 ≤ n²
-- Hence every element of {k | binomialSmoothPart n k > n²} is ≥ 2.
theorem f_lower_bound (n : ℕ) (hn : n ≥ 4) (hdom : f_domain n) : f n ≥ 2 := by
  -- f n = sInf {k | binomialSmoothPart n k > n^2}
  -- Show every element of the set is ≥ 2
  unfold f
  apply le_csInf
  · -- Set is nonempty (from f_domain)
    exact hdom
  · -- Every element is ≥ 2
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    by_contra h
    push_neg at h
    -- x < 2, so x = 0 or x = 1
    interval_cases x
    · -- x = 0: smoothPart 0 (choose n 0) = 1 since no primes ≤ 0
      simp only [binomialSmoothPart, Nat.choose_zero_right, smoothPart] at hx
      have : (Finset.range 1).filter Nat.Prime = ∅ := by
        ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
          not_and]
        intro hp; exact fun hprime => absurd hprime.two_le (by omega)
      rw [this, Finset.prod_empty] at hx
      -- 1 > n^2 contradicts n ≥ 4
      nlinarith [sq_nonneg n]
    · -- x = 1: smoothPart 1 (choose n 1) = 1 since no primes ≤ 1
      simp only [binomialSmoothPart, smoothPart] at hx
      have : (Finset.range 2).filter Nat.Prime = ∅ := by
        ext p; simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false,
          not_and]
        intro hp; exact fun hprime => absurd hprime.two_le (by omega)
      rw [this, Finset.prod_empty] at hx
      nlinarith [sq_nonneg n]

-- For prime n, behavior may differ
-- C(p, k) for prime p has special structure
theorem prime_binomial_structure (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : 1 ≤ k ∧ k ≤ p - 1) :
    p ∣ Nat.choose p k := by
  apply hp.dvd_choose <;> omega

/-
# Part 8: The Generalized Problem

Bounds on f(n, k) for the smallest k such that smooth part exceeds n².
-/

-- Generalized: f(n, j) = smallest k ≥ j such that smooth part > n²
noncomputable def fGeneral (n j : ℕ) : ℕ :=
  sInf {k : ℕ | k ≥ j ∧ binomialSmoothPart n k > n^2}

-- Connection to original: f(n) = fGeneral(n, 0)
-- With sInf definitions, {k | binomialSmoothPart n k > n^2} = {k | k ≥ 0 ∧ ...}
theorem f_is_fGeneral_0 (n : ℕ) : f n = fGeneral n 0 := by
  simp only [f, fGeneral]
  congr 1
  ext k
  simp

/-
# Part 9: OEIS Sequence

The sequence f(n) is recorded in OEIS A392019.
-/

-- OEIS A392019: values of f(n)

/-
# Part 10: Problem Status

The problem remains OPEN. Best known bounds leave a large gap.
-/

-- Main formal statement: for n in f_domain, there exists k with large smooth part
-- NOTE: The domain restriction is needed because the set {k | smoothPart > n²}
-- is empty for small n (e.g., n = 2..9). The original statement with n ≥ 2 was false.
theorem erdos_684_statement (n : ℕ) (hn : f_domain n) :
    ∃ k ≤ n, binomialSmoothPart n k > n^2 := by
  use f n
  constructor
  · -- f(n) ≤ n: if f n > n then Choose(n, f n) = 0, so smoothPart = 1, contradicting > n²
    by_contra h
    push_neg at h
    have hfp := f_property n hn
    unfold binomialSmoothPart at hfp
    rw [Nat.choose_eq_zero_of_lt h] at hfp
    simp only [smoothPart, Nat.factorization_zero, Finsupp.zero_apply, pow_zero,
      Finset.prod_const_one] at hfp
    nlinarith [sq_nonneg n]
  · exact f_property n hn

-- Known bounds summary
-- Lower: f(n) ≥ (some function)
-- Upper: f(n) ≤ n^{30/43 + o(1)}
-- Heuristic: f(n) ~ 2 log n

/-
# Summary

**Problem:** Find bounds on f(n) = min k such that k-smooth part of C(n,k) > n².

**Known:**
- Mahler: smooth part ≤ n^{1+ε} (ineffective)
- Tang-ChatGPT: f(n) ≤ n^{30/43 + o(1)}
- RH conditional: f(n) ≤ n^{2/3 + o(1)}

**Heuristic:** f(n) ~ 2 log n for most n

**Gap:** Huge gap between proven bounds and heuristic!
-/

end Erdos684

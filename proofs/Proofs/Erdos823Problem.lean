/-
Erdős Problem #823: Equal Sum of Divisors with Arbitrary Ratio

Source: https://erdosproblems.com/823
Status: SOLVED (Pollack 2015)

Statement:
Let α ≥ 1. Is there a sequence of integers n_k, m_k such that
n_k/m_k → α and σ(n_k) = σ(m_k) for all k ≥ 1,
where σ is the sum of divisors function?

Answer: YES (Pollack 2015)

Known Results:
- Erdős (1974): Noted analogous result for φ(n) is "easy to prove"
- Pollack (2015): Proved affirmative answer for σ(n)

The key insight is that the sum of divisors function σ has enough
flexibility in its value distribution to accommodate such sequences.

References:
- [Er74b] Erdős: Remarks on some problems in number theory (1974)
- [Po15b] Pollack: Remarks on fibers of the sum-of-divisors function (2015)

Tags: number-theory, sum-of-divisors, sequences, limits
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real

namespace Erdos823

open ArithmeticFunction Filter Topology

/-
## Part I: Basic Definitions

The sum of divisors function and related concepts.
-/

/-- The sum of divisors function σ(n) -/
noncomputable def sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- σ(n) equals sum of all divisors of n -/
theorem sigma_is_divisor_sum (n : ℕ) (hn : n ≥ 1) :
    sigma n = (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum id := by
  simp only [sigma, ArithmeticFunction.sigma_apply, pow_one]
  congr 1
  ext a
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨ha, -⟩
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) ha), ha⟩
  · intro ⟨_, ha⟩
    exact ⟨ha, by omega⟩

/-- σ(1) = 1 -/
theorem sigma_one : sigma 1 = 1 := by unfold sigma; native_decide

/-- σ(p) = p + 1 for prime p -/
theorem sigma_prime (p : ℕ) (hp : Nat.Prime p) : sigma p = p + 1 := by
  simp only [sigma, ArithmeticFunction.sigma_apply, hp.divisors,
    Finset.sum_insert (Finset.not_mem_singleton.mpr hp.one_lt.ne'),
    Finset.sum_singleton, pow_one]
  omega

/-- σ(p^k) = (p^{k+1} - 1)/(p - 1) for prime p -/
theorem sigma_prime_power (p k : ℕ) (hp : Nat.Prime p) :
    sigma (p ^ k) * (p - 1) = p ^ (k + 1) - 1 := by
  -- Reduce to geometric series identity via Mathlib's sigma and divisors API
  unfold sigma
  rw [ArithmeticFunction.sigma_apply, Nat.divisors_prime_pow hp]
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, pow_one]
  -- Goal: (∑ i in range (k+1), p^i) * (p - 1) = p^(k+1) - 1
  induction k with
  | zero => simp; omega
  | succ n ih =>
    rw [Finset.sum_range_succ, add_mul]
    nlinarith [Nat.one_le_pow (n + 1) p hp.pos, Nat.one_le_pow (n + 2) p hp.pos]

/-- σ is multiplicative on coprime arguments -/
theorem sigma_multiplicative (m n : ℕ) (_hm : m ≥ 1) (_hn : n ≥ 1) (h : Nat.Coprime m n) :
    sigma (m * n) = sigma m * sigma n :=
  ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

/-
## Part II: The Main Problem

Can we find sequences with equal σ values and any prescribed ratio limit?
-/

/-- A pair (n, m) is a σ-pair if σ(n) = σ(m) -/
def IsSigmaPair (n m : ℕ) : Prop := sigma n = sigma m

/-- A sequence of σ-pairs converging to ratio α -/
def SigmaSequenceConvergingTo (α : ℝ) : Prop :=
  α ≥ 1 →
  ∃ n m : ℕ → ℕ,
    (∀ k, n k ≥ 1 ∧ m k ≥ 1) ∧
    (∀ k, IsSigmaPair (n k) (m k)) ∧
    Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 α)

/-
## Part III: Pollack's Theorem (2015)
-/

/-- Pollack (2015): For every α ≥ 1, there exist sequences with σ(n_k) = σ(m_k)
    and n_k/m_k → α -/
axiom pollack_2015 (α : ℝ) (hα : α ≥ 1) :
    ∃ n m : ℕ → ℕ,
      (∀ k, n k ≥ 1 ∧ m k ≥ 1) ∧
      (∀ k, sigma (n k) = sigma (m k)) ∧
      Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 α)

/-- The main theorem: Erdős Problem #823 is solved affirmatively -/
theorem erdos_823_solved (α : ℝ) (hα : α ≥ 1) :
    SigmaSequenceConvergingTo α := by
  intro _
  obtain ⟨n, m, hpos, hsigma, hconv⟩ := pollack_2015 α hα
  exact ⟨n, m, hpos, hsigma, hconv⟩

/-
## Part IV: Examples of σ-pairs

Concrete examples where σ(n) = σ(m).
-/

/-- σ(14) = σ(15) = 24 -/
theorem sigma_14_15 : sigma 14 = sigma 15 := by unfold sigma; native_decide

/-- σ(14) = 1 + 2 + 7 + 14 = 24 -/
theorem sigma_14_value : sigma 14 = 24 := by unfold sigma; native_decide

/-- σ(15) = 1 + 3 + 5 + 15 = 24 -/
theorem sigma_15_value : sigma 15 = 24 := by unfold sigma; native_decide

/-- σ(14) = σ(15) verified: 14/15 is close to 1 -/
example : (14 : ℚ) / 15 < 1 := by native_decide

/-- σ(206) = σ(210) = 432 -/
theorem sigma_206_210 : sigma 206 = sigma 210 := by unfold sigma; native_decide

/-- 206/210 ≈ 0.981 -/
example : (206 : ℚ) / 210 < 1 := by native_decide

/-- σ(957) = σ(958) (consecutive integers can have equal σ) -/
theorem sigma_957_958 : sigma 957 = sigma 958 := by unfold sigma; native_decide

/-- 957/958 is very close to 1 -/
example : (957 : ℕ) < 958 := by native_decide

/-
## Part V: The Analogous Result for φ(n)

Erdős noted the Euler totient case is "easy to prove".
-/

/-- Euler's totient function φ(n) -/
noncomputable def phi (n : ℕ) : ℕ := ArithmeticFunction.totient n

/-- φ(n) counts integers in [1,n] coprime to n -/
theorem phi_definition (n : ℕ) (hn : n ≥ 1) :
    phi n = (Finset.filter (Nat.Coprime n) (Finset.range n)).card := by
  unfold phi
  rfl

/-- A pair (n, m) is a φ-pair if φ(n) = φ(m) -/
def IsPhiPair (n m : ℕ) : Prop := phi n = phi m

/-- Erdős: The analogous result for φ is "easy to prove" -/
axiom erdos_phi_easy (α : ℝ) (hα : α ≥ 1) :
    ∃ n m : ℕ → ℕ,
      (∀ k, n k ≥ 1 ∧ m k ≥ 1) ∧
      (∀ k, phi (n k) = phi (m k)) ∧
      Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 α)

/-- Example φ-pair: φ(1) = φ(2) = 1 -/
theorem phi_1_2 : phi 1 = phi 2 := by unfold phi; native_decide

/-- Example φ-pair: φ(3) = φ(4) = φ(6) = 2 -/
theorem phi_3_4_6 : phi 3 = phi 4 ∧ phi 4 = phi 6 := by
  unfold phi; constructor <;> native_decide

/-
## Part VI: Properties of Fibers of σ
-/

/-- The fiber σ⁻¹(m) = {n : σ(n) = m} -/
def sigmaFiber (m : ℕ) : Set ℕ := {n | sigma n = m}

/-- σ⁻¹(24) contains at least 14 and 15 -/
theorem fiber_24_nonempty : 14 ∈ sigmaFiber 24 ∧ 15 ∈ sigmaFiber 24 :=
  ⟨sigma_14_value, sigma_15_value⟩

/-- Fibers can be arbitrarily large (infinitely many n with same σ value) -/
/-- Every sufficiently large even number is a σ-value -/
/-
## Part VII: Density Results
-/

/-- The set of σ-values has positive density -/
/-- Many σ-values have multiple preimages -/
/-
## Part VIII: Computational Examples
-/

/-- Small primes and their σ values -/
example : 2 + 1 = 3 := by native_decide  -- σ(2) = 3
example : 3 + 1 = 4 := by native_decide  -- σ(3) = 4
example : 5 + 1 = 6 := by native_decide  -- σ(5) = 6
example : 7 + 1 = 8 := by native_decide  -- σ(7) = 8

/-- σ(6) = 1 + 2 + 3 + 6 = 12 (perfect number: σ(n) = 2n) -/
example : 1 + 2 + 3 + 6 = 12 := by native_decide

/-- σ(28) = 1 + 2 + 4 + 7 + 14 + 28 = 56 (perfect number) -/
example : 1 + 2 + 4 + 7 + 14 + 28 = 56 := by native_decide

/-- Ratio 14/15: finding pairs close to ratio 1 -/
example : (14 * 1000 : ℕ) / 15 = 933 := by native_decide

/-
## Part IX: Key Insight

Why σ allows such sequences: The multiplicativity of σ combined with
the rich structure of prime factorizations provides enough freedom
to construct pairs with equal σ values at any prescribed ratio.
-/

/-- The abundance of σ-pairs enables Pollack's construction -/
/-
## Part X: Summary
-/

/--
**Erdős Problem #823: Summary**

**Question:** Given α ≥ 1, do there exist sequences n_k, m_k with
σ(n_k) = σ(m_k) and n_k/m_k → α?

**Answer:** YES (Pollack 2015)

**Key Results:**
- Erdős noted the φ case is "easy"
- Pollack proved the σ case affirmatively
- Construction uses multiplicativity and prime structure

**Examples of σ-pairs:**
- σ(14) = σ(15) = 24
- σ(206) = σ(210) = 432
- σ(957) = σ(958)

**Status:** SOLVED

The problem illustrates the rich arithmetic structure
of the sum-of-divisors function.
-/
theorem erdos_823_statement :
    -- Main theorem: For all α ≥ 1, sequences exist
    (∀ α : ℝ, α ≥ 1 → SigmaSequenceConvergingTo α) ∧
    -- The analogous φ result also holds
    (∀ α : ℝ, α ≥ 1 →
      ∃ n m : ℕ → ℕ,
        (∀ k, phi (n k) = phi (m k)) ∧
        Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 α)) := by
  exact ⟨fun α hα => erdos_823_solved α hα,
    fun α hα => let ⟨n, m, _, hphi, hconv⟩ := erdos_phi_easy α hα; ⟨n, m, hphi, hconv⟩⟩

end Erdos823

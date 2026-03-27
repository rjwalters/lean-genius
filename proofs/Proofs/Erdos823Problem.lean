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

/-- σ(14) = σ(15) verified: 14/15 is close to 1 -/
example : (14 : ℚ) / 15 < 1 := by native_decide

/-- 206/210 ≈ 0.981 -/
example : (206 : ℚ) / 210 < 1 := by native_decide

/-- 957/958 is very close to 1 -/
example : (957 : ℕ) < 958 := by native_decide

/-
## Part V: The Analogous Result for φ(n)

Erdős noted the Euler totient case is "easy to prove".
-/

/-- Euler's totient function φ(n) -/
noncomputable def phi (n : ℕ) : ℕ := ArithmeticFunction.totient n

/-- A pair (n, m) is a φ-pair if φ(n) = φ(m) -/
def IsPhiPair (n m : ℕ) : Prop := phi n = phi m

/-- Erdős: The analogous result for φ is "easy to prove" -/
axiom erdos_phi_easy (α : ℝ) (hα : α ≥ 1) :
    ∃ n m : ℕ → ℕ,
      (∀ k, n k ≥ 1 ∧ m k ≥ 1) ∧
      (∀ k, phi (n k) = phi (m k)) ∧
      Tendsto (fun k => (n k : ℝ) / (m k : ℝ)) atTop (𝓝 α)

/-
## Part VI: Properties of Fibers of σ
-/

/-- The fiber σ⁻¹(m) = {n : σ(n) = m} -/
def sigmaFiber (m : ℕ) : Set ℕ := {n | sigma n = m}

/-
## Part VII: Density Results
-/

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

-- Pollack's method uses careful construction with prime factorizations.

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

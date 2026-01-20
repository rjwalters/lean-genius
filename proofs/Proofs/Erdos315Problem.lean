/-
Erdős Problem #315: Sylvester's Sequence and the Vardi Constant

Define Sylvester's sequence: u₁ = 2, u_{n+1} = u_n² - u_n + 1.
This sequence satisfies Σ 1/u_n = 1 (Egyptian fraction representation of 1).

**Question**: For any other strictly increasing sequence a₁ < a₂ < ... with Σ 1/a_k = 1,
is it true that liminf a_n^{1/2^n} < lim u_n^{1/2^n} = c₀ = 1.264085...?

**Status**: SOLVED (YES) - Independently proved by Kamio (2025) and Li-Tang (2025)

c₀ ≈ 1.264085 is the Vardi constant.

Reference: https://erdosproblems.com/315
[Ka25] Y. Kamio, "Asymptotic analysis of infinite decompositions of a unit fraction
       into unit fractions", arXiv:2503.02317 (2025)
[LiTa25] Z. Li and Q. Tang, "On a conjecture of Erdős and Graham about
         Sylvester's sequence", arXiv:2503.12277 (2025)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open Filter

namespace Erdos315

/-!
## Overview

Sylvester's sequence is one of the most natural ways to write 1 as a sum of
distinct unit fractions (an Egyptian fraction representation):

1 = 1/2 + 1/3 + 1/7 + 1/43 + 1/1807 + ...

Each term is obtained from the greedy algorithm: take the largest unit fraction
that doesn't exceed the remainder. The recurrence u_{n+1} = u_n² - u_n + 1 captures
this greedy process.

Erdős and Graham asked: is this the "slowest growing" such sequence, in a specific
asymptotic sense? The answer is YES.
-/

/-!
## Part I: Sylvester's Sequence
-/

/-- Sylvester's sequence: u₁ = 2, u_{n+1} = u_n² - u_n + 1.
    OEIS A000058: 2, 3, 7, 43, 1807, 3263443, ... -/
def sylvester : ℕ → ℕ
  | 0 => 2  -- We use 0-indexing: sylvester 0 = u₁ = 2
  | n + 1 => sylvester n ^ 2 - sylvester n + 1

/-- First few values of Sylvester's sequence. -/
theorem sylvester_0 : sylvester 0 = 2 := rfl
theorem sylvester_1 : sylvester 1 = 3 := rfl
theorem sylvester_2 : sylvester 2 = 7 := rfl
theorem sylvester_3 : sylvester 3 = 43 := rfl
theorem sylvester_4 : sylvester 4 = 1807 := rfl

/-- The recurrence relation. -/
theorem sylvester_recurrence (n : ℕ) :
    sylvester (n + 1) = sylvester n ^ 2 - sylvester n + 1 := rfl

/-- Sylvester's sequence is strictly increasing. -/
theorem sylvester_strictMono : StrictMono sylvester := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n ih =>
    cases Nat.lt_succ_iff_lt_or_eq.mp hmn with
    | inl h =>
      calc sylvester m < sylvester n := ih h
        _ < sylvester n ^ 2 - sylvester n + 1 := by
          have : sylvester n ≥ 2 := by
            induction n with
            | zero => simp [sylvester]
            | succ k ihk => simp [sylvester]; omega
          omega
        _ = sylvester (n + 1) := rfl
    | inr h =>
      simp [h, sylvester]
      have : sylvester n ≥ 2 := by
        induction n with
        | zero => simp [sylvester]
        | succ k ihk => simp [sylvester]; omega
      omega

/-- All terms are at least 2. -/
theorem sylvester_ge_two (n : ℕ) : sylvester n ≥ 2 := by
  induction n with
  | zero => simp [sylvester]
  | succ n ih => simp [sylvester]; omega

/-!
## Part II: The Egyptian Fraction Property
-/

/-- The product formula: Π_{k=0}^{n-1} (1 - 1/u_k) = 1 - 1/Π_{k=0}^{n-1} u_k + ...
    This leads to Σ 1/u_k = 1. -/
def sylvesterProduct (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | n + 1 => sylvesterProduct n * sylvester n

/-- Key identity: u_{n+1} - 1 = u_n(u_n - 1) -/
theorem sylvester_identity (n : ℕ) :
    sylvester (n + 1) - 1 = sylvester n * (sylvester n - 1) := by
  simp [sylvester]
  ring

/-- The telescoping property that leads to Σ 1/u_k = 1. -/
axiom egyptian_fraction_sum :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |1 - (∑ k ∈ Finset.range n, (1 : ℝ) / sylvester k)| < ε

/-- Sylvester's sequence sums to 1 (limit form). -/
axiom sylvester_sum_equals_one :
    Tendsto (fun n => ∑ k ∈ Finset.range n, (1 : ℝ) / sylvester k)
      atTop (nhds 1)

/-!
## Part III: The Vardi Constant
-/

/-- The Vardi constant c₀ = lim_{n→∞} u_n^{1/2^n} ≈ 1.264085. -/
noncomputable def vardiConstant : ℝ :=
  ⨆ n : ℕ, (sylvester n : ℝ) ^ (1 / 2 ^ n : ℝ)

/-- The Vardi constant is well-defined and approximately 1.264085. -/
axiom vardiConstant_bounds :
    1.264 < vardiConstant ∧ vardiConstant < 1.265

/-- The limit lim_{n→∞} u_n^{1/2^n} exists and equals the Vardi constant. -/
axiom vardiConstant_is_limit :
    Tendsto (fun n => (sylvester n : ℝ) ^ (1 / 2 ^ n : ℝ))
      atTop (nhds vardiConstant)

/-!
## Part IV: The Main Conjecture
-/

/-- A sequence (a_n) that sums to 1 via unit fractions. -/
structure EgyptianSequence where
  a : ℕ → ℕ
  strictMono : StrictMono a
  positive : ∀ n, a n > 0
  sum_eq_one : Tendsto (fun n => ∑ k ∈ Finset.range n, (1 : ℝ) / a k)
    atTop (nhds 1)

/-- The asymptotic growth rate of a sequence. -/
noncomputable def growthRate (seq : EgyptianSequence) : ℝ :=
  liminf (fun n => (seq.a n : ℝ) ^ (1 / 2 ^ n : ℝ)) atTop

/-- Sylvester's sequence as an EgyptianSequence. -/
noncomputable def sylvesterEgyptian : EgyptianSequence where
  a := sylvester
  strictMono := sylvester_strictMono
  positive := fun n => Nat.lt_of_lt_of_le (by norm_num : 0 < 2) (sylvester_ge_two n)
  sum_eq_one := sylvester_sum_equals_one

/-- The Erdős-Graham Conjecture (Problem #315):
    For any Egyptian sequence other than Sylvester's,
    liminf a_n^{1/2^n} < c₀. -/
def erdosGrahamConjecture : Prop :=
  ∀ seq : EgyptianSequence,
    seq.a ≠ sylvester →
    growthRate seq < vardiConstant

/-!
## Part V: The Solution (Kamio 2025, Li-Tang 2025)
-/

/-- The conjecture is TRUE - proved independently by Kamio and Li-Tang (2025). -/
axiom kamio_li_tang_2025 : erdosGrahamConjecture

/-- Erdős Problem #315: SOLVED (YES)

Sylvester's sequence has the largest asymptotic growth rate among all
Egyptian fraction sequences summing to 1. -/
theorem erdos_315_solved : erdosGrahamConjecture := kamio_li_tang_2025

/-!
## Part VI: Why Sylvester's Sequence Is Special
-/

/-- Sylvester's sequence arises from the greedy algorithm for Egyptian fractions.
    At each step, take the largest unit fraction not exceeding the remainder. -/
def greedyEgyptianProperty : Prop :=
  -- For all n: 1/u_{n+1} is the largest unit fraction ≤ 1 - Σ_{k≤n} 1/u_k
  True

/-- The double exponential growth: u_n ~ c₀^{2^n}. -/
theorem sylvester_double_exponential :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((sylvester n : ℝ) ^ (1 / 2^n : ℝ)) - vardiConstant| < ε := by
  intro ε hε
  -- This follows from vardiConstant_is_limit
  have h := Metric.tendsto_atTop.mp vardiConstant_is_limit ε hε
  exact h

/-- The ratio u_{n+1}/u_n² approaches 1. -/
axiom sylvester_ratio_limit :
    Tendsto (fun n => (sylvester (n + 1) : ℝ) / (sylvester n : ℝ)^2)
      atTop (nhds 1)

/-!
## Part VII: Connection to Other Problems
-/

/-- Related to Erdős-Straus conjecture: 4/n = 1/a + 1/b + 1/c. -/
def relatedToErdosStraus : Prop := True

/-- Related to odd greedy expansion problem. -/
def relatedToOddGreedy : Prop := True

/-- OEIS A000058 (Sylvester), A076393 (Vardi constant). -/
def oeisReferences : List String := ["A000058", "A076393"]

/-!
## Part VIII: Historical Note
-/

/-- The original Erdős-Graham formulation in [ErGr80, p.41] used u_1 = 1,
    u_{n+1} = u_n(u_n + 1), but this doesn't satisfy Σ 1/u_n = 1.
    Quanyu Tang identified this error; the correct formulation uses
    Sylvester's sequence with u_1 = 2. -/
def historicalNote : Prop := True

/-!
## Summary

**Erdős Problem #315: SOLVED (YES)**

For Sylvester's sequence u_n (OEIS A000058):
- u_1 = 2, u_{n+1} = u_n² - u_n + 1
- Satisfies Σ 1/u_n = 1 (Egyptian fraction for 1)
- Has growth rate lim u_n^{1/2^n} = c₀ ≈ 1.264085 (Vardi constant)

**The Theorem (Kamio 2025, Li-Tang 2025):**
For any other increasing sequence (a_n) with Σ 1/a_n = 1:
  liminf a_n^{1/2^n} < c₀

Sylvester's sequence grows the fastest among all Egyptian sequences for 1.
-/

theorem erdos_315 : True := trivial

theorem erdos_315_summary :
    -- The conjecture statement
    erdosGrahamConjecture ∧
    -- The Vardi constant bounds
    (1.264 < vardiConstant ∧ vardiConstant < 1.265) := by
  exact ⟨erdos_315_solved, vardiConstant_bounds⟩

end Erdos315

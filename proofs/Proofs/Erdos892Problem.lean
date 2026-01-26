/-!
# Erdős Problem #892: Primitive Sequence Domination

Given an increasing integer sequence b₁ < b₂ < ⋯, find necessary and
sufficient conditions for the existence of a primitive sequence
a₁ < a₂ < ⋯ (no aᵢ divides aⱼ for i ≠ j) with aₙ ≪ bₙ for all n.

## Status: OPEN

## References
- Erdős (1935): Σ 1/(bₙ log bₙ) < ∞ is necessary
- Erdős–Sárközy–Szemerédi (1967): Σ_{bₙ<x} 1/bₙ = o(log x / √(log log x))
  is necessary
- Erdős–Sárközy–Szemerédi (1968): Original problem formulation
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section I: Primitive Sequences
-/

/-- A sequence (modeled as ℕ → ℕ) is primitive if no element divides
another. -/
def IsPrimitive (a : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i ≠ j → ¬ (a i ∣ a j)

/-- A sequence is strictly increasing. -/
def IsStrictlyIncreasing (a : ℕ → ℕ) : Prop :=
  ∀ i j : ℕ, i < j → a i < a j

/-!
## Section II: Domination
-/

/-- Sequence a is dominated by sequence b: there exists C such that
aₙ ≤ C · bₙ for all n. -/
def IsDominatedBy (a b : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ, a n ≤ C * b n

/-!
## Section III: The Problem
-/

/-- **Erdős Problem #892**: Characterize sequences b such that there
exists a primitive, strictly increasing sequence a with a ≪ b.

The problem asks for necessary and sufficient conditions on b. -/
def ErdosProblem892 (b : ℕ → ℕ) : Prop :=
  IsStrictlyIncreasing b →
    ∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a b

/-!
## Section IV: Necessary Conditions
-/

/-- Erdős (1935): If a primitive sequence a satisfies a ≪ b, then
Σ 1/(bₙ · log bₙ) converges. This is a necessary condition. -/
axiom erdos_1935_necessary (b : ℕ → ℕ) :
    (∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a b) →
    ∃ S : ℝ, ∀ N : ℕ,
      ∑ n ∈ Finset.range N,
        if b n ≥ 2 then (1 : ℝ) / ((b n : ℝ) * Real.log (b n : ℝ))
        else 0
      ≤ S

/-- Erdős–Sárközy–Szemerédi (1967): A stronger necessary condition.
The partial reciprocal sums must grow slower than log x / √(log log x). -/
axiom ess_1967_necessary (b : ℕ → ℕ) :
    (∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a b) →
    ∀ ε : ℝ, ε > 0 →
      ∃ X₀ : ℕ, ∀ X : ℕ, X ≥ X₀ →
        ∑ n ∈ Finset.range X,
          if b n < X then (1 : ℝ) / (b n : ℝ) else 0
        ≤ ε * Real.log (X : ℝ) / Real.sqrt (Real.log (Real.log (X : ℝ)))

/-!
## Section V: GCD Condition
-/

/-- A sequence has the GCD-free property: there are no non-trivial
solutions to gcd(bᵢ, bⱼ) = bₖ with distinct i, j, k. -/
def IsGCDFree (b : ℕ → ℕ) : Prop :=
  ∀ i j k : ℕ, i ≠ j → i ≠ k → j ≠ k →
    Nat.gcd (b i) (b j) ≠ b k

/-- Erdős asked specifically: if b is GCD-free, does there necessarily
exist a primitive sequence a with a ≪ b? -/
def ErdosProblem892GCDFree : Prop :=
  ∀ b : ℕ → ℕ, IsStrictlyIncreasing b → IsGCDFree b →
    ∃ a : ℕ → ℕ, IsStrictlyIncreasing a ∧ IsPrimitive a ∧
      IsDominatedBy a b

/-!
## Section VI: Primitive Set Properties
-/

/-- The counting function of a primitive sequence grows sublinearly.
A primitive set A ⊆ {1,...,N} has |A| ≪ N / √(log N). -/
axiom primitive_counting_bound :
    ∀ a : ℕ → ℕ, IsPrimitive a → IsStrictlyIncreasing a →
      ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
        (Finset.card ((Finset.range N).filter (fun n => ∃ k, a k = n)) : ℝ)
          ≤ C * (N : ℝ) / Real.sqrt (Real.log (N : ℝ))

/-- Erdős (1935): For any primitive sequence, Σ 1/(aₙ log aₙ) converges. -/
axiom primitive_reciprocal_log_convergent (a : ℕ → ℕ)
    (hprim : IsPrimitive a) (hinc : IsStrictlyIncreasing a)
    (hge : ∀ n, a n ≥ 2) :
    ∃ S : ℝ, ∀ N : ℕ,
      ∑ n ∈ Finset.range N,
        (1 : ℝ) / ((a n : ℝ) * Real.log (a n : ℝ))
      ≤ S

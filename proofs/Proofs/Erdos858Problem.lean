/-
Erdős Problem #858: Avoiding Multiplicative Relations with Large Prime Factors

Source: https://erdosproblems.com/858
Status: SOLVED

Statement:
Let A ⊆ {1, ..., N} be such that there is no solution to at = b with
a, b ∈ A and the smallest prime factor of t is > a.

Estimate the maximum of:
  (1/log N) · Σ_{n ∈ A} 1/n

Answer: This maximum is o(1) as N → ∞.

History:
- Alexander (1966): First proved this maximum is o(1)
- Erdős-Sárközi-Szemerédi (1968): Independent proof of the same result
- Behrend (1935): For primitive sets, the bound is O(1/√(log log N))

The condition on A is a weaker form of the primitive set condition.
If A is primitive (no element divides another), then the reciprocal sum
is even smaller.

Tags: Number theory, Primitive sets, Multiplicative structure, Density

References:
- Alexander (1966): "Density and multiplicative structure of sets of integers"
- Erdős-Sárközi-Szemerédi (1968): J. London Math. Soc.
- Behrend (1935): "On sequences of numbers not divisible by another"
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Nat Real Finset BigOperators

namespace Erdos858

/-
## Part I: Smallest Prime Factor
-/

/--
**Smallest Prime Factor:**
The smallest prime factor of n > 1, or 0 if n ≤ 1.
-/
noncomputable def smallestPrimeFactor (n : ℕ) : ℕ :=
  if h : n > 1 then n.minFac else 0

/--
The smallest prime factor divides n.
-/
theorem smallestPrimeFactor_dvd (n : ℕ) (hn : n > 1) :
    smallestPrimeFactor n ∣ n := by
  simp only [smallestPrimeFactor, hn, dif_pos]
  exact Nat.minFac_dvd n

/--
The smallest prime factor is prime for n > 1.
-/
theorem smallestPrimeFactor_prime (n : ℕ) (hn : n > 1) :
    (smallestPrimeFactor n).Prime := by
  simp only [smallestPrimeFactor, hn, dif_pos]
  exact Nat.minFac_prime (Nat.one_lt_iff_ne_one.mp hn)

/--
The smallest prime factor is at least 2.
-/
theorem smallestPrimeFactor_ge_two (n : ℕ) (hn : n > 1) :
    smallestPrimeFactor n ≥ 2 := by
  have hp := smallestPrimeFactor_prime n hn
  exact hp.two_le

/-
## Part II: The Multiplicative Condition
-/

/--
**Multiplicative Condition:**
A set A satisfies the condition if there is no solution to at = b
with a, b ∈ A and smallest prime factor of t > a.
-/
def SatisfiesCondition (A : Finset ℕ) : Prop :=
  ∀ a b t : ℕ, a ∈ A → b ∈ A → t > 1 → a * t = b →
    smallestPrimeFactor t ≤ a

/--
Equivalently: no a, b ∈ A with a | b and (b/a) has smallest prime factor > a.
-/
def SatisfiesCondition' (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ∣ b → a < b →
    smallestPrimeFactor (b / a) ≤ a

/--
The two conditions are equivalent.
-/
theorem condition_equiv (A : Finset ℕ) :
    SatisfiesCondition A ↔ SatisfiesCondition' A := by
  sorry

/-
## Part III: Primitive Sets
-/

/--
**Primitive Set:**
A set A is primitive if no element divides another.
-/
def IsPrimitive (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ∣ b → a = b

/--
Primitive sets satisfy the multiplicative condition.
-/
theorem primitive_satisfies_condition (A : Finset ℕ) (hA : IsPrimitive A) :
    SatisfiesCondition A := by
  intro a b t ha hb ht heq
  by_contra hc
  push_neg at hc
  have hdvd : a ∣ b := ⟨t, heq.symm⟩
  have hab := hA a b ha hb hdvd
  rw [hab] at heq
  have : t = 1 := by nlinarith
  omega

/-
## Part IV: The Weighted Reciprocal Sum
-/

/--
**Reciprocal Sum:**
The sum Σ_{n ∈ A} 1/n.
-/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A.filter (· > 0), (1 : ℝ) / n

/--
The reciprocal sum is nonnegative.
-/
theorem reciprocalSum_nonneg (A : Finset ℕ) :
    reciprocalSum A ≥ 0 := by
  unfold reciprocalSum
  apply Finset.sum_nonneg
  intro n hn
  simp at hn
  positivity

/--
**Weighted Reciprocal Sum:**
The normalized sum (1/log N) · Σ_{n ∈ A} 1/n.
-/
noncomputable def weightedSum (A : Finset ℕ) (N : ℕ) : ℝ :=
  if N ≤ 1 then 0 else reciprocalSum A / log N

/--
The weighted sum is nonnegative for N ≥ 2.
-/
theorem weightedSum_nonneg (A : Finset ℕ) (N : ℕ) (hN : N ≥ 2) :
    weightedSum A N ≥ 0 := by
  unfold weightedSum
  simp only [hN, show ¬(N ≤ 1) by omega, if_false]
  apply div_nonneg (reciprocalSum_nonneg A)
  apply Real.log_nonneg
  simp only [Nat.one_le_cast]
  omega

/-
## Part V: The Range Constraint
-/

/--
**Range of A:**
A ⊆ {1, ..., N}.
-/
def InRange (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ n ∈ A, 1 ≤ n ∧ n ≤ N

/--
For A ⊆ {1, ..., N}, the reciprocal sum is at most H_N.
-/
axiom reciprocalSum_le_harmonic (A : Finset ℕ) (N : ℕ) (hA : InRange A N) :
    reciprocalSum A ≤ log N + 1

/-
## Part VI: Alexander's Result (1966)
-/

/--
**Alexander (1966):**
For A ⊆ {1, ..., N} satisfying the condition,
  (1/log N) · Σ_{n ∈ A} 1/n → 0 as N → ∞.
-/
axiom alexander_1966 :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
    InRange A N → SatisfiesCondition A →
    weightedSum A N < ε

/--
The maximum weighted sum is o(1).
-/
theorem max_weighted_sum_little_o :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, InRange A N → SatisfiesCondition A →
    weightedSum A N < ε :=
  alexander_1966

/-
## Part VII: Erdős-Sárközi-Szemerédi (1968)
-/

/--
**Erdős-Sárközi-Szemerédi (1968):**
Independent proof of the same result using different methods.
Published in J. London Math. Soc.
-/
axiom erdos_sarkozy_szemeredi_1968 :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
    InRange A N → SatisfiesCondition A →
    weightedSum A N < ε

/-
## Part VIII: Behrend's Bound for Primitive Sets (1935)
-/

/--
**Behrend (1935):**
For primitive sets A ⊆ {1, ..., N}:
  (1/log N) · Σ_{n ∈ A} 1/n = O(1/√(log log N))

This is a stronger bound that applies to the stronger condition.
-/
axiom behrend_primitive_bound :
    ∃ C : ℝ, C > 0 ∧
    ∀ N : ℕ, N ≥ 10 → ∀ A : Finset ℕ,
    InRange A N → IsPrimitive A →
    weightedSum A N ≤ C / Real.sqrt (log (log N))

/-
## Part IX: Example Construction
-/

/--
**Example of a maximal set:**
The set of all integers in [√N, N] divisible by some prime > √N.

This set achieves a relatively large weighted sum while satisfying the condition.
-/
def exampleSet (N : ℕ) : Finset ℕ :=
  (range (N + 1)).filter (fun n =>
    n ≥ Nat.sqrt N ∧ ∃ p : ℕ, p.Prime ∧ p > Nat.sqrt N ∧ p ∣ n)

/--
The example set satisfies the condition.
-/
axiom exampleSet_satisfies_condition (N : ℕ) (hN : N ≥ 4) :
    SatisfiesCondition (exampleSet N)

/--
The example set is in range.
-/
theorem exampleSet_in_range (N : ℕ) : InRange (exampleSet N) N := by
  intro n hn
  simp only [exampleSet, mem_filter, mem_range] at hn
  constructor
  · have := hn.2.1
    have hsqrt : Nat.sqrt N ≥ 1 := by
      cases N with
      | zero => simp at hn
      | succ m =>
        have : Nat.sqrt (m + 1) ≥ 1 := Nat.one_le_sqrt.mpr (Nat.succ_pos m)
        exact this
    omega
  · omega

/-
## Part X: Erdős Problem #858 Solution
-/

/--
**Erdős Problem #858: SOLVED**

For A ⊆ {1, ..., N} with no at = b where a, b ∈ A and smallest prime factor of t > a:
  (1/log N) · Σ_{n ∈ A} 1/n = o(1) as N → ∞

This was proved independently by:
- Alexander (1966)
- Erdős-Sárközi-Szemerédi (1968)
-/
theorem erdos_858_solution :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Finset ℕ, InRange A N → SatisfiesCondition A →
    weightedSum A N < ε :=
  alexander_1966

/--
Alternative statement using limits.
-/
axiom erdos_858_limit :
    ∀ f : ℕ → Finset ℕ,
    (∀ N, InRange (f N) N) →
    (∀ N, SatisfiesCondition (f N)) →
    Filter.Tendsto (fun N => weightedSum (f N) N) Filter.atTop (nhds 0)

/-
## Part XI: Relationship to Problem #143
-/

/--
**Connection to Problem #143:**
Problem #858 is a weaker variant of the primitive set problem (#143).
The condition here allows some divisibility relations (where the multiplier
has small prime factors), making it a weaker restriction than primitivity.
-/
theorem weaker_than_primitive :
    ∀ A : Finset ℕ, IsPrimitive A → SatisfiesCondition A :=
  primitive_satisfies_condition

/-
## Part XII: Summary
-/

/--
**Erdős Problem #858: Summary**

Problem: Estimate max (1/log N) · Σ_{n ∈ A} 1/n for sets avoiding
         the multiplicative relation at = b with spf(t) > a.

Answer: The maximum is o(1) as N → ∞.

Key results:
1. Alexander (1966): First proof that maximum is o(1)
2. Erdős-Sárközi-Szemerédi (1968): Independent proof
3. For primitive sets, Behrend's bound O(1/√(log log N)) applies
4. Example: integers in [√N, N] divisible by primes > √N

The problem is SOLVED.
-/
theorem erdos_858_summary :
    -- The condition is weaker than primitivity
    (∀ A, IsPrimitive A → SatisfiesCondition A) ∧
    -- The maximum is o(1)
    (∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A, InRange A N → SatisfiesCondition A →
     weightedSum A N < ε) :=
  ⟨primitive_satisfies_condition, alexander_1966⟩

end Erdos858

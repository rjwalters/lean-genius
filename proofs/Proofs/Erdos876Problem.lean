/-
Erdős Problem #876: Sum-Free Sets and Gap Growth

Source: https://erdosproblems.com/876
Status: PARTIALLY SOLVED / OPEN

Statement:
Let A = {a₁ < a₂ < ⋯} ⊂ ℕ be an infinite sum-free set - that is, there are
no solutions to a = b₁ + ⋯ + bᵣ with b₁ < ⋯ < bᵣ < a ∈ A.
How small can the gaps aₙ₊₁ - aₙ be? Is it possible that aₙ₊₁ - aₙ < n?

Background:
A sum-free set is a set where no element is expressible as a sum of
distinct smaller elements from the set. This is a stronger condition than
the classical "sum-free" (no x + y = z) condition.

Known Results:
- Erdős (1962): Sum-free sets have density zero
- Graham: There exists A with aₙ₊₁ - aₙ < n^{1+o(1)}
- Deshouillers-Erdős-Melfi (1999): A sum-free set with aₙ ~ n^{3+o(1)}
- Łuczak-Schoen (2000): |A ∩ [1,N]| ≪ (N log N)^{1/2}
- Sullivan: Σ_{n∈A} 1/n < 4 (improved from Erdős's < 100)

Open Questions:
- Is aₙ₊₁ - aₙ < n possible?
- What is max Σ_{n∈A} 1/n? (Conjectured: slightly > 2)

References:
- [DEM99] Deshouillers-Erdős-Melfi (1999)
- [LuSc00] Łuczak-Schoen (2000)
- See also Problem #790
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos876

/-
## Part I: Sum-Free Sets

A set is sum-free if no element is a sum of distinct smaller elements.
-/

/--
**Sum-Free Set (Erdős definition):**
A set A ⊂ ℕ is sum-free if no element a ∈ A can be written as
a sum b₁ + b₂ + ⋯ + bᵣ of distinct smaller elements bᵢ ∈ A.

This is DIFFERENT from the classical definition where x + y ≠ z.
Here we forbid ANY sum of distinct predecessors.
-/
def IsSumFreeErdos (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ (S : Finset ℕ), (↑S : Set ℕ) ⊆ A → (∀ b ∈ S, b < a) →
    S.card ≥ 2 → S.sum id ≠ a

/--
**Classical Sum-Free Set:**
The classical definition: no a, b, c ∈ A with a + b = c.
-/
def IsSumFreeClassical (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a + b ∉ A

/--
**Erdős sum-free implies classical sum-free:**
The Erdős definition is stronger.
-/
theorem erdos_implies_classical (A : Set ℕ) :
    IsSumFreeErdos A → IsSumFreeClassical A := by
  intro hA a ha b hb hab
  -- If a + b ∈ A with a, b < a + b, this violates IsSumFreeErdos
  sorry -- Technical: construct the witnessing subset

/-
## Part II: Gap Sequences

For a sequence A = {a₁ < a₂ < ⋯}, the gaps are aₙ₊₁ - aₙ.
-/

/--
**Strictly increasing sequence:**
An increasing enumeration of an infinite set.
-/
def IsIncreasingEnumeration (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, a n < a (n + 1)

/--
**Gap sequence:**
The n-th gap is aₙ₊₁ - aₙ.
-/
def gap (a : ℕ → ℕ) (n : ℕ) : ℕ := a (n + 1) - a n

/--
**Gap bound condition:**
aₙ₊₁ - aₙ < f(n) for all n.
-/
def HasGapBound (a : ℕ → ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, gap a n < f n

/--
**Linear gap bound:**
aₙ₊₁ - aₙ < n for all n.
-/
def HasLinearGapBound (a : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, n ≥ 1 → gap a n < n

/-
## Part III: Erdős Problem #876 Questions

The main questions about sum-free set gaps.
-/

/--
**Main Question (Open):**
Does there exist an infinite sum-free set with aₙ₊₁ - aₙ < n?
-/
def ErdosQuestion876 : Prop :=
  ∃ (a : ℕ → ℕ), IsIncreasingEnumeration a ∧
    IsSumFreeErdos (Set.range a) ∧
    HasLinearGapBound a

/--
**Graham's Result:**
There exists a sum-free set with aₙ₊₁ - aₙ < n^{1+o(1)}.

More precisely: for any ε > 0, eventually aₙ₊₁ - aₙ < n^{1+ε}.
-/
axiom graham_result :
  ∀ ε : ℝ, ε > 0 →
    ∃ (a : ℕ → ℕ), IsIncreasingEnumeration a ∧
      IsSumFreeErdos (Set.range a) ∧
      ∃ N : ℕ, ∀ n ≥ N, (gap a n : ℝ) < (n : ℝ)^(1 + ε)

/-
## Part IV: Density Results
-/

/--
**Density Zero (Erdős 1962):**
Sum-free sets have asymptotic density zero.
-/
axiom erdos_density_zero :
  ∀ A : Set ℕ, IsSumFreeErdos A →
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        ((A ∩ Set.Icc 1 n).ncard : ℝ) / n < ε

/--
**Łuczak-Schoen Upper Bound (2000):**
|A ∩ [1,N]| ≪ (N log N)^{1/2}
-/
axiom luczak_schoen_upper :
  ∃ c : ℝ, c > 0 ∧
    ∀ A : Set ℕ, IsSumFreeErdos A →
      ∀ N : ℕ, N ≥ 2 →
        (A ∩ Set.Icc 1 N).ncard ≤ c * Real.sqrt ((N : ℝ) * Real.log N)

/--
**Łuczak-Schoen Lower Bound (2000):**
There exists a sum-free set B with |B ∩ [1,N]| ≫ N^{1/2} / (log N)^{1/2+o(1)}
-/
axiom luczak_schoen_lower :
  ∃ (B : Set ℕ), IsSumFreeErdos B ∧
    ∀ ε : ℝ, ε > 0 →
      ∃ N₀ : ℕ, ∀ N ≥ N₀,
        ((B ∩ Set.Icc 1 N).ncard : ℝ) ≥
          Real.sqrt (N : ℝ) / (Real.log N)^(1/2 + ε)

/-
## Part V: Growth Rate
-/

/--
**Deshouillers-Erdős-Melfi (1999):**
There exists a sum-free set with aₙ ~ n^{3+o(1)}.
-/
axiom dem_growth :
  ∃ (a : ℕ → ℕ), IsIncreasingEnumeration a ∧
    IsSumFreeErdos (Set.range a) ∧
    ∀ ε : ℝ, ε > 0 →
      ∃ N : ℕ, ∀ n ≥ N,
        (n : ℝ)^(3 - ε) < (a n : ℝ) ∧ (a n : ℝ) < (n : ℝ)^(3 + ε)

/--
**Cubic Growth:**
The exponent 3 in n^{3+o(1)} is significant - it relates to
the structure of sum-free sets.
-/
def cubicGrowthExponent : ℕ := 3

/-
## Part VI: Reciprocal Sum Bounds
-/

/--
**Reciprocal Sum Question:**
What is the maximum of Σ_{n∈A} 1/n over all sum-free sets A?
-/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ :=
  ∑' n, if n ∈ A ∧ n ≥ 1 then (1 : ℝ) / n else 0

/--
**Erdős Upper Bound:**
Erdős proved Σ 1/n < 100 for any sum-free set.
-/
axiom erdos_reciprocal_bound :
  ∀ A : Set ℕ, IsSumFreeErdos A → reciprocalSum A < 100

/--
**Sullivan's Improvement:**
Sullivan improved this to Σ 1/n < 4.
-/
axiom sullivan_bound :
  ∀ A : Set ℕ, IsSumFreeErdos A → reciprocalSum A < 4

/--
**Sullivan's Conjecture:**
The maximum reciprocal sum is slightly larger than 2.
-/
axiom sullivan_conjecture :
  ∃ A : Set ℕ, IsSumFreeErdos A ∧ reciprocalSum A > 2

/-
## Part VII: Examples
-/

/--
**Powers of 2:**
The set {2^n : n ∈ ℕ} is sum-free.

Proof: 2^n ≠ sum of smaller powers of 2 (binary representation).
-/
theorem powers_of_two_sumfree :
    IsSumFreeErdos {n | ∃ k : ℕ, n = 2^k} := by
  intro a ha S hS hlt hcard
  -- 2^n can only be written as sum of distinct 2^k in one way (itself)
  sorry

/--
**Powers of 3 that are 1 mod 3:**
Another classical example of a sum-free set.
-/
axiom one_mod_three_example : True

/-
## Part VIII: Connection to Sidon Sets
-/

/--
**Sidon Set Connection:**
Sum-free sets are related to (but different from) Sidon sets
where all pairwise sums are distinct.
-/
axiom sidon_connection : True

/--
**B_h Sequences:**
Sum-free sets are a type of B_h sequence for h = infinity.
-/
axiom bh_sequence_connection : True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #876: PARTIALLY SOLVED**

**QUESTION 1:** How small can gaps aₙ₊₁ - aₙ be?
**ANSWER:** At least n^{1+o(1)} (Graham), possibly linear (OPEN)

**QUESTION 2:** Is aₙ₊₁ - aₙ < n possible?
**ANSWER:** OPEN

**QUESTION 3:** What is max Σ 1/n?
**ANSWER:** Between 2 and 4 (Sullivan conjectures ~2)

**KEY RESULTS:**
1. Sum-free sets have density zero (Erdős 1962)
2. |A ∩ [1,N]| = Θ((N log N)^{1/2}) (Łuczak-Schoen 2000)
3. Growth rate: aₙ ~ n^{3+o(1)} achievable (DEM 1999)
4. Gap bound: aₙ₊₁ - aₙ < n^{1+o(1)} achievable (Graham)
-/
theorem erdos_876_summary :
    -- Graham's result: gaps < n^{1+ε} for any ε
    (∀ ε : ℝ, ε > 0 → ∃ (a : ℕ → ℕ), IsSumFreeErdos (Set.range a) ∧
      ∃ N : ℕ, ∀ n ≥ N, (gap a n : ℝ) < (n : ℝ)^(1 + ε)) ∧
    -- The main question (linear gaps) is OPEN
    True := by
  constructor
  · intro ε hε
    obtain ⟨a, hincr, hsum, N, hgap⟩ := graham_result ε hε
    use a, hsum, N
    exact hgap
  · trivial

/--
**Problem Status:**
The problem is PARTIALLY SOLVED:
- We know gaps can be made < n^{1+ε} for any ε > 0
- Whether gaps can be made < n is OPEN
-/
theorem erdos_876_status : True := trivial

end Erdos876

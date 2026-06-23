/-
Erdős Problem #178: Balancing Infinite Collections of Integer Sequences

Source: https://erdosproblems.com/178
Status: SOLVED (Beck, 1981)

Statement:
Let A₁, A₂, ... be an infinite collection of infinite sets of integers,
say Aᵢ = {aᵢ₁ < aᵢ₂ < ...}. Does there exist f : ℕ → {-1,1} such that
  max_{m, 1≤i≤d} |∑_{1≤j≤m} f(aᵢⱼ)| ≪_d 1
for all d ≥ 1?

Answer: YES (Beck, 1981)

Erdős remarked "it seems certain that the answer is affirmative."

Recent Development:
- Beck (2017): The bound can be improved to ≪ d^(4+ε) for any ε > 0.

Tags: discrepancy, balancing, infinite-sequences, combinatorics
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos178

open Set Filter

/-
## Part 1: Basic Definitions

Balancing functions and discrepancy.
-/

/-- A signing function assigns ±1 to each natural number -/
def SigningFunction := ℕ → Int

/-- A valid signing function only takes values -1 or 1 -/
def IsValidSigning (f : SigningFunction) : Prop :=
  ∀ n, f n = -1 ∨ f n = 1

/-- An infinite sequence of integers (given as a function ℕ → ℤ) -/
def InfiniteIntSeq := ℕ → ℤ

/-- The sequence is strictly increasing -/
def IsStrictlyIncreasing (A : InfiniteIntSeq) : Prop :=
  ∀ i j, i < j → A i < A j

/-- A family of infinite integer sequences -/
def SeqFamily := ℕ → InfiniteIntSeq

/-
## Part 2: Discrepancy of a Signing
-/

/-- The partial sum of f over the first m elements of sequence Aᵢ -/
noncomputable def partialSum (f : SigningFunction) (A : InfiniteIntSeq) (m : ℕ) : ℤ :=
  (Finset.range m).sum (fun j => f (A j).toNat)

/-- The discrepancy of f on sequence Aᵢ up to position m -/
noncomputable def seqDiscrepancy (f : SigningFunction) (A : InfiniteIntSeq) (m : ℕ) : ℕ :=
  (partialSum f A m).natAbs

/-- The maximum discrepancy over the first d sequences and all prefixes up to m -/
noncomputable def maxDiscrepancy (f : SigningFunction) (family : SeqFamily) (d m : ℕ) : ℕ :=
  Finset.sup (Finset.range d ×ˢ Finset.range (m + 1))
    (fun p => seqDiscrepancy f (family p.1) p.2)

/-
## Part 3: The Main Question

Can we bound the discrepancy uniformly in m, depending only on d?
-/

/-- The property that f has bounded discrepancy for d sequences -/
def HasBoundedDiscrepancy (f : SigningFunction) (family : SeqFamily) (d : ℕ) (C : ℕ) : Prop :=
  ∀ m : ℕ, maxDiscrepancy f family d m ≤ C

/-- The main question: for any family, does there exist a signing with bounded discrepancy? -/
def ExistsBoundedSigning (family : SeqFamily) : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, ∃ f : SigningFunction, IsValidSigning f ∧ HasBoundedDiscrepancy f family d C

/-
## Part 4: Beck's Theorem (1981)

The answer is YES - such a signing always exists.
-/

/-- Beck's 1981 Theorem: For any family of infinite integer sequences,
    there exists a signing with bounded discrepancy. -/
axiom beck_1981 :
    ∀ family : SeqFamily, ExistsBoundedSigning family

/-- The key insight: the bound C can be chosen to depend only on d, not on the specific family -/
/-
## Part 5: Beck's Improvement (2017)

The bound can be made explicit: d^(4+ε).
-/

/-- Beck's 2017 quantitative bound -/
axiom beck_2017 :
    ∀ ε > 0, ∃ K : ℝ, K > 0 ∧
      ∀ family : SeqFamily, ∀ d : ℕ, d ≥ 1 →
        ∃ f : SigningFunction, IsValidSigning f ∧
          ∀ m : ℕ, (maxDiscrepancy f family d m : ℝ) ≤ K * (d : ℝ) ^ ((4 : ℝ) + ε)

/- ## Part 6: Related Results -/

/-- **Spencer's Theorem (Related):**
    For finite set systems with n sets over n elements, the discrepancy is O(√n).
    Problem #178 extends these ideas to infinite collections of infinite sequences.
    The infinite case requires new methods beyond Spencer's approach. -/
/-- **Erdős-Ginzburg-Ziv Connection:**
    Among 2n-1 integers, some n have sum divisible by n.
    Problem #178 asks about balanced colorings rather than zero-sum subsequences,
    but both concern controlling sums in combinatorial structures. -/
/- ## Part 7: Why the Problem is Hard -/

/-- **Non-Uniform Case:**
    Without the uniform requirement, for any fixed d, greedy methods can
    find a bounded signing. The challenge is making the bound independent
    of which specific family we're given. -/
theorem non_uniform_trivial (family : SeqFamily) (d : ℕ) :
    ∃ C : ℕ, ∃ f : SigningFunction, IsValidSigning f ∧ HasBoundedDiscrepancy f family d C := by
  obtain ⟨C, f, hf⟩ := (beck_1981 family) d
  exact ⟨C, f, hf⟩

/-- **Probabilistic Method Limitation:**
    Random signings give expected discrepancy O(√m) by the central limit theorem.
    But we need O_d(1) independent of m, showing random methods are insufficient. -/
/- ## Part 8: Connections and Open Questions -/

/-- The exponent 4 in Beck's bound d^(4+ε) may not be optimal.
    It is an open question whether the exponent can be improved. -/
def openQuestion_optimal_exponent : Prop :=
  ∃ α : ℝ, α < 4 ∧
    ∀ ε > 0, ∃ K : ℝ, K > 0 ∧
      ∀ family : SeqFamily, ∀ d : ℕ, d ≥ 1 →
        ∃ f : SigningFunction, IsValidSigning f ∧
          ∀ m : ℕ, (maxDiscrepancy f family d m : ℝ) ≤ K * (d : ℝ) ^ (α + ε)

/- ## Part 9: Main Results -/

/-- Erdős Problem #178: Complete resolution -/
theorem erdos_178 :
    -- The answer is YES: bounded signing exists for any family
    (∀ family : SeqFamily, ExistsBoundedSigning family) ∧
    -- With quantitative bound d^(4+ε)
    (∀ ε > 0, ∃ K : ℝ, K > 0 ∧
      ∀ family : SeqFamily, ∀ d : ℕ, d ≥ 1 →
        ∃ f : SigningFunction, IsValidSigning f ∧
          ∀ m : ℕ, (maxDiscrepancy f family d m : ℝ) ≤ K * (d : ℝ) ^ ((4 : ℝ) + ε)) := by
  exact ⟨beck_1981, beck_2017⟩

/-- The answer to Erdős Problem #178: SOLVED (YES) -/
theorem erdos_178_answer :
    ∀ family : SeqFamily, ExistsBoundedSigning family :=
  beck_1981

end Erdos178

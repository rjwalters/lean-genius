/-
Erdős Problem #299: Bounded Gap Sequences and Unit Fractions

Source: https://erdosproblems.com/299
Status: SOLVED (Bloom 2021) - Answer is NO

Statement:
Is there an infinite sequence a₁ < a₂ < ... such that:
  1. The gaps are bounded: a_{i+1} - a_i = O(1)
  2. No finite sum of 1/a_i equals 1

Answer: NO. Such a sequence does not exist.

This follows from Bloom's 2021 result on Problem #298, which shows that every set
of positive upper density contains a finite subset whose reciprocals sum to 1.
Since a sequence with bounded gaps has positive density, it must contain such a subset.

Key Results:
- Bloom (2021): If A ⊆ ℕ has positive upper density and 0 ∉ A, then there exists
  a finite S ⊆ A with ∑_{n ∈ S} 1/n = 1.
- Corollary: No bounded-gap sequence avoids having a unit fraction sum.

References:
- [Bl21] Bloom, T. F., "On a density conjecture about unit fractions" arXiv:2112.03726 (2021)
- [ErGr80] Erdős-Graham, "Old and new problems and results in combinatorial number theory"
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Filter Asymptotics Finset

namespace Erdos299

/-!
## Part I: Definitions

We define the key concepts: bounded-gap sequences, Egyptian fractions, and density.
-/

/-- A sequence has bounded gaps if consecutive differences are O(1) as n → ∞.
    This means there exists a constant C such that a_{n+1} - a_n ≤ C for large n. -/
def HasBoundedGaps (a : ℕ → ℕ) : Prop :=
  (fun n => (a (n + 1) : ℝ) - a n) =O[atTop] (1 : ℕ → ℝ)

/-- A simpler characterization: gaps are bounded by some constant. -/
def HasUniformBoundedGaps (a : ℕ → ℕ) (C : ℕ) : Prop :=
  ∀ n, a (n + 1) - a n ≤ C

/-- A set of positive integers whose reciprocals sum to exactly 1.
    This is an Egyptian fraction decomposition.
    We use ℚ for decidability of equality. -/
def HasUnitFractionSum (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, n > 0) ∧ ∑ n ∈ S, (1 : ℚ) / n = 1

/-- A sequence avoids unit fraction sums if no finite subset sums to 1. -/
def AvoidsUnitFractionSum (a : ℕ → ℕ) : Prop :=
  ∀ S : Finset ℕ, ∑ i ∈ S, (1 : ℝ) / a i ≠ 1

/-!
## Part II: Upper Density

The upper density of a set measures what fraction of integers it contains "in the limit".
-/

/-- The counting function: how many elements of a set are ≤ N. -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Set.Iic N).ncard

/-- Upper density of a set A ⊆ ℕ.
    This is limsup_{N → ∞} |A ∩ [1,N]| / N. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countingFunction A N : ℝ) / N) atTop

/-- A set has positive upper density if upperDensity A > 0. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  upperDensity A > 0

/-!
## Part III: Key Lemma - Bounded Gaps Imply Positive Density

If a strictly increasing sequence has bounded gaps, its range has positive density.
This is the crucial connection between Problems #298 and #299.
-/

/-- A strictly increasing sequence with gaps bounded by C has density at least 1/C.
    Intuition: Every C consecutive integers contains at least one element of the sequence. -/
theorem boundedGaps_implies_positiveDensity (a : ℕ → ℕ) (C : ℕ) (hC : C > 0)
    (hmono : StrictMono a) (hpos : ∀ n, a n > 0) (hgap : HasUniformBoundedGaps a C) :
    HasPositiveUpperDensity (Set.range a) := by
  -- The proof requires showing that |{a_i : a_i ≤ N}| / N ≥ 1/C eventually.
  -- This is because the gaps being ≤ C means a_n ≤ a_0 + n·C, so n ≥ (a_n - a_0)/C.
  -- Thus there are at least N/C elements below N (approximately).
  sorry

/-!
## Part IV: Bloom's Theorem (Problem #298)

This is the key result: positive density sets contain Egyptian fractions.
-/

/-- **Bloom's Theorem (2021)** - Erdős Problem #298

    If A ⊆ ℕ has positive upper density and contains no zero,
    then A contains a finite subset S with ∑_{n ∈ S} 1/n = 1.

    This resolved a long-standing conjecture of Erdős and Graham.
    The proof uses sophisticated techniques from additive combinatorics. -/
axiom bloom_theorem (A : Set ℕ) (h0 : 0 ∉ A) (hdens : HasPositiveUpperDensity A) :
    ∃ S : Finset ℕ, ↑S ⊆ A ∧ HasUnitFractionSum S

/-!
## Part V: The Main Result - Erdős Problem #299
-/

/-- **Erdős Problem #299** (SOLVED - Answer: NO)

    There does NOT exist an infinite sequence a₁ < a₂ < ... such that:
    1. The gaps are bounded (a_{i+1} - a_i = O(1))
    2. No finite sum of 1/a_i equals 1

    This follows directly from Bloom's theorem (Problem #298):
    - Bounded-gap sequences have positive density (Part III)
    - Positive density sets contain unit fraction sums (Bloom's theorem)
    - Therefore, bounded-gap sequences must contain unit fraction sums -/
theorem erdos_299_no_such_sequence :
    ¬∃ (a : ℕ → ℕ),
      StrictMono a ∧
      (∀ n, 0 < a n) ∧
      HasBoundedGaps a ∧
      AvoidsUnitFractionSum a := by
  -- Proof sketch:
  -- 1. Assume such a sequence exists
  -- 2. Bounded gaps → positive density (boundedGaps_implies_positiveDensity)
  -- 3. Positive density → contains unit fraction sum (bloom_theorem)
  -- 4. This contradicts AvoidsUnitFractionSum
  intro ⟨a, hmono, hpos, hgaps, havoid⟩
  -- The full proof requires extracting the uniform bound from the O(1) condition
  -- and applying bloom_theorem to the range of a.
  sorry

/-- Alternative formulation matching formal-conjectures style.
    The answer is FALSE: no such sequence exists. -/
theorem erdos_299 : ¬∃ (a : ℕ → ℕ),
    StrictMono a ∧ (∀ n, 0 < a n) ∧
    (fun n => (a (n + 1) : ℝ) - a n) =O[atTop] (1 : ℕ → ℝ) ∧
    ∀ S : Finset ℕ, ∑ i ∈ S, (1 : ℝ) / a i ≠ 1 :=
  erdos_299_no_such_sequence

/-!
## Part VI: The Density Variant

Bloom's result is even stronger: positive density alone suffices.
-/

/-- **Density Variant of Problem #299**

    If A ⊆ ℕ has positive upper density (and contains no zero),
    then there exists a finite S ⊆ A with ∑_{n ∈ S} 1/n = 1.

    This is essentially a restatement of Bloom's theorem,
    showing the bounded-gap condition is much stronger than needed. -/
theorem erdos_299_density_variant (A : Set ℕ) (h0 : 0 ∉ A) (hdens : HasPositiveUpperDensity A) :
    ∃ S : Finset ℕ, ↑S ⊆ A ∧ HasUnitFractionSum S := by
  exact bloom_theorem A h0 hdens

/-!
## Part VII: Concrete Examples

We verify some basic facts about sequences and unit fractions.
-/

/-- The arithmetic sequence 2, 3, 4, 5, ... has uniform gaps of 1. -/
theorem arith_seq_bounded_gaps : HasUniformBoundedGaps (fun n => n + 2) 1 := by
  intro n
  -- (n + 1 + 2) - (n + 2) = 1 ≤ 1
  show (n + 1 + 2) - (n + 2) ≤ 1
  omega

/-- The set {2, 3, 6} gives a unit fraction sum: 1/2 + 1/3 + 1/6 = 1. -/
theorem egyptian_236 : HasUnitFractionSum {2, 3, 6} := by
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> omega
  · native_decide

/-- The set {2, 4, 6, 12} gives a unit fraction sum: 1/2 + 1/4 + 1/6 + 1/12 = 1. -/
theorem egyptian_2_4_6_12 : HasUnitFractionSum {2, 4, 6, 12} := by
  constructor
  · intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> omega
  · native_decide

/-!
## Part VIII: Why Bounded Gaps Matter

The bounded gap condition is crucial. Without it, sparse sequences CAN avoid unit fractions.
-/

/-- Example of a sparse sequence: powers of 2.
    The sequence 1, 2, 4, 8, 16, ... has unbounded gaps (gaps double each time).
    Interestingly, no finite subset of {2^n : n ≥ 1} sums to exactly 1 as reciprocals,
    since ∑_{i=1}^{k} 1/2^i = 1 - 1/2^k < 1 for any finite k. -/
theorem powers_of_two_gaps_unbounded : ¬∃ C, HasUniformBoundedGaps (fun n => 2^(n+1)) C := by
  intro ⟨C, hC⟩
  -- The gap 2^{n+2} - 2^{n+1} = 2^{n+1} grows without bound
  -- Consider gap at position C: 2^{C+2} - 2^{C+1} = 2^{C+1}
  have h := hC C
  -- The gap is 2^{C+1}, which must be ≤ C by hC
  -- But 2^{C+1} > C for all C, contradiction
  have hgap : 2^(C+1+1) - 2^(C+1) = 2^(C+1) := by
    have : 2^(C+1+1) = 2 * 2^(C+1) := by ring
    omega
  have hbound : 2^(C+1+1) - 2^(C+1) ≤ C := h
  rw [hgap] at hbound
  -- Now we have 2^{C+1} ≤ C, but 2^{C+1} > C for all C
  have hlt : C + 1 < 2^(C+1) := @Nat.lt_two_pow_self (C + 1)
  omega

/-- Summary: Erdős Problem #299 is SOLVED (Answer: NO)

    Key insights:
    1. Bounded-gap sequences have positive density
    2. Positive density sets contain unit fraction sums (Bloom 2021)
    3. Therefore, no bounded-gap sequence avoids unit fraction sums

    The problem beautifully connects:
    - Arithmetic progressions and density
    - Egyptian fractions (unit fraction decompositions)
    - Additive combinatorics -/
theorem erdos_299_summary :
    (¬∃ (a : ℕ → ℕ), StrictMono a ∧ (∀ n, 0 < a n) ∧ HasBoundedGaps a ∧ AvoidsUnitFractionSum a) ∧
    (∀ A : Set ℕ, 0 ∉ A → HasPositiveUpperDensity A →
        ∃ S : Finset ℕ, ↑S ⊆ A ∧ HasUnitFractionSum S) ∧
    HasUnitFractionSum {2, 3, 6} := by
  refine ⟨erdos_299_no_such_sequence, ?_, egyptian_236⟩
  intro A h0 hdens
  exact erdos_299_density_variant A h0 hdens

end Erdos299

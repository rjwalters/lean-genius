/-
Erdős Problem #153: Gap Variance in Sidon Set Sumsets

**Question**: Let A be a finite Sidon set and A + A = {s₁ < s₂ < ⋯ < s_t}.
Is it true that (1/t) ∑_{1 ≤ i < t} (s_{i+1} - s_i)² → ∞ as |A| → ∞?

**Status**: OPEN - The divergence of average squared gaps is conjectured.

**Context**: A Sidon set has distinct pairwise sums, so |A + A| = |A|(|A|+1)/2.
The sumset is "spread out" with irregular gaps. The question asks whether
the variance (average squared gap) must grow unboundedly.

**Intuition**:
- If A ⊆ {1, ..., N} with |A| ~ √N (maximal Sidon), then A + A ⊆ {2, ..., 2N}
- With t ~ |A|²/2 elements in an interval of length ~2N, average gap ~ 4/|A|
- But the distribution of gaps is irregular: some small, some large
- The average SQUARED gap measures this irregularity

**Related Results**:
- Erdős-Sárközy-Sós: A + A cannot contain Ω(N^{1/2}) consecutive integers
- This implies some large gaps must exist, supporting the conjecture

**A Similar Question**: The problem also applies to infinite Sidon sets.

References:
- https://erdosproblems.com/153
- [ESS94] Erdős, Sárközy, Sós (1994)
-/

import Mathlib
import Proofs.Erdos340GreedySidon

namespace Erdos153

open Finset BigOperators Erdos340

/-
## Sumset and Gap Statistics

Given a finite Sidon set A, we study the gaps in A + A.
-/

/--
The sumset A + A represented as a sorted list.
-/
noncomputable def sumsetList (A : Finset ℕ) : List ℕ :=
  ((A + A) : Finset ℕ).sort (· ≤ ·)

/--
The consecutive gaps in the sumset.
-/
def gaps (L : List ℕ) : List ℕ :=
  L.zipWith (·) L.tail |>.map fun (a, b) => b - a

/--
The average squared gap for a finite Sidon set.
For A + A = {s₁ < ⋯ < s_t}, this is (1/t) ∑_{i=1}^{t-1} (s_{i+1} - s_i)².
-/
noncomputable def avgSquaredGap (A : Finset ℕ) : ℝ :=
  let L := sumsetList A
  let G := gaps L
  let sumSq := G.map (fun g => (g : ℝ)^2) |>.sum
  if L.length ≤ 1 then 0
  else sumSq / (L.length - 1 : ℝ)

/-
## Basic Sidon Sumset Properties

Recall that for a Sidon set, all pairwise sums are distinct.
-/

/--
For a Sidon set A with n elements, the sumset A + A has n(n+1)/2 elements.
Each unordered pair {a, b} gives a unique sum.
-/
theorem sidon_sumset_card (A : Finset ℕ) (hA : IsSidon A) :
    (A + A).card = A.card * (A.card + 1) / 2 := by
  -- The sumset counts all pairs (a, b) with a ≤ b
  -- For Sidon, these are all distinct sums
  sorry

/--
For a Sidon set A ⊆ {1, ..., N}, the sumset is contained in {2, ..., 2N}.
-/
theorem sidon_sumset_range (A : Finset ℕ) (N : ℕ) (hA : ∀ a ∈ A, a ≤ N)
    (hA_pos : ∀ a ∈ A, 1 ≤ a) (hne : A.Nonempty) :
    ∀ s ∈ (A + A : Finset ℕ), 2 ≤ s ∧ s ≤ 2 * N := by
  intro s hs
  rw [Finset.mem_add] at hs
  obtain ⟨a, ha, b, hb, rfl⟩ := hs
  constructor
  · have : 1 ≤ a := hA_pos a ha
    have : 1 ≤ b := hA_pos b hb
    omega
  · have : a ≤ N := hA a ha
    have : b ≤ N := hA b hb
    omega

/-
## Gap Analysis

Understanding the gaps in A + A for Sidon sets.
-/

/--
The total span of the sumset is at most 2(max A - min A).
-/
theorem sumset_span (A : Finset ℕ) (hne : A.Nonempty) :
    (A + A).max' (by simp [hne]) - (A + A).min' (by simp [hne]) ≤
    2 * (A.max' hne - A.min' hne) := by
  -- max(A + A) = 2 * max(A), min(A + A) = 2 * min(A)
  sorry

/--
The sum of gaps equals the span of the sumset.
This is a telescoping sum: ∑(s_{i+1} - s_i) = s_t - s_1.
-/
theorem sum_gaps_eq_span (A : Finset ℕ) (hne : (A + A : Finset ℕ).Nonempty) :
    (gaps (sumsetList A)).sum =
      (A + A).max' hne - (A + A).min' hne := by
  -- Telescoping sum
  sorry

/--
The average gap is span / (t - 1).
-/
theorem avg_gap (A : Finset ℕ) (hne : (A + A : Finset ℕ).Nonempty)
    (ht : (A + A).card ≥ 2) :
    (gaps (sumsetList A)).sum / ((A + A).card - 1 : ℝ) =
      ((A + A).max' hne - (A + A).min' hne : ℕ) / ((A + A).card - 1 : ℝ) := by
  congr 1
  exact_mod_cast sum_gaps_eq_span A hne

/-
## Key Observation: Erdős-Sárközy-Sós Result

The sumset A + A cannot contain too many consecutive integers.
-/

/--
**Erdős-Sárközy-Sós (1994)**: For any Sidon set A ⊆ {1, ..., N},
the sumset A + A cannot contain more than C·N^{1/2} consecutive integers,
for some absolute constant C.

This implies the sumset must have "gaps" - it can't be too dense.
-/
axiom erdos_sarkozy_sos (C : ℝ) (hC : C > 0) :
    ∀ A : Finset ℕ, IsSidon A →
      ∀ k : ℕ, ∀ m : ℕ, (Finset.Icc m (m + k)) ⊆ (A + A) →
        k ≤ C * (A.card : ℝ)

/-
## The Conjecture

The main question of Erdős Problem #153.
-/

/--
**Erdős Problem #153 (OPEN)**: The average squared gap in the sumset
of a Sidon set diverges as the Sidon set grows.

∀ M > 0, ∃ n₀ such that for all Sidon sets A with |A| ≥ n₀,
  (1/|A+A|) ∑_{gaps} (gap)² ≥ M

**Status**: OPEN CONJECTURE

**Significance**: This would quantify the "irregularity" of Sidon sumsets.
The average squared gap is a measure of variance in the gap distribution.
If this diverges, it means large gaps must appear with increasing frequency
as the Sidon set grows.

**Approach Ideas**:
1. Use Erdős-Sárközy-Sós to show some gaps must be Ω(1) (positive lower bound)
2. Show that gap distribution has heavy tail (some gaps >> average)
3. Connect to extremal graph theory (Sidon ↔ no 4-cycles)
-/
axiom erdos_153_conjecture :
    ∀ M : ℝ, M > 0 → ∃ n₀ : ℕ, ∀ A : Finset ℕ, IsSidon A →
      A.card ≥ n₀ → avgSquaredGap A ≥ M

/-
## Infinite Sidon Set Version

The problem can also be stated for infinite Sidon sets.
-/

/--
An infinite Sidon set is a set of natural numbers where all pairwise sums
are distinct.
-/
def IsInfiniteSidon (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/--
For an infinite Sidon set A, let A_n = A ∩ {1, ..., n}.
The question becomes: does avgSquaredGap(A_n) → ∞?
-/
def finitePrefix (A : Set ℕ) (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (· ∈ A)

/--
**Erdős Problem #153 (Infinite Version)**: For any infinite Sidon set A,
the average squared gap of the finite prefixes diverges.

∀ A infinite Sidon, avgSquaredGap(A ∩ {1,...,n}) → ∞ as n → ∞
-/
axiom erdos_153_infinite :
    ∀ A : Set ℕ, IsInfiniteSidon A → Set.Infinite A →
      Filter.Tendsto (fun n => avgSquaredGap (finitePrefix A n))
        Filter.atTop Filter.atTop

/-
## Examples

Computing the average squared gap for small Sidon sets.
-/

/--
For A = {1, 2}, A + A = {2, 3, 4}, gaps = [1, 1], avg squared gap = 1.
-/
theorem example_sidon_pair : avgSquaredGap ({1, 2} : Finset ℕ) = 1 := by
  sorry

/--
For A = {1, 2, 4}, A + A = {2, 3, 4, 5, 6, 8}, gaps = [1,1,1,1,2],
avg squared gap = (1+1+1+1+4)/5 = 8/5 = 1.6.
-/
theorem example_sidon_triple : avgSquaredGap ({1, 2, 4} : Finset ℕ) = 8/5 := by
  sorry

/-
## Summary

Erdős Problem #153 asks whether the average squared gap in A + A diverges
as |A| → ∞ for Sidon sets A.

**What we know**:
- The sumset A + A has |A|(|A|+1)/2 elements (by Sidon property)
- The sumset spans at most 2(max A - min A)
- A + A can't contain too many consecutive integers (Erdős-Sárközy-Sós)
- Some large gaps must exist

**Open**:
- Does the average SQUARED gap diverge?
- This would quantify the "irregularity" of Sidon sumsets

**Intuition**: The squared gap emphasizes large gaps. If the conjecture is true,
it means that as Sidon sets grow, they must have increasingly irregular sumsets
with some gaps much larger than average.
-/

theorem erdos_153_summary : True := trivial

end Erdos153

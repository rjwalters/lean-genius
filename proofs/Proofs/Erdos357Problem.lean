/-
  Erdős Problem #357: Distinct Consecutive Sums

  Source: https://erdosproblems.com/357
  Status: OPEN (partial results)

  Statement:
  Let 1 ≤ a₁ < a₂ < ... < aₖ ≤ n be integers such that all sums of the form
  Σᵢ₌ᵤᵛ aᵢ are distinct. Let f(n) be the maximal such k.

  How does f(n) grow? Is f(n) = o(n)?

  Known Results:
  - Weisenberg: f(n) ≥ (2 + o(1))√n
  - Hegyvári (1986): For non-monotone version g(n), (1/3 + o(1))n ≤ g(n) ≤ (2/3 + o(1))n
  - Lower density of any such infinite set is 0

  Related: Problems #34, #356, #670, #867, #421 (multiplicative analogue)

  References:
  [Er77c] Erdős (1977), "Problems and results on combinatorial number theory III"
  [He86] Hegyvári (1986), "On consecutive sums in sequences"

  Tags: combinatorics, number-theory, distinct-sums
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sum
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos357

open Nat Filter Asymptotics Finset

/-! ## Part I: Consecutive Sums and Distinct Sums Property -/

/-- A finset of indices is ord-connected if it forms a contiguous interval.
    For I ⊆ {0, 1, ..., k-1}, this means I = {u, u+1, ..., v} for some u ≤ v. -/
def IsContiguousInterval (I : Finset ℕ) : Prop :=
  ∃ u v, u ≤ v ∧ I = Finset.Icc u v

/-- A sequence has distinct consecutive sums if all contiguous subsequence sums are different.
    That is, for distinct intervals I ≠ J, we have Σᵢ∈I aᵢ ≠ Σⱼ∈J aⱼ. -/
def HasDistinctConsecutiveSums (a : ℕ → ℤ) (k : ℕ) : Prop :=
  ∀ I J : Finset ℕ, I ⊆ Finset.range k → J ⊆ Finset.range k →
    IsContiguousInterval I → IsContiguousInterval J → I ≠ J →
      ∑ i ∈ I, a i ≠ ∑ j ∈ J, a j

/-- Alternative definition: injectivity on contiguous intervals. -/
def HasDistinctSums' (a : Fin k → ℤ) : Prop :=
  ∀ I J : Finset (Fin k), I.val.toFinset.OrdConnected → J.val.toFinset.OrdConnected →
    (∑ i ∈ I, a i) = (∑ j ∈ J, a j) → I = J

/-! ## Part II: The Function f(n) -/

/-- A valid sequence for f(n): strictly increasing integers in [1, n] with distinct consecutive sums. -/
def IsValidSequence (n k : ℕ) (a : Fin k → ℤ) : Prop :=
  (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
  (∀ i j : Fin k, i < j → a i < a j) ∧
  HasDistinctSums' a

/-- f(n) = maximum k such that there exist 1 ≤ a₁ < ... < aₖ ≤ n with distinct consecutive sums. -/
noncomputable def f (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ, IsValidSequence n k a}

/-- f(n) is well-defined: the empty sequence is always valid. -/
theorem f_nonempty (n : ℕ) : {k : ℕ | ∃ a : Fin k → ℤ, IsValidSequence n k a}.Nonempty := by
  use 0
  use Fin.elim0
  constructor
  · intro i; exact Fin.elim0 i
  constructor
  · intro i j; exact Fin.elim0 i
  · intro I J _ _ _
    simp [Finset.sum_empty]
    sorry

/-! ## Part III: Trivial Bounds -/

/-- Trivial upper bound: f(n) ≤ n (can't have more than n distinct values in [1,n]). -/
theorem f_le_n (n : ℕ) : f n ≤ n := by
  sorry

/-- Any single element works: f(n) ≥ 1 for n ≥ 1. -/
theorem f_ge_one (n : ℕ) (hn : n ≥ 1) : f n ≥ 1 := by
  sorry

/-- Two elements work if n ≥ 2: {1, 2} gives sums 1, 2, 3 all distinct. -/
theorem f_ge_two (n : ℕ) (hn : n ≥ 2) : f n ≥ 2 := by
  sorry

/-! ## Part IV: Counting Consecutive Sums -/

/-- The number of contiguous intervals in {1, ..., k} is k(k+1)/2.
    These are: single elements (k), pairs (k-1), triples (k-2), ..., full sequence (1). -/
theorem count_contiguous_intervals (k : ℕ) :
    (Finset.filter IsContiguousInterval (Finset.powerset (Finset.range k))).card =
      k * (k + 1) / 2 := by
  sorry

/-- Upper bound on f(n): since we need k(k+1)/2 distinct sums, and sums are at most k·n,
    we need k(k+1)/2 ≤ k·n, giving k ≤ 2n. (This is very weak.) -/
theorem f_le_2n (n : ℕ) : f n ≤ 2 * n := by
  sorry

/-! ## Part V: Weisenberg's Lower Bound -/

/-- **Weisenberg's Lower Bound**

    f(n) ≥ (2 + o(1))√n

    This uses the connection to B₂ sequences (Sidon sets).
    A B₂ sequence satisfies this problem's condition. -/
axiom weisenberg_lower_bound :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop, (2 + o n) * Real.sqrt n ≤ (f n : ℝ)

/-- Corollary: f(n) grows at least like √n. -/
theorem f_grows_at_least_sqrt :
    ∃ C > 0, ∀ᶠ n in atTop, C * Real.sqrt n ≤ (f n : ℝ) := by
  obtain ⟨o, ho, hbound⟩ := weisenberg_lower_bound
  use 1
  constructor
  · norm_num
  · sorry

/-! ## Part VI: The Main Conjecture -/

/-- **Erdős Problem #357 (Main Conjecture)**

    Is f(n) = o(n)?

    That is, does f(n)/n → 0 as n → ∞?
    This would mean sequences with distinct consecutive sums are sparse. -/
def Erdos357Conjecture : Prop :=
  (fun n => (f n : ℝ)) =o[atTop] (fun n => (n : ℝ))

/-- Alternative formulation: f(n)/n → 0. -/
def Erdos357ConjectureAlt : Prop :=
  Tendsto (fun n => (f n : ℝ) / n) atTop (𝓝 0)

/-- The two formulations are equivalent. -/
theorem conjecture_equiv : Erdos357Conjecture ↔ Erdos357ConjectureAlt := by
  sorry

/-! ## Part VII: The Non-Monotone Variant g(n) -/

/-- g(n) = maximum k for 1 ≤ a₁, ..., aₖ ≤ n (not necessarily increasing)
    with distinct consecutive sums. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ,
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧ HasDistinctSums' a}

/-- g(n) ≥ f(n) since every valid sequence for f is valid for g. -/
theorem g_ge_f (n : ℕ) : g n ≥ f n := by
  sorry

/-- **Hegyvári (1986)**: (1/3 + o(1))n ≤ g(n) ≤ (2/3 + o(1))n. -/
axiom hegyvari_1986 :
    ∃ (o o' : ℕ → ℝ), o =o[atTop] (1 : ℕ → ℝ) ∧ o' =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop, (1/3 + o n) * n ≤ (g n : ℝ) ∧ (g n : ℝ) ≤ (2/3 + o' n) * n

/-- Corollary: g(n) = Θ(n). -/
theorem g_linear_growth :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ C₁ < C₂ ∧
      ∀ᶠ n in atTop, C₁ * n ≤ (g n : ℝ) ∧ (g n : ℝ) ≤ C₂ * n := by
  sorry

/-! ## Part VIII: The Weakly Monotone Variant h(n) -/

/-- h(n) = maximum k for 1 ≤ a₁ ≤ a₂ ≤ ... ≤ aₖ ≤ n (weakly increasing)
    with distinct consecutive sums. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ a : Fin k → ℤ,
    (∀ i, 1 ≤ a i ∧ a i ≤ n) ∧
    (∀ i j : Fin k, i ≤ j → a i ≤ a j) ∧
    HasDistinctSums' a}

/-- h(n) ≥ f(n) since strictly increasing implies weakly increasing. -/
theorem h_ge_f (n : ℕ) : h n ≥ f n := by
  sorry

/-- Is h(n) = o(n)? This is analogous to the main conjecture. -/
def MonotoneConjecture : Prop :=
  (fun n => (h n : ℝ)) =o[atTop] (fun n => (n : ℝ))

/-! ## Part IX: Infinite Sets -/

/-- An infinite set with distinct consecutive sums. -/
def InfiniteDistinctSums (A : ℕ → ℕ) : Prop :=
  StrictMono A ∧ ∀ k, HasDistinctConsecutiveSums (fun i => (A i : ℤ)) k

/-- **Known Result**: Any infinite set with distinct consecutive sums has lower density 0. -/
axiom infinite_set_lower_density_zero (A : ℕ → ℕ) (hA : InfiniteDistinctSums A) :
    Filter.liminf (fun n => ({k | A k ≤ n}.toFinset.card : ℝ) / n) atTop = 0

/-- **Conjecture**: Any such infinite set has density 0 (not just lower density). -/
def InfiniteDensityZeroConjecture : Prop :=
  ∀ A : ℕ → ℕ, InfiniteDistinctSums A →
    Tendsto (fun n => ({k | A k ≤ n}.toFinset.card : ℝ) / n) atTop (𝓝 0)

/-- **Conjecture**: For any such infinite set, Σ 1/aₖ converges. -/
def InfiniteSumConvergesConjecture : Prop :=
  ∀ A : ℕ → ℕ, InfiniteDistinctSums A → Summable (fun i => (1 : ℝ) / A i)

/-! ## Part X: Examples -/

/-- The sequence {1} has distinct sums trivially. -/
example : HasDistinctConsecutiveSums (fun _ => (1 : ℤ)) 1 := by
  intro I J hI hJ hIcont hJcont hne
  simp only [Finset.range_one, Finset.subset_singleton_iff] at hI hJ
  cases hI <;> cases hJ <;> simp_all

/-- The sequence {1, 2} has sums 1, 2, 3 all distinct. -/
theorem example_1_2 : HasDistinctConsecutiveSums (![1, 2]) 2 := by
  sorry

/-- The sequence {1, 2, 4} has sums 1, 2, 4, 3, 6, 7 all distinct. -/
theorem example_1_2_4 : HasDistinctConsecutiveSums (![1, 2, 4]) 3 := by
  sorry

/-- Powers of 2 work: {1, 2, 4, 8, ...} has all distinct consecutive sums.
    This is because Σᵢ₌ᵤᵛ 2^(aᵢ) determines the set {u, ..., v} uniquely. -/
theorem powers_of_2_distinct : ∀ k, HasDistinctConsecutiveSums (fun i => (2^i : ℤ)) k := by
  sorry

/-! ## Part XI: Connection to B₂ Sequences -/

/-- A B₂ sequence (Sidon set) has all pairwise sums distinct:
    a_i + a_j = a_k + a_l implies {i,j} = {k,l}. -/
def IsB2Sequence (a : ℕ → ℤ) : Prop :=
  ∀ i j k l, a i + a j = a k + a l → ({i, j} : Set ℕ) = {k, l}

/-- B₂ sequences have distinct consecutive sums (consecutive sums are a special case). -/
theorem B2_implies_distinct_consecutive (a : ℕ → ℤ) (hB2 : IsB2Sequence a) :
    ∀ k, HasDistinctConsecutiveSums a k := by
  sorry

/-- The maximum size of a B₂ sequence in [1, n] is (1 + o(1))√n. -/
axiom B2_max_size :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ᶠ n in atTop, ∀ a : ℕ → ℤ, IsB2Sequence a →
        (∀ i, 1 ≤ a i ∧ a i ≤ n) →
          ∃ k, k ≤ (1 + o n) * Real.sqrt n ∧ ∀ i ≥ k, a i > n

/-! ## Part XII: Related Problems -/

/-- Problem #874: Sequences where all subset sums are distinct.
    Such sequences also have distinct consecutive sums. -/
def HasDistinctSubsetSums (a : Fin k → ℤ) : Prop :=
  Function.Injective (fun S : Finset (Fin k) => ∑ i ∈ S, a i)

/-- Distinct subset sums implies distinct consecutive sums. -/
theorem subset_sums_implies_consecutive (a : Fin k → ℤ)
    (h : HasDistinctSubsetSums a) : HasDistinctSums' a := by
  sorry

/-- Problem #421: The multiplicative analogue asks about distinct consecutive products. -/
def HasDistinctConsecutiveProducts (a : ℕ → ℤ) (k : ℕ) : Prop :=
  ∀ I J : Finset ℕ, I ⊆ Finset.range k → J ⊆ Finset.range k →
    IsContiguousInterval I → IsContiguousInterval J → I ≠ J →
      ∏ i ∈ I, a i ≠ ∏ j ∈ J, a j

end Erdos357

/-!
## Summary

This file formalizes Erdős Problem #357 on distinct consecutive sums.

**Status**: OPEN (with partial results)

**The Problem**: Let f(n) = max k such that there exist 1 ≤ a₁ < ... < aₖ ≤ n
with all consecutive sums Σᵢ₌ᵤᵛ aᵢ distinct. Is f(n) = o(n)?

**Known Results**:
- Weisenberg: f(n) ≥ (2 + o(1))√n
- Hegyvári (1986): For non-monotone g(n), (1/3 + o(1))n ≤ g(n) ≤ (2/3 + o(1))n
- Lower density of any infinite such set is 0

**What we formalize**:
1. Distinct consecutive sums property
2. The function f(n) and its variants g(n), h(n)
3. Counting contiguous intervals
4. Weisenberg's lower bound (axiomatized)
5. Hegyvári's bounds for g(n) (axiomatized)
6. The main conjecture: f(n) = o(n)?
7. Infinite sets and density
8. Connection to B₂ sequences
9. Examples: {1,2,4}, powers of 2

**Key axioms**:
- `weisenberg_lower_bound`: f(n) ≥ (2 + o(1))√n
- `hegyvari_1986`: (1/3)n ≤ g(n) ≤ (2/3)n
- `infinite_set_lower_density_zero`: infinite sets have lower density 0

**Related Problems**: #34, #356, #670, #867, #421, #874
-/

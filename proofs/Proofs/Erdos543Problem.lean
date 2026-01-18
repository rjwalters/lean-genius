/-
  Erdős Problem #543: Random Subset Sums in Abelian Groups

  Source: https://erdosproblems.com/543
  Status: OPEN

  Statement:
  Define f(N) to be the minimal k such that: if G is an abelian group of
  size N and A ⊆ G is a random set of size k, then with probability ≥ 1/2,
  all elements of G can be written as ∑_{x ∈ S} x for some S ⊆ A.

  Question: Is f(N) ≤ log₂ N + o(log log N)?

  Known Results:
  - Erdős-Rényi (1965): f(N) ≤ log₂ N + O(log log N)

  Erdős's Belief:
  Erdős believed improving O(log log N) to o(log log N) is IMPOSSIBLE.
  This suggests the answer to the question is likely NO.

  References:
  - [ErRe65] Erdős-Rényi: Probabilistic Methods in Group Theory (1965)

  Tags: combinatorics, group-theory, probability, additive-combinatorics
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Fintype
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic

namespace Erdos543

open Finset Real

/-! ## Part I: Subset Sums in Groups -/

/-- The set of all subset sums of a finite set A in an additive group. -/
def subsetSums {G : Type*} [AddCommGroup G] (A : Finset G) : Set G :=
  { g | ∃ S : Finset G, S ⊆ A ∧ S.sum id = g }

/-- A set A is a spanning set if every element of G is a subset sum of A. -/
def IsSpanningSet {G : Type*} [AddCommGroup G] [Fintype G] (A : Finset G) : Prop :=
  ∀ g : G, g ∈ subsetSums A

/-- Alternative: the subset sums cover the entire group. -/
theorem isSpanningSet_iff {G : Type*} [AddCommGroup G] [Fintype G] (A : Finset G) :
    IsSpanningSet A ↔ subsetSums A = Set.univ := by
  unfold IsSpanningSet
  simp only [Set.eq_univ_iff_forall]

/-! ## Part II: The Function f(N) -/

/-- The probability that a random k-subset of G is a spanning set.
    This is the fraction of k-subsets that span G. -/
noncomputable def spanningProbability (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] (k : ℕ) : ℝ :=
  let allSubsets := (Fintype.elems : Finset G).powersetCard k
  let spanningSubsets := allSubsets.filter (fun A => ∀ g : G, g ∈ subsetSums A)
  (spanningSubsets.card : ℝ) / (allSubsets.card : ℝ)

/-- f(N) is the minimal k such that a random k-subset spans G with probability ≥ 1/2. -/
noncomputable def minimalSpanningSize (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] : ℕ :=
  Nat.find (⟨Fintype.card G, by
    -- A set of size |G| certainly spans (take the whole group minus what you need)
    sorry⟩ : ∃ k, spanningProbability G k ≥ 1/2)

/-- The function f from the problem statement. -/
noncomputable def f (N : ℕ) : ℕ :=
  -- Take supremum over all abelian groups of size N
  -- In practice, we'd need to show this is well-defined
  sorry

/-! ## Part III: Elementary Properties -/

/-- The empty set only spans the trivial group. -/
theorem empty_spanning_iff {G : Type*} [AddCommGroup G] [Fintype G] :
    IsSpanningSet (∅ : Finset G) ↔ Fintype.card G = 1 := by
  constructor
  · intro h
    -- If ∅ spans, then every element is a sum of empty subset = 0
    -- So G = {0}, hence |G| = 1
    sorry
  · intro hcard
    -- If |G| = 1, then G = {0} and ∅ trivially spans
    intro g
    use ∅
    simp only [empty_subset, sum_empty, true_and]
    -- g must be 0 since |G| = 1
    sorry

/-- A set containing all generators spans. -/
theorem spanning_of_generators {G : Type*} [AddCommGroup G] [Fintype G]
    (A : Finset G) (hgen : ∀ g : G, ∃ S : Finset G, S ⊆ A ∧ S.sum id = g) :
    IsSpanningSet A := hgen

/-- Adding elements can only increase spanning probability. -/
theorem spanningProbability_mono {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (hk₂ : k₂ ≤ Fintype.card G) :
    spanningProbability G k₁ ≤ spanningProbability G k₂ := by
  -- Larger sets are more likely to span
  sorry

/-! ## Part IV: The Erdős-Rényi Upper Bound -/

/-- Erdős-Rényi (1965): f(N) ≤ log₂ N + O(log log N).

More precisely, there exists a constant C such that for all N ≥ 2,
f(N) ≤ ⌈log₂ N⌉ + C · log(log N).
-/
theorem erdos_renyi_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      (f N : ℝ) ≤ Real.logb 2 N + C * Real.log (Real.log N) := by
  sorry

/-- Restatement: f(N) = log₂ N + O(log log N). -/
theorem f_asymptotic_upper :
    ∃ C : ℝ, ∀ N : ℕ, N ≥ 4 →
      (f N : ℝ) ≤ Real.logb 2 N + C * Real.log (Real.log N) :=
  erdos_renyi_upper_bound.imp fun C ⟨_, h⟩ => fun N hN => h N (by omega)

/-! ## Part V: The Conjecture -/

/-- The question asks: can we improve O(log log N) to o(log log N)?

Formally: Is it true that for every ε > 0, there exists N₀ such that
for all N ≥ N₀, f(N) ≤ log₂ N + ε · log log N?
-/
def LittleOConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    (f N : ℝ) ≤ Real.logb 2 N + ε * Real.log (Real.log N)

/-- Erdős believed the answer is NO - the O(log log N) term cannot be improved.

This would mean there exists ε > 0 such that for infinitely many N,
f(N) > log₂ N + ε · log log N.
-/
def ErdosCounterConjecture : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N ≥ N₀ ∧
    (f N : ℝ) > Real.logb 2 N + ε * Real.log (Real.log N)

/-- The two conjectures are negations of each other. -/
theorem conjectures_complementary : LittleOConjecture ↔ ¬ErdosCounterConjecture := by
  unfold LittleOConjecture ErdosCounterConjecture
  push_neg
  constructor <;> intro h
  · intro ⟨ε, hε, hN⟩
    obtain ⟨N₀, hN₀⟩ := h ε hε
    obtain ⟨N, hNge, hNgt⟩ := hN N₀
    exact (hNgt.trans_le (hN₀ N hNge)).false
  · intro ε hε
    by_contra hc
    push_neg at hc
    exact h ε hε (fun N₀ => ⟨N₀, le_refl _, hc N₀⟩)

/-! ## Part VI: Lower Bound Intuition -/

/-- A random k-subset has 2^k possible subset sums.
    To cover N elements, we need roughly 2^k ≥ N, i.e., k ≥ log₂ N. -/
theorem naive_lower_bound (N : ℕ) (hN : N ≥ 2) :
    (f N : ℝ) ≥ Real.logb 2 N - 1 := by
  -- A k-subset has at most 2^k distinct subset sums
  -- If 2^k < N, we can't cover all elements
  sorry

/-- The log log N term arises from collision probability analysis.

When k ≈ log₂ N, there are roughly N possible subset sums but they
collide with probability that depends on the group structure.
The extra O(log log N) terms handle these collisions with high probability.
-/
theorem collision_intuition :
    True := trivial -- Placeholder for the conceptual explanation

/-! ## Part VII: Special Cases -/

/-- For cyclic groups ℤ/Nℤ, the problem has additional structure. -/
def f_cyclic (N : ℕ) : ℕ :=
  minimalSpanningSize (ZMod N)

/-- The cyclic case: every element must be representable as a subset sum. -/
theorem cyclic_spanning_characterization (N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    IsSpanningSet A ↔ ∀ m : ZMod N, ∃ S : Finset (ZMod N), S ⊆ A ∧ S.sum id = m := by
  rfl

/-- For prime p, the structure is particularly nice. -/
theorem prime_case_structure (p : ℕ) [hp : Fact p.Prime] :
    ∀ A : Finset (ZMod p), A.card ≥ p → IsSpanningSet A := by
  -- If |A| ≥ p in ℤ/pℤ, then A = ℤ/pℤ, so certainly spanning
  sorry

end Erdos543

/-! ## Summary

This file formalizes Erdős Problem #543 on random subset sums in abelian groups.

**Status**: OPEN

**The Question**: Is f(N) ≤ log₂ N + o(log log N)?

**Known Results**:
- Erdős-Rényi (1965): f(N) ≤ log₂ N + O(log log N)
- Naive lower bound: f(N) ≥ log₂ N - O(1)

**Erdős's Belief**: The answer is NO - the O(log log N) term is tight.

**What we formalize**:
1. Subset sums and spanning sets in abelian groups
2. The function f(N) as minimal size for probability ≥ 1/2 spanning
3. The Erdős-Rényi upper bound
4. Both the "little-o" conjecture and Erdős's counter-conjecture
5. Special cases: cyclic groups, primes

**Key sorries**:
- `erdos_renyi_upper_bound`: The main 1965 result (probabilistic argument)
- `spanningProbability_mono`: Monotonicity in k
- `naive_lower_bound`: Information-theoretic lower bound

**What would resolve this**:
- Prove LittleOConjecture: Show f(N) ≤ log₂ N + o(log log N)
- Prove ErdosCounterConjecture: Construct groups where the log log N term is necessary
-/

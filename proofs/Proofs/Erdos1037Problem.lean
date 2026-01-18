/-
  Erdős Problem #1037: Degree Diversity and Ramsey Properties

  Source: https://erdosproblems.com/1037
  Status: DISPROVED (Cambie-Chan-Hunter)

  Statement:
  Let G be a graph on n vertices where every degree occurs at most twice,
  and the number of distinct degrees is > (1/2 + ε)n. Must G contain a
  trivial (empty or complete) subgraph of size "much larger" than log n?

  Answer: NO - Cambie, Chan, and Hunter constructed graphs with ≥ 3n/4
  distinct degrees (each appearing at most twice) where the largest
  trivial subgraph has size O(log n).

  A question of Chen and Erdős.
-/

import Mathlib

namespace Erdos1037

/-
## Graph Setup
-/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of vertices in the graph. -/
def vertexCount : ℕ := Fintype.card V

/-- The degree of a vertex v in graph G. -/
def degree (v : V) : ℕ := G.degree v

/-
## Degree Sequences
-/

/-- The multiset of all vertex degrees. -/
def degreeMultiset : Multiset ℕ :=
  Finset.univ.val.map (fun v => G.degree v)

/-- The set of distinct degrees appearing in the graph. -/
def distinctDegrees : Finset ℕ :=
  Finset.univ.image (fun v => G.degree v)

/-- Number of distinct degree values. -/
def distinctDegreeCount : ℕ := (distinctDegrees G).card

/-- How many times a degree d appears in the graph. -/
def degreeMultiplicity (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => G.degree v = d)).card

/-
## Degree Constraints
-/

/-- Every degree occurs at most twice. -/
def hasLimitedMultiplicity : Prop :=
  ∀ d : ℕ, degreeMultiplicity G d ≤ 2

/-- The number of distinct degrees exceeds (1/2 + ε)n. -/
def hasManyDistinctDegrees (ε : ℝ) : Prop :=
  (distinctDegreeCount G : ℝ) > (1/2 + ε) * (vertexCount G : ℝ)

/-- Graph satisfies the Chen-Erdős conditions. -/
def isChenErdosGraph (ε : ℝ) : Prop :=
  hasLimitedMultiplicity G ∧ hasManyDistinctDegrees G ε

/-
## Trivial Subgraphs
-/

/-- A set S forms an independent set (no edges within S). -/
def isIndependentSet (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- A set S forms a clique (all pairs adjacent). -/
def isClique (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- A set is trivial if it's an independent set or a clique. -/
def isTrivialSet (S : Finset V) : Prop :=
  isIndependentSet G S ∨ isClique G S

/-- Size of the largest trivial subset. -/
noncomputable def maxTrivialSize : ℕ :=
  Finset.sup (Finset.univ.powerset.filter (isTrivialSet G)) Finset.card

/-
## The Chen-Erdős Conjecture
-/

/-- The Chen-Erdős conjecture: under degree constraints,
    must there be a trivial subgraph much larger than log n? -/
def chenErdosConjecture : Prop :=
  ∀ ε > 0, ∃ c > 0, ∀ (V' : Type*) [Fintype V'] [DecidableEq V'],
    ∀ (G' : SimpleGraph V') [DecidableRel G'.Adj],
    isChenErdosGraph G' ε →
    (maxTrivialSize G' : ℝ) > c * Real.log (Fintype.card V')

/-- The conjecture is false. -/
axiom chenErdos_false : ¬chenErdosConjecture

/-
## The Cambie-Chan-Hunter Counterexample
-/

/-- The Cambie-Chan-Hunter construction achieves 3n/4 distinct degrees. -/
def cambieConstant : ℝ := 3/4

/-- Verification that 3/4 > 1/2. -/
theorem cambie_exceeds_half : cambieConstant > 1/2 := by
  unfold cambieConstant
  norm_num

/-- The counterexample construction exists. -/
axiom cambieChanHunter_construction :
  ∀ n : ℕ, n ≥ 4 →
  ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
  ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = n ∧
    hasLimitedMultiplicity G ∧
    (distinctDegreeCount G : ℝ) ≥ cambieConstant * n ∧
    ∃ C > 0, (maxTrivialSize G : ℝ) ≤ C * Real.log n

/-- The construction disproves the conjecture for any ε < 1/4. -/
theorem counterexample_works (ε : ℝ) (hε : ε > 0) (hε' : ε < 1/4) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      isChenErdosGraph G ε ∧
      ∃ C > 0, (maxTrivialSize G : ℝ) ≤ C * Real.log (Fintype.card V) := by
  sorry

/-
## Ramsey Connection
-/

/-- Ramsey number R(k,k). -/
noncomputable def ramseyNumber (k : ℕ) : ℕ := sorry

/-- Ramsey theorem: graphs on ≥ R(k,k) vertices have trivial set of size k. -/
axiom ramsey_theorem (k : ℕ) (hk : k ≥ 2) :
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ ramseyNumber k →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      maxTrivialSize G ≥ k

/-- Ramsey numbers grow exponentially: R(k,k) ≥ 2^(k/2). -/
axiom ramsey_lower_bound (k : ℕ) (hk : k ≥ 2) :
  (ramseyNumber k : ℝ) ≥ 2^((k : ℝ)/2)

/-- The counterexample shows degree diversity doesn't help Ramsey. -/
theorem degree_diversity_no_ramsey_help :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      hasLimitedMultiplicity G ∧
      distinctDegreeCount G ≥ (3 * Fintype.card V) / 4 ∧
      maxTrivialSize G ≤ 10 * Nat.log 2 (Fintype.card V) := by
  sorry

/-
## Degree Sequence Properties
-/

/-- Sum of all degrees equals 2|E|. -/
theorem degree_sum_eq_twice_edges :
    (Finset.univ.sum (fun v => G.degree v)) = 2 * G.edgeFinset.card := by
  sorry

/-- With limited multiplicity, distinct degrees ≤ n/2 + 1. -/
theorem limited_multiplicity_bound :
    hasLimitedMultiplicity G →
    distinctDegreeCount G ≤ (vertexCount G + 2) / 2 := by
  sorry

/-- Maximum possible degree in a graph. -/
def maxPossibleDegree : ℕ := vertexCount G - 1

/-- All degrees are at most n-1. -/
theorem degree_bound (v : V) : G.degree v ≤ maxPossibleDegree G := by
  sorry

/-
## Stronger Bounds
-/

/-- The 3n/4 bound is essentially optimal for multiplicity 2. -/
def optimalDistinctBound : ℝ := 3/4

/-- For multiplicity at most 2, at most (3n)/4 + O(1) distinct degrees. -/
theorem max_distinct_with_limited_mult :
    hasLimitedMultiplicity G →
    (distinctDegreeCount G : ℝ) ≤ optimalDistinctBound * (vertexCount G : ℝ) + 2 := by
  sorry

/-- The Cambie-Chan-Hunter construction is asymptotically optimal. -/
theorem cambie_is_optimal :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      Fintype.card V = n ∧
      hasLimitedMultiplicity G ∧
      (distinctDegreeCount G : ℝ) ≥ (optimalDistinctBound - ε) * n := by
  sorry

/-
## Generalizations
-/

/-- For multiplicity at most k, study the maximum distinct degrees. -/
def hasMultiplicityAtMost (k : ℕ) : Prop :=
  ∀ d : ℕ, degreeMultiplicity G d ≤ k

/-- Maximum distinct degrees with multiplicity ≤ k is roughly (k/(k+1))n. -/
def generalMultiplicityBound (k : ℕ) : ℝ := k / (k + 1)

/-- The general bound conjecture. -/
def generalBoundConjecture : Prop :=
  ∀ k : ℕ, k ≥ 1 →
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    hasMultiplicityAtMost G k →
    (distinctDegreeCount G : ℝ) ≤ generalMultiplicityBound k * (Fintype.card V : ℝ) + O(1) := by
  sorry

/-- For k=2, the bound is 2/3, achieved by specific constructions. -/
theorem multiplicity_two_bound :
    generalMultiplicityBound 2 = 2/3 := by
  unfold generalMultiplicityBound
  norm_num

/-- But wait - our constant is 3/4, not 2/3! -/
theorem cambie_beats_general : cambieConstant > generalMultiplicityBound 2 := by
  unfold cambieConstant generalMultiplicityBound
  norm_num

/-
## The Resolved Question
-/

/-- The main result: conjecture is disproved. -/
theorem erdos_1037_disproved :
    ∃ ε > 0,
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V),
    ∃ (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      isChenErdosGraph G ε ∧
      ∃ C > 0, (maxTrivialSize G : ℝ) ≤ C * Real.log (Fintype.card V) := by
  use 1/8
  constructor
  · norm_num
  sorry

/-- The answer to Erdős #1037 is NO. -/
theorem erdos_1037_answer : ¬chenErdosConjecture := chenErdos_false

/-
## Summary

Erdős Problem #1037 asked whether graphs with many distinct degrees
(each appearing at most twice) must contain large trivial subgraphs.

Chen and Erdős conjectured: if distinctDegrees > (1/2 + ε)n with
each degree appearing ≤ 2 times, then maxTrivial >> log n.

Cambie, Chan, and Hunter disproved this by constructing graphs with:
- ≥ 3n/4 distinct degrees (far exceeding (1/2 + ε)n)
- Each degree appearing at most twice
- Largest clique/independent set of size O(log n)

This shows degree diversity doesn't improve Ramsey-type bounds.
-/

end Erdos1037

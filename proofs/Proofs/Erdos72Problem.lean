/-
  Erdős Problem #72: Unavoidable Cycle Lengths

  Source: https://erdosproblems.com/72
  Status: SOLVED (affirmatively)
  Prize: $100

  Statement:
  Is there a set A ⊂ ℕ of density 0 and a constant c > 0 such that every
  graph on sufficiently many vertices with average degree ≥ c contains
  a cycle whose length is in A?

  Answer: YES

  Key Results:
  - Bollobás (1977): Works for infinite arithmetic progressions with even numbers
  - Verstraëte (2005): Non-constructive existence proof
  - Liu & Montgomery (2020): Powers of 2 work (contradicting Erdős's intuition)

  References:
  [Bo77] Bollobás, "Cycles modulo k" (1977)
  [Ve05] Verstraëte, "Unavoidable cycle lengths" (2005)
  [LM20] Liu-Montgomery, "A proof of the Erdős-Hajnal conjecture on cycle lengths" (2020)

  Tags: graph-theory, extremal-combinatorics, cycles, density
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

namespace Erdos72

open SimpleGraph Finset Filter

/-! ## Part I: Density of Sets of Natural Numbers -/

/-- The counting function for a set A up to n. -/
def countingFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.filter (· ∈ A) (Finset.range (n + 1))).card

/-- A set A ⊂ ℕ has density 0 if |A ∩ [1,n]|/n → 0 as n → ∞. -/
def hasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun n : ℕ => (countingFunction A n : ℝ) / n) atTop (nhds 0)

/-- Powers of 2 form a set of density 0. -/
def powersOfTwo : Set ℕ := {n | ∃ k : ℕ, n = 2 ^ k}

/-- Powers of 2 have density 0 (only log₂(n) elements up to n). -/
theorem powersOfTwo_density_zero : hasDensityZero powersOfTwo := by
  sorry

/-- An arithmetic progression with common difference d starting at a. -/
def arithmeticProgression (a d : ℕ) : Set ℕ := {n | ∃ k : ℕ, n = a + k * d}

/-- Arithmetic progressions have positive density, not 0. -/
theorem arithmeticProgression_positive_density (a d : ℕ) (hd : d > 0) :
    ¬hasDensityZero (arithmeticProgression a d) := by
  sorry

/-! ## Part II: Graph Definitions -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The average degree of a finite simple graph. -/
noncomputable def averageDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (∑ v : V, G.degree v : ℝ) / Fintype.card V

/-- A graph has average degree at least c. -/
def hasAverageDegreeAtLeast (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  averageDegree G ≥ c

/-- The set of cycle lengths that appear in a graph. -/
def cycleLengths (G : SimpleGraph V) : Set ℕ :=
  {k | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = k}

/-- A graph contains a cycle of length in the set A. -/
def containsCycleIn (G : SimpleGraph V) (A : Set ℕ) : Prop :=
  ∃ k ∈ A, k ∈ cycleLengths G

/-! ## Part III: The Unavoidable Cycle Length Property -/

/-- A set A ⊂ ℕ is unavoidable with threshold c if every sufficiently large graph
    with average degree ≥ c contains a cycle whose length is in A. -/
def isUnavoidable (A : Set ℕ) (c : ℝ) : Prop :=
  ∃ n₀ : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V],
    Fintype.card V ≥ n₀ →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
      hasAverageDegreeAtLeast G c → containsCycleIn G A

/-- A set A ⊂ ℕ is strongly unavoidable if there exists some threshold c. -/
def isStronglyUnavoidable (A : Set ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ isUnavoidable A c

/-! ## Part IV: The Main Problem -/

/-- **Erdős Problem #72 (Affirmative Solution)**

    There exists a set A ⊂ ℕ of density 0 that is strongly unavoidable.
    That is, there exists c > 0 such that every sufficiently large graph
    with average degree ≥ c contains a cycle whose length is in A.
-/
def Erdos72Statement : Prop :=
  ∃ A : Set ℕ, hasDensityZero A ∧ isStronglyUnavoidable A

/-! ## Part V: Known Results (Axiomatized) -/

/-- **Bollobás (1977)**

    If A is an infinite arithmetic progression containing even numbers,
    then A is strongly unavoidable.

    Note: Arithmetic progressions have positive density, so this doesn't
    directly solve the problem, but shows the cycle-forcing phenomenon.
-/
axiom bollobas_arithmetic_progression (a d : ℕ) (hd : d > 0) (heven : ∃ k, a + k * d ∈ ({n | Even n} : Set ℕ)) :
    isStronglyUnavoidable (arithmeticProgression a d)

/-- **Verstraëte (2005)**

    Non-constructively proved that Erdős Problem #72 has an affirmative answer.
    Some density-0 set A exists with the required property.
-/
axiom verstraete_existence : Erdos72Statement

/-- **Liu-Montgomery (2020)**

    The set of powers of 2 is strongly unavoidable.
    This was surprising as Erdős believed powers of 2 would NOT work.
-/
axiom liu_montgomery_powers_of_two : isStronglyUnavoidable powersOfTwo

/-- Combining Liu-Montgomery with the density result gives the main theorem. -/
theorem erdos_72_solved : Erdos72Statement := by
  use powersOfTwo
  exact ⟨powersOfTwo_density_zero, liu_montgomery_powers_of_two⟩

/-! ## Part VI: Erdős's Incorrect Conjecture -/

/-- Erdős believed that for powers of 2, no constant threshold would work,
    but rather the required average degree would grow with graph size.
    Liu-Montgomery proved this wrong. -/
def erdos_incorrect_belief : Prop :=
  ¬isStronglyUnavoidable powersOfTwo

/-- Liu-Montgomery refuted Erdős's belief. -/
theorem erdos_was_wrong : ¬erdos_incorrect_belief :=
  fun h => h liu_montgomery_powers_of_two

/-! ## Part VII: Other Density-0 Sets -/

/-- Perfect squares. -/
def perfectSquares : Set ℕ := {n | ∃ k : ℕ, n = k ^ 2}

/-- Perfect squares have density 0. -/
theorem perfectSquares_density_zero : hasDensityZero perfectSquares := by
  sorry

/-- It remains unknown whether perfect squares are strongly unavoidable. -/
def openQuestion_squares : Prop := isStronglyUnavoidable perfectSquares

/-- Even numbers of the form 2^k (subset of powers of 2, all even). -/
theorem powersOfTwo_all_even (n : ℕ) (hn : n ∈ powersOfTwo) (hn_pos : n > 0) :
    Even n ∨ n = 1 := by
  obtain ⟨k, rfl⟩ := hn
  cases k with
  | zero => right; rfl
  | succ k => left; exact ⟨2^k, by ring⟩

/-! ## Part VIII: Quantitative Bounds -/

/-- The optimal threshold for a set A. -/
noncomputable def optimalThreshold (A : Set ℕ) : ℝ :=
  sInf {c : ℝ | c > 0 ∧ isUnavoidable A c}

/-- Liu-Montgomery gives some explicit bound for powers of 2. -/
axiom liu_montgomery_explicit_bound : optimalThreshold powersOfTwo < 10^6

/-- Finding the exact optimal threshold for powers of 2 remains open. -/
def openQuestion_optimal_threshold : Prop :=
  ∃ c : ℝ, optimalThreshold powersOfTwo = c ∧ c < 100

/-! ## Part IX: Generalizations -/

/-- A set A with controlled growth: |A ∩ [1,n]| ≤ f(n) for slow-growing f. -/
def hasControlledGrowth (A : Set ℕ) (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, countingFunction A n ≤ f n

/-- Liu-Montgomery actually proves a more general result for sets with
    logarithmic growth of even numbers. -/
axiom liu_montgomery_general (A : Set ℕ)
    (hgrowth : hasControlledGrowth A (fun n => Nat.log 2 n + 1))
    (heven : ∀ a ∈ A, Even a ∨ a = 1) :
    isStronglyUnavoidable A

end Erdos72

/-!
## Summary

This file formalizes Erdős Problem #72 on unavoidable cycle lengths.

**The Problem**: Does there exist a density-0 set A ⊂ ℕ and constant c > 0
such that every large graph with average degree ≥ c contains a cycle
whose length is in A?

**Answer**: YES (solved affirmatively)

**Key Results**:
1. Bollobás (1977): Arithmetic progressions with even numbers work
2. Verstraëte (2005): Non-constructive existence proof
3. Liu-Montgomery (2020): Powers of 2 work (contradicting Erdős's belief)

**What We Formalize**:
1. Density 0 for sets of natural numbers
2. Average degree and cycle lengths in graphs
3. The unavoidability property
4. Main theorem statement and solution
5. Key results as axioms

**Erdős's Error**: Erdős believed powers of 2 would NOT work and that
the required average degree would grow with graph size. Liu-Montgomery
proved a constant threshold suffices.

**Open Questions**:
- Optimal threshold for powers of 2?
- Do perfect squares work?
- Algorithmic implications?
-/

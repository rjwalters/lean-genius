/-!
# Erdős Problem #289: Unit Fractions from Disjoint Intervals

Is it true that for all sufficiently large k, there exist k disjoint,
non-adjacent intervals I₁, ..., Iₖ ⊂ ℕ (each with |Iᵢ| ≥ 2) such that
∑ᵢ ∑_{n ∈ Iᵢ} 1/n = 1?

## Key Results

- Erdős–Graham [ErGr80] posed the problem
- Hickerson–Montgomery found 5 intervals summing to 2:
  [2,7], [9,10], [17,18], [34,35], [84,85]
- The disjointness and non-adjacency constraints prevent trivial solutions

## References

- Erdős, Graham (1980): Old and New Problems and Results in Combinatorial
  Number Theory
- <https://erdosproblems.com/289>
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

open Finset

/-! ## Core Definitions -/

/-- An interval block [a, b] ⊂ ℕ with a ≤ b. -/
structure IntervalBlock where
  lo : ℕ
  hi : ℕ
  hlo : 0 < lo
  hle : lo ≤ hi
  hsize : hi - lo + 1 ≥ 2

/-- The elements of an interval block as a finset. -/
def IntervalBlock.toFinset (I : IntervalBlock) : Finset ℕ :=
  Finset.Icc I.lo I.hi

/-- Two interval blocks are disjoint if their ranges don't overlap. -/
def IntervalBlock.Disjoint (I J : IntervalBlock) : Prop :=
  I.hi < J.lo ∨ J.hi < I.lo

/-- Two interval blocks are non-adjacent: there is a gap between them. -/
def IntervalBlock.NonAdjacent (I J : IntervalBlock) : Prop :=
  I.hi + 1 < J.lo ∨ J.hi + 1 < I.lo

/-- The reciprocal sum of an interval block: ∑_{n=lo}^{hi} 1/n. -/
noncomputable def IntervalBlock.recipSum (I : IntervalBlock) : ℚ :=
  ∑ n ∈ I.toFinset, (1 : ℚ) / (n : ℚ)

/-- A valid decomposition: k pairwise disjoint, non-adjacent intervals
    whose reciprocal sums total exactly 1. -/
def ValidDecomposition (k : ℕ) (blocks : Fin k → IntervalBlock) : Prop :=
  (∀ i j : Fin k, i ≠ j → IntervalBlock.NonAdjacent (blocks i) (blocks j)) ∧
  ∑ i : Fin k, (blocks i).recipSum = 1

/-! ## Main Conjecture -/

/-- **Erdős Problem #289** (OPEN): For all sufficiently large k, there exists
    a valid decomposition of 1 into k disjoint non-adjacent interval blocks. -/
axiom erdos_289_conjecture :
  ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    ∃ blocks : Fin k → IntervalBlock, ValidDecomposition k blocks

/-! ## Basic Properties -/

/-- Every interval block has at least 2 elements. -/
theorem interval_block_has_two (I : IntervalBlock) :
    I.toFinset.card ≥ 2 := by
  unfold IntervalBlock.toFinset
  simp [Nat.card_Icc]
  omega

/-- Non-adjacency implies disjointness. -/
theorem nonadj_implies_disjoint (I J : IntervalBlock) :
    IntervalBlock.NonAdjacent I J → IntervalBlock.Disjoint I J := by
  intro h
  unfold IntervalBlock.NonAdjacent at h
  unfold IntervalBlock.Disjoint
  cases h with
  | inl h => left; omega
  | inr h => right; omega

/-! ## Hickerson–Montgomery Example -/

/-- The Hickerson–Montgomery example: 5 intervals summing to 2.
    [2,7], [9,10], [17,18], [34,35], [84,85].
    This shows the feasibility of interval decomposition for targets other than 1. -/
axiom hickerson_montgomery_example :
  ∃ blocks : Fin 5 → IntervalBlock,
    (∀ i j : Fin 5, i ≠ j → IntervalBlock.NonAdjacent (blocks i) (blocks j)) ∧
    ∑ i : Fin 5, (blocks i).recipSum = 2

/-! ## Structural Observations -/

/-- The harmonic series diverges, so the total available reciprocal sum
    from any tail of ℕ is unbounded. This is necessary for the problem
    to have solutions for arbitrarily many blocks. -/
axiom harmonic_tail_diverges :
  ∀ (M : ℕ) (C : ℚ), C > 0 →
    ∃ N : ℕ, N > M ∧ ∑ n ∈ Finset.Icc M N, (1 : ℚ) / (n : ℚ) > C

/-- Each interval block contributes at most 1/lo + ... + 1/hi ≤ (hi-lo+1)/lo. -/
axiom interval_recipsum_upper (I : IntervalBlock) :
  I.recipSum ≤ ((I.hi - I.lo + 1 : ℕ) : ℚ) / (I.lo : ℚ)

/-- Each interval block contributes at least (hi-lo+1)/hi. -/
axiom interval_recipsum_lower (I : IntervalBlock) :
  I.recipSum ≥ ((I.hi - I.lo + 1 : ℕ) : ℚ) / (I.hi : ℚ)

/-- To achieve exactly 1 with many small-contribution blocks, we need
    blocks at large values of n. The gap constraint forces intervals
    to spread out, making the target harder to hit exactly. -/
axiom exact_target_difficulty :
  ∀ k : ℕ, k > 0 →
    ∀ blocks : Fin k → IntervalBlock,
      (∀ i j : Fin k, i ≠ j → IntervalBlock.NonAdjacent (blocks i) (blocks j)) →
        -- The smallest block endpoint grows with k
        ∃ i : Fin k, (blocks i).hi ≥ k

/-- The problem without the non-adjacency constraint is easier: one can
    always decompose 1 into disjoint intervals (Erdős–Graham remark). -/
axiom trivial_without_nonadjacency :
  ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
    ∃ blocks : Fin k → IntervalBlock,
      (∀ i j : Fin k, i ≠ j → IntervalBlock.Disjoint (blocks i) (blocks j)) ∧
      ∑ i : Fin k, (blocks i).recipSum = 1

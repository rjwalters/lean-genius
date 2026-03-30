/-
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

/- ## Core Definitions -/

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

/- ## Main Conjecture -/

/-- **Erdős Problem #289** (OPEN): For all sufficiently large k, there exists
    a valid decomposition of 1 into k disjoint non-adjacent interval blocks. -/
/- ## Basic Properties -/

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

/- ## Hickerson–Montgomery Example -/

/-- The Hickerson–Montgomery example: 5 intervals summing to 2.
    [2,7], [9,10], [17,18], [34,35], [84,85].
    This shows the feasibility of interval decomposition for targets other than 1. -/
/- ## Structural Observations -/

/-- The harmonic series diverges, so the total available reciprocal sum
    from any tail of ℕ is unbounded. This is necessary for the problem
    to have solutions for arbitrarily many blocks. -/
/-- Each interval block contributes at most (hi-lo+1)/lo.
    Proof: each term 1/n ≤ 1/lo since lo ≤ n for n ∈ [lo, hi]. -/
theorem interval_recipsum_upper (I : IntervalBlock) :
    I.recipSum ≤ ((I.hi - I.lo + 1 : ℕ) : ℚ) / (I.lo : ℚ) := by
  unfold IntervalBlock.recipSum IntervalBlock.toFinset
  have hlo_pos : (0 : ℚ) < (I.lo : ℚ) := Nat.cast_pos.mpr I.hlo
  calc ∑ n ∈ Icc I.lo I.hi, (1 : ℚ) / (n : ℚ)
      ≤ ∑ _n ∈ Icc I.lo I.hi, (1 : ℚ) / (I.lo : ℚ) := by
        apply Finset.sum_le_sum; intro n hn
        simp only [mem_Icc] at hn
        have hn_pos : (0 : ℚ) < (n : ℚ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
        exact div_le_div_of_le_left (by positivity) hlo_pos hn_pos
              (Nat.cast_le.mpr hn.1)
    _ = (Icc I.lo I.hi).card • ((1 : ℚ) / (I.lo : ℚ)) := sum_const _
    _ = ((I.hi - I.lo + 1 : ℕ) : ℚ) / (I.lo : ℚ) := by
        rw [Nat.card_Icc]; simp [nsmul_eq_mul]

/-- Each interval block contributes at least (hi-lo+1)/hi.
    Proof: each term 1/n ≥ 1/hi since n ≤ hi for n ∈ [lo, hi]. -/
theorem interval_recipsum_lower (I : IntervalBlock) :
    I.recipSum ≥ ((I.hi - I.lo + 1 : ℕ) : ℚ) / (I.hi : ℚ) := by
  unfold IntervalBlock.recipSum IntervalBlock.toFinset
  have hhi_pos : (0 : ℚ) < (I.hi : ℚ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
  calc ((I.hi - I.lo + 1 : ℕ) : ℚ) / (I.hi : ℚ)
      = (Icc I.lo I.hi).card • ((1 : ℚ) / (I.hi : ℚ)) := by
        rw [Nat.card_Icc]; simp [nsmul_eq_mul]
    _ = ∑ _n ∈ Icc I.lo I.hi, (1 : ℚ) / (I.hi : ℚ) := (sum_const _).symm
    _ ≤ ∑ n ∈ Icc I.lo I.hi, (1 : ℚ) / (n : ℚ) := by
        apply Finset.sum_le_sum; intro n hn
        simp only [mem_Icc] at hn
        have hn_pos : (0 : ℚ) < (n : ℚ) :=
          Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by omega))
        exact div_le_div_of_le_left (by positivity) hn_pos hhi_pos
              (Nat.cast_le.mpr hn.2)

/-- To achieve exactly 1 with many small-contribution blocks, we need
    blocks at large values of n. The gap constraint forces intervals
    to spread out, making the target harder to hit exactly. -/
/-- The problem without the non-adjacency constraint is easier: one can
    always decompose 1 into disjoint intervals (Erdős–Graham remark). -/

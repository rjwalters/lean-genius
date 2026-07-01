/-
# Erdős Problem #101 — OQ-01 · OQ-02: exact base cases of the extremal function

Parent `Erdos101OQ01.lean` introduces the genuine size-indexed extremal
quantity

  `maxCountAtSize n := sSup { fourPointLineCount Q | |Q| = n, NoFiveCollinear Q }`,

the precise function OQ-01 asks to bound by `o(n²)`, and establishes the
`O(n²)` upper certificate `maxCountAtSize_isBigO_n_squared`. The asymptotic
statements say nothing about the *small* values of this function, yet those
values are the anchor points every candidate growth rate must interpolate.

This file pins the base cases exactly:

  * `maxCountAtSize n = 0` for every `n < 4` (a set with fewer than four
    points has no four-point line — `fourPointLineCount_lt_four`);
  * `maxCountAtSize 4 = 1` (the first non-trivial value): four collinear
    points realise a single four-point line, and the elementary bound
    `improved_upper_bound` (`4·3/12 = 1`) forbids more.

The lower half of `maxCountAtSize 4 = 1` is witnessed by an **explicit**
no-five-collinear configuration — four points on the `x`-axis — for which
`fourPointLineCount = 1` is computed directly from the definition (the only
cardinality-`4` subset of a four-element set is the set itself). This is the
smallest concrete lower-bound witness for OQ-01, complementing the deferred
Solymosi–Stojaković near-quadratic construction at the opposite end.

All results here are unconditional and axiom-free: no `sorry`, no `axiom`,
and no dependence on the parent's two deferred obligations (the open
conjecture and the Solymosi–Stojaković lower bound).
-/
import Proofs.Erdos101OQ01

open Classical
open Erdos101OQ01

namespace Erdos101OQ01OQ02

/-! ### Base values `n < 4`: the extremal function vanishes -/

/-- For every size `n < 4` the extremal four-point-line function vanishes:
no set of fewer than four points contains a four-point line, so every
candidate count is `0`, hence so is their supremum. Proved by pushing the
uniform bound `fourPointLineCount Q = 0` through `maxCountAtSize_lt_of_forall`
with the real threshold `X = 1`. -/
theorem maxCountAtSize_eq_zero_of_lt_four {n : ℕ} (hn : n < 4) :
    maxCountAtSize n = 0 := by
  have hlt : (maxCountAtSize n : ℝ) < 1 := by
    refine maxCountAtSize_lt_of_forall (by norm_num) ?_
    intro Q hQcard _
    have hz : fourPointLineCount Q = 0 :=
      fourPointLineCount_lt_four Q (by rw [hQcard]; exact hn)
    rw [hz]; norm_num
  have : maxCountAtSize n < 1 := by exact_mod_cast hlt
  omega

/-! ### The explicit witness at size 4

Four points on the `x`-axis: `(0,0), (1,0), (2,0), (3,0)`. They are pairwise
distinct (so the set has cardinality `4`), vacuously no-five-collinear (there
are only four points), and all lie on the single line `y = 0`, giving exactly
one four-point line. -/

/-- The witness point set: four distinct collinear points on the `x`-axis. -/
noncomputable def witness : PlanarPointSet where
  points := {((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0), (3, 0)}
  size_pos := by
    have : ({((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)).Nonempty :=
      ⟨(0, 0), by simp⟩
    exact Finset.card_pos.mpr this

/-- The witness has exactly four points. -/
theorem witness_card : witness.points.card = 4 := by
  show ({((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)).card = 4
  rw [Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Prod.ext_iff]),
      Finset.card_singleton]

/-- The witness is (vacuously) no-five-collinear: it has only four points. -/
theorem witness_noFive : NoFiveCollinear witness :=
  noFiveCollinear_small witness (le_of_eq witness_card)

/-- Every point of the witness lies on the line `y = 0`, hence is collinear
with the two anchors `(0,0)` and `(1,0)`. -/
theorem witness_all_collinear :
    ∀ p ∈ witness.points, collinear ((0 : ℝ), (0 : ℝ)) (1, 0) p := by
  intro p hp
  have hp' : p ∈ ({((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ)) := hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp'
  rcases hp' with rfl | rfl | rfl | rfl <;>
    · unfold collinear; ring

/-- **The witness realises exactly one four-point line.** The only
cardinality-`4` subset of a four-element set is the set itself, and that
subset satisfies the collinearity predicate (anchors `(0,0)`, `(1,0)`), so the
counted family is the singleton `{witness.points}`. -/
theorem witness_fourPointLineCount : fourPointLineCount witness = 1 := by
  have hcard : witness.points.card = 4 := witness_card
  -- The filtered family is exactly `{witness.points}`.
  have hset :
      (witness.points.powerset.filter (fun S =>
        S.card = 4 ∧ ∃ a b : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
          ∀ p ∈ S, collinear a b p)) = {witness.points} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.Subset.refl _, hcard, (0, 0), (1, 0), ?_, ?_, ?_, witness_all_collinear⟩
      · show ((0 : ℝ), (0 : ℝ)) ∈ witness.points
        show ((0 : ℝ), (0 : ℝ)) ∈ ({((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ))
        simp
      · show ((1 : ℝ), (0 : ℝ)) ∈ witness.points
        show ((1 : ℝ), (0 : ℝ)) ∈ ({((0 : ℝ), (0 : ℝ)), (1, 0), (2, 0), (3, 0)} : Finset (ℝ × ℝ))
        simp
      · simp [Prod.ext_iff]
    · intro S hS
      rw [Finset.mem_filter, Finset.mem_powerset] at hS
      exact Finset.eq_of_subset_of_card_le hS.1 (by rw [hcard, hS.2.1])
  unfold fourPointLineCount
  rw [hset, Finset.card_singleton]

/-! ### The first non-trivial value: `maxCountAtSize 4 = 1` -/

/-- **The extremal four-point-line function at size 4 equals 1.**

Lower bound `1 ≤ maxCountAtSize 4`: the explicit witness attains
`fourPointLineCount = 1` (`witness_fourPointLineCount`) at cardinality `4`.

Upper bound `maxCountAtSize 4 ≤ 1`: every no-five-collinear set of four points
has at most `4·3/12 = 1` four-point line (`improved_upper_bound`), pushed
through `maxCountAtSize_lt_of_forall` with threshold `X = 2`. -/
theorem maxCountAtSize_four_eq_one : maxCountAtSize 4 = 1 := by
  refine le_antisymm ?_ ?_
  · -- upper bound
    have hlt : (maxCountAtSize 4 : ℝ) < 2 := by
      refine maxCountAtSize_lt_of_forall (by norm_num) ?_
      intro Q hQcard hQ5
      have hb := improved_upper_bound Q hQ5
      rw [hQcard] at hb
      have hb1 : fourPointLineCount Q ≤ 1 := by norm_num at hb; exact hb
      have : (fourPointLineCount Q : ℝ) ≤ 1 := by exact_mod_cast hb1
      linarith
    have : maxCountAtSize 4 < 2 := by exact_mod_cast hlt
    omega
  · -- lower bound via the explicit witness
    have h := le_maxCountAtSize witness witness_noFive
    rw [witness_fourPointLineCount, witness_card] at h
    exact h

end Erdos101OQ01OQ02

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Walters
-/
import Proofs.Erdos85Ramsey

/-!
# Consecutive star-Ramsey bounds and the Erdős 85 threshold

This module isolates the exact algebraic content of a consecutive bound for
`R(C₄, K_{1,s})`.  The external Ramsey result is deliberately represented by
the named property `ConsecutiveC4StarRamseyBound`; it is not added as an axiom.

With the convention-free predicate `C4StarRamseyAt`, a bound

`R(C₄, K_{1,s+1}) ≤ R(C₄, K_{1,s}) + g`

is used through the implication that a Ramsey guarantee at `(m,s)` gives one
at `(m+g,s+1)`.  Its threshold consequence is

`f(m+g) ≤ f(m) + g - 1`.

In particular, the reported gap-two inequality gives `f(m+2) ≤ f(m)+1`.
This controls upward growth on a two-step subsequence.  It does **not** bound
downward jumps and therefore does not by itself imply `WeakerConjecture`.
-/

namespace Erdos85

/-- Convention-free form of a uniform upper bound on consecutive
`C₄`-versus-star Ramsey numbers.  It is a hypothesis/property, not an axiom. -/
def ConsecutiveC4StarRamseyBound (gap : ℕ) : Prop :=
  ∀ ⦃m s : ℕ⦄, 4 ≤ m → s ≤ m - 1 →
    C4StarRamseyAt m s → C4StarRamseyAt (m + gap) (s + 1)

/-- Exact pointwise threshold translation of a generic consecutive Ramsey
bound.  Side conditions merely exclude the degenerate orders in the Ramsey
translation. -/
theorem consecutiveC4StarRamseyBound_iff_threshold (gap : ℕ) (hgap1 : 1 ≤ gap) :
    ConsecutiveC4StarRamseyBound gap ↔
      ∀ ⦃m s : ℕ⦄, 4 ≤ m → s ≤ m - 1 →
        minDegreeForC4 m ≤ m - s →
        minDegreeForC4 (m + gap) ≤ m + gap - (s + 1) := by
  constructor
  · intro h m s hm hs hthreshold
    have hRamsey : C4StarRamseyAt m s :=
      (c4StarRamseyAt_iff_threshold hm hs).2 hthreshold
    have hnext := h hm hs hRamsey
    have hmnext : 4 ≤ m + gap := by omega
    have hsnext : s + 1 ≤ m + gap - 1 := by omega
    exact (c4StarRamseyAt_iff_threshold hmnext hsnext).1 hnext
  · intro h m s hm hs hRamsey
    have hthreshold : minDegreeForC4 m ≤ m - s :=
      (c4StarRamseyAt_iff_threshold hm hs).1 hRamsey
    have hnext := h hm hs hthreshold
    have hmnext : 4 ≤ m + gap := by omega
    have hsnext : s + 1 ≤ m + gap - 1 := by omega
    exact (c4StarRamseyAt_iff_threshold hmnext hsnext).2 hnext

/-- The clean numerical consequence: a Ramsey gap bound `gap` permits upward
growth of at most `gap - 1` when the order advances by `gap`. -/
theorem minDegreeForC4_add_le_of_consecutiveRamseyBound
    {gap m : ℕ} (hgap : ConsecutiveC4StarRamseyBound gap)
    (hgap1 : 1 ≤ gap) (hm : 4 ≤ m) :
    minDegreeForC4 (m + gap) ≤ minDegreeForC4 m + gap - 1 := by
  have hf_le : minDegreeForC4 m ≤ m - 1 := minDegreeForC4_le_sub_one hm
  have hf_pos : 1 ≤ minDegreeForC4 m := by
    have := two_le_minDegreeForC4 (n := m - 1) (by omega)
    have htwo : 2 ≤ minDegreeForC4 m := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using this
    omega
  let s := m - minDegreeForC4 m
  have hs : s ≤ m - 1 := by dsimp [s]; omega
  have hbase : minDegreeForC4 m ≤ m - s := by dsimp [s]; omega
  have htranslated :=
    (consecutiveC4StarRamseyBound_iff_threshold gap hgap1).1 hgap hm hs hbase
  dsimp [s] at htranslated
  omega

/-- The gap-two specialization associated with the reported consecutive
`C₄`-star Ramsey inequality. -/
theorem minDegreeForC4_add_two_le_add_one
    (hChen : ConsecutiveC4StarRamseyBound 2) {m : ℕ} (hm : 4 ≤ m) :
    minDegreeForC4 (m + 2) ≤ minDegreeForC4 m + 1 := by
  simpa using minDegreeForC4_add_le_of_consecutiveRamseyBound hChen (by norm_num) hm

/-- Iterating the numerical consequence along an arithmetic progression. -/
theorem minDegreeForC4_add_mul_le_of_consecutiveRamseyBound
    {gap m : ℕ} (hgap : ConsecutiveC4StarRamseyBound gap)
    (hgap1 : 1 ≤ gap) (hm : 4 ≤ m) (k : ℕ) :
    minDegreeForC4 (m + k * gap) ≤
      minDegreeForC4 m + k * (gap - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hm' : 4 ≤ m + k * gap := by omega
      have hstep :=
        minDegreeForC4_add_le_of_consecutiveRamseyBound hgap hgap1 hm'
      simp only [Nat.succ_mul]
      have hindex : m + k * gap + gap = m + (k * gap + gap) := by omega
      rw [hindex] at hstep
      omega

/-- Under the gap-two hypothesis, each parity subsequence has slope at most
one half in this precise integral sense. -/
theorem minDegreeForC4_add_twice_le
    (hChen : ConsecutiveC4StarRamseyBound 2) {m : ℕ} (hm : 4 ≤ m) (k : ℕ) :
    minDegreeForC4 (m + 2 * k) ≤ minDegreeForC4 m + k := by
  have h := minDegreeForC4_add_mul_le_of_consecutiveRamseyBound
    hChen (by norm_num) hm k
  simpa [Nat.mul_comm] using h

end Erdos85

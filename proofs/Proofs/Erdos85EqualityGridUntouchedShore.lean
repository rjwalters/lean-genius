import Mathlib

/-!
# Untouched points in the complement of an equality grid

If every row on one coordinate side uses only two points of the shore
complement, a linear-size subset of that complement is untouched by the
entire side.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- A shore complement of size `3q-4`, hit twice by each of `q-2` rows,
contains at least `q` points hit by none of the rows. -/
theorem equalityGrid_q_le_card_untouched_of_two_regular
    {Point Row : Type*} [DecidableEq Point] [DecidableEq Row]
    (Inc : Row → Point → Prop) [DecidableRel Inc]
    (E : Finset Point) (Z : Finset Row) (q : ℕ)
    (hq : 2 ≤ q)
    (hEcard : E.card = 3 * q - 4)
    (hZcard : Z.card = q - 2)
    (hrow : ∀ z ∈ Z, (E.filter fun e => Inc z e).card = 2) :
    q ≤ (E.filter fun e => (Z.filter fun z => Inc z e).card = 0).card := by
  classical
  let T := E.filter fun e => 0 < (Z.filter fun z => Inc z e).card
  let N := E.filter fun e => (Z.filter fun z => Inc z e).card = 0
  have hTle : T.card ≤ ∑ e ∈ E, (Z.filter fun z => Inc z e).card := by
    calc
      T.card = ∑ _e ∈ T, 1 := by simp
      _ ≤ ∑ e ∈ T, (Z.filter fun z => Inc z e).card := by
        apply Finset.sum_le_sum
        intro e he
        exact (Finset.mem_filter.mp he).2
      _ ≤ ∑ e ∈ E, (Z.filter fun z => Inc z e).card := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.filter_subset _ _
  have hdouble : (∑ e ∈ E, (Z.filter fun z => Inc z e).card) = 2 * Z.card := by
    calc
      _ = ∑ z ∈ Z, (E.filter fun e => Inc z e).card := by
        simp only [Finset.card_eq_sum_ones]
        simp_rw [Finset.sum_filter]
        exact Finset.sum_comm
      _ = ∑ _z ∈ Z, 2 := Finset.sum_congr rfl hrow
      _ = 2 * Z.card := by simp [Nat.mul_comm]
  have hNT : Disjoint N T := by
    rw [Finset.disjoint_left]
    intro e heN heT
    have hz := (Finset.mem_filter.mp heN).2
    have hp := (Finset.mem_filter.mp heT).2
    omega
  have hcover : N ∪ T = E := by
    ext e
    constructor
    · intro he
      rcases Finset.mem_union.mp he with heN | heT
      · exact (Finset.mem_filter.mp heN).1
      · exact (Finset.mem_filter.mp heT).1
    · intro he
      by_cases hz : (Z.filter fun z => Inc z e).card = 0
      · exact Finset.mem_union_left T (Finset.mem_filter.mpr ⟨he, hz⟩)
      · have hp : 0 < (Z.filter fun z => Inc z e).card := Nat.pos_of_ne_zero hz
        exact Finset.mem_union_right N (Finset.mem_filter.mpr ⟨he, hp⟩)
  have hcardSplit : N.card + T.card = E.card := by
    rw [← Finset.card_union_of_disjoint hNT, hcover]
  change q ≤ N.card
  have hTle' : T.card ≤ 2 * Z.card := hTle.trans_eq hdouble
  rw [hEcard] at hcardSplit
  rw [hZcard] at hTle'
  omega

end


end Erdos85

#print axioms Erdos85.equalityGrid_q_le_card_untouched_of_two_regular

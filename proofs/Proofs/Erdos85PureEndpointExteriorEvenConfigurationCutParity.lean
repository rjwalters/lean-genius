import Proofs.Erdos85PureEndpointExteriorEvenConfigurationIntersectionParity
import Proofs.Erdos85PureEndpointExteriorRowIntersectionDegree

/-!
# Per-row cut parity of an even exterior configuration
-/

open Finset BigOperators SimpleGraph

namespace Erdos85

noncomputable section

/-- Inside an even linear configuration, the number of other selected blocks
meeting a selected `m`-uniform block has parity `m`. -/
theorem linear_even_configuration_internal_meeting_add_uniform_even
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β) (p : α) (m : ℕ)
    (hp : p ∈ T)
    (huniform : (L.filter fun l => Inc p l).card = m)
    (heven : ∀ l ∈ L, Even ((T.filter fun q => Inc q l).card))
    (hlinear : ∀ q ∈ T.erase p,
      (L.filter fun l => Inc p l ∧ Inc q l).card ≤ 1) :
    Even (m + ((T.erase p).filter fun q =>
      (L.filter fun l => Inc p l ∧ Inc q l).Nonempty).card) := by
  classical
  let block := L.filter fun l => Inc p l
  let d : β → ℕ := fun l => (T.filter fun q => Inc q l).card
  let inter : α → Finset β := fun q =>
    L.filter fun l => Inc p l ∧ Inc q l
  let meet := (T.erase p).filter fun q => (inter q).Nonempty
  have hIeven : Even (∑ l ∈ block, d l) := by
    exact Finset.even_sum _ fun l hl => heven l (mem_filter.mp hl).1
  have hdouble : (∑ l ∈ block, d l) = ∑ q ∈ T, (inter q).card := by
    calc
      (∑ l ∈ block, d l) = ∑ l ∈ L,
          if Inc p l then ∑ q ∈ T, if Inc q l then 1 else 0 else 0 := by
            rw [show block = L.filter fun l => Inc p l by rfl, sum_filter]
            apply sum_congr rfl
            intro l hl
            by_cases hpl : Inc p l
            · simp only [hpl, if_true, d, card_filter]
            · simp [hpl]
      _ = ∑ l ∈ L, ∑ q ∈ T,
          if Inc p l ∧ Inc q l then 1 else 0 := by
            apply sum_congr rfl
            intro l hl
            by_cases hpl : Inc p l
            · simp [hpl]
            · simp [hpl]
      _ = ∑ q ∈ T, ∑ l ∈ L,
          if Inc p l ∧ Inc q l then 1 else 0 := by rw [sum_comm]
      _ = ∑ q ∈ T, (inter q).card := by
            apply sum_congr rfl
            intro q hq
            simp only [inter, card_filter]
  have hself : (inter p).card = m := by
    have heq : inter p = block := by
      ext l
      simp [inter, block]
    rw [heq]
    exact huniform
  have herase : ∑ q ∈ T, (inter q).card =
      (inter p).card + ∑ q ∈ T.erase p, (inter q).card := by
    rw [add_comm, sum_erase_add _ _ hp]
  have hindicator : ∀ q ∈ T.erase p,
      (inter q).card = if (inter q).Nonempty then 1 else 0 := by
    intro q hq
    by_cases hn : (inter q).Nonempty
    · simp only [hn, if_true]
      exact Nat.le_antisymm (hlinear q hq) (card_pos.mpr hn)
    · simp only [hn, if_false]
      exact card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
  have hother : (∑ q ∈ T.erase p, (inter q).card) = meet.card := by
    calc
      (∑ q ∈ T.erase p, (inter q).card) =
          ∑ q ∈ T.erase p, if (inter q).Nonempty then 1 else 0 := by
            apply sum_congr rfl
            intro q hq
            exact hindicator q hq
      _ = meet.card := by simp [meet]
  have hEq : (∑ l ∈ block, d l) = m + meet.card := by
    rw [hdouble, herase, hself, hother]
  simpa [meet, inter] using hEq ▸ hIeven

end

end Erdos85

#print axioms Erdos85.linear_even_configuration_internal_meeting_add_uniform_even

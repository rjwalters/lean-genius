import Proofs.Erdos85MuThreeKSymmetryTaggedExhaustive
import Proofs.Erdos85OrderSixtyFourMuThreeMixedGridAssembly

/-! # Family-tagged `K`-symmetry classifications -/

namespace Erdos85

noncomputable section

def muThreeKSymmetryClassification_H16_tagged
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H16Row x.val)
    (himpossible : ∀
      (slot : {slot : Mu3KCandidateSlot //
        slot.MatchesInternalRows mu3H16Row})
      (dK : DecidableRel (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot.1))
      (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot.1)))
      [dC : DecidableRel C.Adj],
      ¬ @MuThreeMixedGridCode X Y _ _ _ _ H
        (muThreeKCandidateRel (mu3SlotCandidate row column) slot.1)
        _ dK C dC) :
    MuThreeKSymmetryClassification H where
  Index := {slot : Mu3KCandidateSlot //
    slot.MatchesInternalRows mu3H16Row}
  candidate := fun slot => mu3SlotCandidate row column slot.1
  exhaustive := by
    intro K dK data
    obtain ⟨slot, htag, hK⟩ := exists_mu3SlotCandidate_H16_tagged
      row column H K data.H_twoRegular data.K_twoRegular
      data.cycle_compatible hHcoord data.row_symmetry data.column_symmetry
    exact ⟨⟨slot, htag⟩, hK⟩
  impossible := himpossible

def muThreeKSymmetryClassification_H88_tagged
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H88Row x.val)
    (himpossible : ∀
      (slot : {slot : Mu3KCandidateSlot //
        slot.MatchesInternalRows mu3H88Row})
      (dK : DecidableRel (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot.1))
      (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot.1)))
      [dC : DecidableRel C.Adj],
      ¬ @MuThreeMixedGridCode X Y _ _ _ _ H
        (muThreeKCandidateRel (mu3SlotCandidate row column) slot.1)
        _ dK C dC) :
    MuThreeKSymmetryClassification H where
  Index := {slot : Mu3KCandidateSlot //
    slot.MatchesInternalRows mu3H88Row}
  candidate := fun slot => mu3SlotCandidate row column slot.1
  exhaustive := by
    intro K dK data
    obtain ⟨slot, htag, hK⟩ := exists_mu3SlotCandidate_H88_tagged
      row column H K data.H_twoRegular data.K_twoRegular
      data.cycle_compatible hHcoord data.row_symmetry data.column_symmetry
    exact ⟨⟨slot, htag⟩, hK⟩
  impossible := himpossible

def muThreeKSymmetryClassification_H106_tagged
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H106Row x.val)
    (himpossible : ∀
      (slot : {slot : Mu3KCandidateSlot //
        slot.MatchesInternalRows mu3H106Row})
      (dK : DecidableRel (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot.1))
      (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot.1)))
      [dC : DecidableRel C.Adj],
      ¬ @MuThreeMixedGridCode X Y _ _ _ _ H
        (muThreeKCandidateRel (mu3SlotCandidate row column) slot.1)
        _ dK C dC) :
    MuThreeKSymmetryClassification H where
  Index := {slot : Mu3KCandidateSlot //
    slot.MatchesInternalRows mu3H106Row}
  candidate := fun slot => mu3SlotCandidate row column slot.1
  exhaustive := by
    intro K dK data
    obtain ⟨slot, htag, hK⟩ := exists_mu3SlotCandidate_H106_tagged
      row column H K data.H_twoRegular data.K_twoRegular
      data.cycle_compatible hHcoord data.row_symmetry data.column_symmetry
    exact ⟨⟨slot, htag⟩, hK⟩
  impossible := himpossible

end

end Erdos85

#print axioms Erdos85.muThreeKSymmetryClassification_H16_tagged
#print axioms Erdos85.muThreeKSymmetryClassification_H88_tagged
#print axioms Erdos85.muThreeKSymmetryClassification_H106_tagged

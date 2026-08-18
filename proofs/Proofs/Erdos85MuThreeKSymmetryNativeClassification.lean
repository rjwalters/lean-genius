import Proofs.Erdos85MuThreeFixedKInternalManifest
import Proofs.Erdos85MuThreeKSymmetryTaggedClassification
import Proofs.Erdos85MuThreeMixedGridCodeNativeAdapter
import Proofs.Erdos85OrderSixtyFourMuThreeInternalShapeCoordinates
import Proofs.Erdos85OrderSixtyFourMuThreeJointEigenlineCapstone

/-!
# Native certificate consumers for the tagged K-symmetry classifications

The structural enumeration produces a slot tagged by its internal two-factor.
This module normalizes an abstract mixed-grid code and dispatches every such
slot, including the three all-triangle-free slots, to the uniform `Fin 22`
native certificate family.
-/

namespace Erdos85

noncomputable section

/-- A mixed-grid code whose normalized internal relation has the family tag
of `slot` contradicts the native certificate indexed by that slot. -/
theorem false_of_muThreeMixedGridCode_taggedSlot
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (rows : Nat → Mu3KRow)
    (slot : {slot : Mu3KCandidateSlot //
      slot.MatchesInternalRows rows})
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ rows x.val)
    (dK : DecidableRel (muThreeKCandidateRel
      (mu3SlotCandidate row column) slot.1))
    (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel
      (mu3SlotCandidate row column) slot.1)))
    [dC : DecidableRel C.Adj]
    (code : @MuThreeMixedGridCode X Y _ _ _ _ H
      (muThreeKCandidateRel (mu3SlotCandidate row column) slot.1)
      _ dK C dC) : False := by
  let K := muThreeKCandidateRel (mu3SlotCandidate row column) slot.1
  let Cn := C.comap (muThreeNormalizeCellEquiv row column K)
  let normalized := code.normalize row column H K C
  apply false_of_muThreeMixedGridCode_fixedK
    slot.1.certificateGridIndex
    (mu3NormalizeRelation row column H)
    (mu3NormalizeRelation row column K)
    Cn normalized
  · intro x y
    simpa [K, mu3NormalizeRelation, muThreeKCandidateRel, mu3Fin8CellCode,
      mu3SlotCandidate] using
        slot.1.not_candidate_iff_fixed_grid_mem x y
  · intro x y
    exact (hHcoord x y).trans
      ((slot.2 x y).symm.trans (slot.1.internal_iff_fixed_grid x y))

/-- The H16 structural classification with all impossible branches discharged
by the native `Fin 22` certificates. -/
def muThreeKSymmetryClassification_H16_native
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H16Row x.val) :
    MuThreeKSymmetryClassification H :=
  muThreeKSymmetryClassification_H16_tagged row column H hHcoord
    (fun slot _ _ _ code =>
      false_of_muThreeMixedGridCode_taggedSlot
        row column H mu3H16Row slot hHcoord _ _ code)

/-- H88 version of `muThreeKSymmetryClassification_H16_native`. -/
def muThreeKSymmetryClassification_H88_native
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H88Row x.val) :
    MuThreeKSymmetryClassification H :=
  muThreeKSymmetryClassification_H88_tagged row column H hHcoord
    (fun slot _ _ _ code =>
      false_of_muThreeMixedGridCode_taggedSlot
        row column H mu3H88Row slot hHcoord _ _ code)

/-- H106 version of `muThreeKSymmetryClassification_H16_native`. -/
def muThreeKSymmetryClassification_H106_native
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H106Row x.val) :
    MuThreeKSymmetryClassification H :=
  muThreeKSymmetryClassification_H106_tagged row column H hHcoord
    (fun slot _ _ _ code =>
      false_of_muThreeMixedGridCode_taggedSlot
        row column H mu3H106Row slot hHcoord _ _ code)

/-- Precise structural socket left above the native certificate layer: it is
enough to put the internal two-factor into one of the three surviving row
normal forms.  The conclusion is exactly the classification consumed by the
graph-facing joint-eigenline capstone. -/
theorem nonempty_muThreeKSymmetryClassification_native_of_shape
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H : X → Y → Prop) [DecidableRel H]
    (hshape :
      (∃ (row : X ≃ Fin 8) (column : Y ≃ Fin 8),
        ∀ x y, mu3NormalizeRelation row column H x y ↔
          y.val ∈ mu3H16Row x.val) ∨
      (∃ (row : X ≃ Fin 8) (column : Y ≃ Fin 8),
        ∀ x y, mu3NormalizeRelation row column H x y ↔
          y.val ∈ mu3H88Row x.val) ∨
      (∃ (row : X ≃ Fin 8) (column : Y ≃ Fin 8),
        ∀ x y, mu3NormalizeRelation row column H x y ↔
          y.val ∈ mu3H106Row x.val)) :
    Nonempty (MuThreeKSymmetryClassification.{_, _, 0} H) := by
  rcases hshape with h16 | h88 | h106
  · obtain ⟨row, column, hcoord⟩ := h16
    exact ⟨muThreeKSymmetryClassification_H16_native
      row column H hcoord⟩
  · obtain ⟨row, column, hcoord⟩ := h88
    exact ⟨muThreeKSymmetryClassification_H88_native
      row column H hcoord⟩
  · obtain ⟨row, column, hcoord⟩ := h106
    exact ⟨muThreeKSymmetryClassification_H106_native
      row column H hcoord⟩

/-- Direct graph-facing closure of the alternating `μ = 3` size-two lane.
The internal shape coordinates come from the existing order-sixteen
two-factor census; every resulting K slot is then discharged by its uniform
native `Fin 22` certificate. -/
theorem false_of_orderSixtyFour_mu3_jointEigenline_native
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2) : False := by
  have hshape :=
    orderSixtyFour_muThreeInternalRel_exists_nativeShapeCoordinates
      G hfree hreg hcardV c hc s hs_in hs_out hA_in
  let classification : MuThreeKSymmetryClassification.{_, _, 0}
      (orderSixtyFourMuThreeInternalRel G
        (cSupp := c.supp) (s := s)) := Classical.choice
    (nonempty_muThreeKSymmetryClassification_native_of_shape
      (orderSixtyFourMuThreeInternalRel G
        (cSupp := c.supp) (s := s)) hshape)
  exact false_of_orderSixtyFour_mu3_jointEigenline
    G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
    classification

end

end Erdos85

#print axioms Erdos85.false_of_muThreeMixedGridCode_taggedSlot
#print axioms Erdos85.muThreeKSymmetryClassification_H16_native
#print axioms Erdos85.muThreeKSymmetryClassification_H88_native
#print axioms Erdos85.muThreeKSymmetryClassification_H106_native
#print axioms Erdos85.nonempty_muThreeKSymmetryClassification_native_of_shape
#print axioms Erdos85.false_of_orderSixtyFour_mu3_jointEigenline_native

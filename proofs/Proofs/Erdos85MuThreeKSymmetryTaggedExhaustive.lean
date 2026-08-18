import Proofs.Erdos85MuThreeKSymmetryCandidateSlots

/-!
# Family-tagged exhaustive `K` candidates

The original shape providers erase which internal row table produced their
candidate.  This module retains exactly the finite-coordinate equality needed
to use a family-specific subtype as the classification index.
-/

namespace Erdos85

/-- A slot belongs to the family represented by `rows`, on the `Fin 8`
coordinate domain relevant to the mixed-grid model. -/
def Mu3KCandidateSlot.MatchesInternalRows
    (slot : Mu3KCandidateSlot) (rows : Nat → Mu3KRow) : Prop :=
  ∀ x y : Fin 8,
    y.val ∈ slot.sector.HRows x.val ↔ y.val ∈ rows x.val

theorem exists_mu3SlotCandidate_of_selection_tagged
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (rows : Nat → Mu3KRow)
    (hHtwo : RelationTwoRegular H) (hKtwo : RelationTwoRegular K)
    (hrowSymm : ∀ x x',
      Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
        Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (hcolumnSymm : ∀ y y',
      Fintype.card {x : X // H x y' ∧ ¬ K x y} =
        Fintype.card {x : X // H x y ∧ ¬ K x y'})
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ rows x.val)
    (selection : Mu3KSectorSelection row column H K) :
    ∃ slot : Mu3KCandidateSlot,
      slot.MatchesInternalRows rows ∧
      ∀ x y, K x y ↔ mu3SlotCandidate row column slot x y = true := by
  let Kn := mu3NormalizeRelation row column K
  have hsectorEquation : ∀ x : Fin 8,
      ((Finset.univ.filter fun y => Kn x y).image Fin.val) ∩
          selection.sector.HRows x.val = selection.sector.TRows x.val := by
    intro x
    exact mu3SectorEquation_of_choice_edge_iff selection.sector Kn
      selection.edge_iff x
  obtain ⟨candidateRows, hi⟩ := exists_mu3KSectorCandidate_of_coordinates
    row column H K selection.sector.HRows selection.sector.TRows
    hHtwo hKtwo selection.H_coordinate hsectorEquation hrowSymm hcolumnSymm
  let i : Mu3AllSectorCandidateIndex := ⟨selection.sector, candidateRows⟩
  obtain ⟨slot, hsector, hrows⟩ :=
    exists_mu3KCandidateSlot_of_allSectorIndex i
  refine ⟨slot, ?_, ?_⟩
  · intro x y
    rw [hsector]
    exact (selection.H_coordinate x y).symm.trans (hHcoord x y)
  · intro x y
    rw [hi x y]
    simp only [mu3SlotCandidate, mu3PullbackCandidate]
    rw [hrows]

theorem exists_mu3SlotCandidate_H16_tagged
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hHtwo : RelationTwoRegular H) (hKtwo : RelationTwoRegular K)
    (hcycle : RelationFactorCycleCompatible H K)
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H16Row x.val)
    (hrowSymm : ∀ x x',
      Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
        Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (hcolumnSymm : ∀ y y',
      Fintype.card {x : X // H x y' ∧ ¬ K x y} =
        Fintype.card {x : X // H x y ∧ ¬ K x y'}) :
    ∃ slot : Mu3KCandidateSlot,
      slot.MatchesInternalRows mu3H16Row ∧
      ∀ x y, K x y ↔ mu3SlotCandidate row column slot x y = true := by
  obtain ⟨selection⟩ := exists_mu3KSectorSelection_H16_of_coordinates
    row column H K hcycle hHcoord
  exact exists_mu3SlotCandidate_of_selection_tagged row column H K
    mu3H16Row hHtwo hKtwo hrowSymm hcolumnSymm hHcoord selection

theorem exists_mu3SlotCandidate_H88_tagged
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hHtwo : RelationTwoRegular H) (hKtwo : RelationTwoRegular K)
    (hcycle : RelationFactorCycleCompatible H K)
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H88Row x.val)
    (hrowSymm : ∀ x x',
      Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
        Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (hcolumnSymm : ∀ y y',
      Fintype.card {x : X // H x y' ∧ ¬ K x y} =
        Fintype.card {x : X // H x y ∧ ¬ K x y'}) :
    ∃ slot : Mu3KCandidateSlot,
      slot.MatchesInternalRows mu3H88Row ∧
      ∀ x y, K x y ↔ mu3SlotCandidate row column slot x y = true := by
  obtain ⟨selection⟩ := exists_mu3KSectorSelection_H88_of_coordinates
    row column H K hcycle hHcoord
  exact exists_mu3SlotCandidate_of_selection_tagged row column H K
    mu3H88Row hHtwo hKtwo hrowSymm hcolumnSymm hHcoord selection

theorem exists_mu3SlotCandidate_H106_tagged
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hHtwo : RelationTwoRegular H) (hKtwo : RelationTwoRegular K)
    (hcycle : RelationFactorCycleCompatible H K)
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H106Row x.val)
    (hrowSymm : ∀ x x',
      Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
        Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (hcolumnSymm : ∀ y y',
      Fintype.card {x : X // H x y' ∧ ¬ K x y} =
        Fintype.card {x : X // H x y ∧ ¬ K x y'}) :
    ∃ slot : Mu3KCandidateSlot,
      slot.MatchesInternalRows mu3H106Row ∧
      ∀ x y, K x y ↔ mu3SlotCandidate row column slot x y = true := by
  obtain ⟨selection⟩ := exists_mu3KSectorSelection_H106_of_coordinates
    row column H K hcycle hHcoord
  exact exists_mu3SlotCandidate_of_selection_tagged row column H K
    mu3H106Row hHtwo hKtwo hrowSymm hcolumnSymm hHcoord selection

end Erdos85

#print axioms Erdos85.exists_mu3SlotCandidate_H16_tagged
#print axioms Erdos85.exists_mu3SlotCandidate_H88_tagged
#print axioms Erdos85.exists_mu3SlotCandidate_H106_tagged

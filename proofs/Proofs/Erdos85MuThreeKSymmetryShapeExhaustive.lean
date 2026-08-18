import Proofs.Erdos85MuThreeKSymmetryCycleSector

/-! # Shape-level exhaustive K-symmetry providers -/

namespace Erdos85

theorem exists_mu3AllSectorCandidate_of_selection_nonempty
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hHtwo : RelationTwoRegular H) (hKtwo : RelationTwoRegular K)
    (hrowSymm : ∀ x x',
      Fintype.card {y : Y // H x' y ∧ ¬ K x y} =
        Fintype.card {y : Y // H x y ∧ ¬ K x' y})
    (hcolumnSymm : ∀ y y',
      Fintype.card {x : X // H x y' ∧ ¬ K x y} =
        Fintype.card {x : X // H x y ∧ ¬ K x y'})
    (hselection : Nonempty (Mu3KSectorSelection row column H K)) :
    ∃ i : Mu3AllSectorCandidateIndex,
      ∀ x y, K x y ↔ mu3AllSectorCandidate row column i x y = true := by
  obtain ⟨selection⟩ := hselection
  exact exists_mu3AllSectorCandidate_of_selection row column H K
    hHtwo hKtwo hrowSymm hcolumnSymm selection

theorem exists_mu3AllSectorCandidate_H16
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
    ∃ i : Mu3AllSectorCandidateIndex,
      ∀ x y, K x y ↔ mu3AllSectorCandidate row column i x y = true := by
  apply exists_mu3AllSectorCandidate_of_selection_nonempty
    row column H K hHtwo hKtwo hrowSymm hcolumnSymm
  exact exists_mu3KSectorSelection_H16_of_coordinates
    row column H K hcycle hHcoord

theorem exists_mu3AllSectorCandidate_H88
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
    ∃ i : Mu3AllSectorCandidateIndex,
      ∀ x y, K x y ↔ mu3AllSectorCandidate row column i x y = true := by
  apply exists_mu3AllSectorCandidate_of_selection_nonempty
    row column H K hHtwo hKtwo hrowSymm hcolumnSymm
  exact exists_mu3KSectorSelection_H88_of_coordinates
    row column H K hcycle hHcoord

theorem exists_mu3AllSectorCandidate_H106
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
    ∃ i : Mu3AllSectorCandidateIndex,
      ∀ x y, K x y ↔ mu3AllSectorCandidate row column i x y = true := by
  apply exists_mu3AllSectorCandidate_of_selection_nonempty
    row column H K hHtwo hKtwo hrowSymm hcolumnSymm
  exact exists_mu3KSectorSelection_H106_of_coordinates
    row column H K hcycle hHcoord

end Erdos85

#print axioms Erdos85.exists_mu3AllSectorCandidate_H16
#print axioms Erdos85.exists_mu3AllSectorCandidate_H88
#print axioms Erdos85.exists_mu3AllSectorCandidate_H106

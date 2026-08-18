import Proofs.Erdos85MuThreeKSymmetryCoordinateTransport
import Proofs.Erdos85MuThreeKSymmetrySectorTables

/-! # Exhaustive half of the mu-three K-symmetry classification -/

namespace Erdos85

abbrev Mu3AllSectorCandidateIndex :=
  Σ sector : Mu3KSectorChoice,
    {rows : Mu3KRows //
      rows ∈ mu3KSectorEnumeration sector.HRows sector.TRows}

def mu3AllSectorCandidate
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (i : Mu3AllSectorCandidateIndex) (x : X) (y : Y) : Bool :=
  mu3KRowsCandidate i.2.1 (row x) (column y)

/-- Exact shape-facing input still required from cycle compatibility.  It
chooses one of the ten explicit sectors, identifies the normalized ambient
factor, and states whether each ambient edge belongs to K. -/
structure Mu3KSectorSelection
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) where
  sector : Mu3KSectorChoice
  H_coordinate : ∀ x y,
    mu3NormalizeRelation row column H x y ↔
      y.val ∈ sector.HRows x.val
  edge_iff : ∀ x y, y.val ∈ sector.HRows x.val →
    (mu3NormalizeRelation row column K x y ↔
      y.val ∈ sector.TRows x.val)

theorem exists_mu3AllSectorCandidate_of_selection
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
    (selection : Mu3KSectorSelection row column H K) :
    ∃ i : Mu3AllSectorCandidateIndex,
      ∀ x y, K x y ↔ mu3AllSectorCandidate row column i x y = true := by
  let Kn := mu3NormalizeRelation row column K
  have hsector : ∀ x : Fin 8,
      ((Finset.univ.filter fun y => Kn x y).image Fin.val) ∩
          selection.sector.HRows x.val =
        selection.sector.TRows x.val := by
    intro x
    exact mu3SectorEquation_of_choice_edge_iff selection.sector Kn
      selection.edge_iff x
  obtain ⟨i, hi⟩ := exists_mu3KSectorCandidate_of_coordinates
    row column H K selection.sector.HRows selection.sector.TRows
    hHtwo hKtwo selection.H_coordinate hsector hrowSymm hcolumnSymm
  exact ⟨⟨selection.sector, i⟩, by
    intro x y
    simpa [mu3AllSectorCandidate, mu3PullbackCandidate] using hi x y⟩

end Erdos85

#print axioms Erdos85.exists_mu3AllSectorCandidate_of_selection

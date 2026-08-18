import Proofs.Erdos85MuThreeAllTfShapeCoordinates
import Proofs.Erdos85MuThreeAllTfExteriorHitTransport
import Proofs.Erdos85MuThreeMixedGridSquareDegrees

/-!
# Abstract mixed-grid adapter for the three all-TF certificates

This is the all-TF analogue of the fixed-K native adapter.  It starts by
identifying the native certificate's ordered occupied cells with the abstract
occupied-cell subtype carried by a `MuThreeMixedGridCode`.
-/

namespace Erdos85

open SimpleGraph

def mu3Fin8PairCode (p : Fin 8 × Fin 8) : Nat :=
  p.1.val * 8 + p.2.val

theorem mu3Fin8PairCode_injective : Function.Injective mu3Fin8PairCode := by
  intro p q h
  apply Prod.ext
  · apply Fin.ext
    have hp := p.2.isLt
    have hq := q.2.isLt
    simp only [mu3Fin8PairCode] at h
    omega
  · apply Fin.ext
    have hp := p.2.isLt
    have hq := q.2.isLt
    simp only [mu3Fin8PairCode] at h
    omega

theorem mu3AllTf_not_internal_iff_cell_mem
    (shape : Mu3AllTfShape) (x y : Fin 8) :
    ¬ mu3AllTfInternal shape x.val y.val = true ↔
      mu3Fin8PairCode (x, y) ∈ mu3AllTfCells shape := by
  cases shape <;> fin_cases x <;> fin_cases y <;> decide

/-- Coordinate map from an abstract occupied cell to the native cell number. -/
def mu3AllTfCodeCellCoordinate
    (shape : Mu3AllTfShape) (H : Fin 8 → Fin 8 → Prop)
    [DecidableRel H]
    (hinternal : ∀ x y,
      H x y ↔ mu3AllTfInternal shape x.val y.val = true) :
    muThreeMixedCell H → {cell : Nat // cell ∈ mu3AllTfCells shape} :=
  fun p => ⟨mu3Fin8PairCode p.1,
    (mu3AllTf_not_internal_iff_cell_mem shape p.1.1 p.1.2).mp
      (fun hi => p.2 ((hinternal _ _).mpr hi))⟩

theorem mu3AllTfCodeCellCoordinate_injective
    (shape : Mu3AllTfShape) (H : Fin 8 → Fin 8 → Prop)
    [DecidableRel H]
    (hinternal : ∀ x y,
      H x y ↔ mu3AllTfInternal shape x.val y.val = true) :
    Function.Injective (mu3AllTfCodeCellCoordinate shape H hinternal) := by
  intro p q h
  apply Subtype.ext
  exact mu3Fin8PairCode_injective (congrArg Subtype.val h)

/-- The native occupied-cell order enumerates the vertices of an abstract
all-TF mixed-grid code. -/
noncomputable def mu3AllTfCodeCellEquiv
    (shape : Mu3AllTfShape) (H : Fin 8 → Fin 8 → Prop)
    [DecidableRel H]
    (C : SimpleGraph (muThreeMixedCell H)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H H C)
    (hinternal : ∀ x y,
      H x y ↔ mu3AllTfInternal shape x.val y.val = true) :
    Fin 48 ≃ muThreeMixedCell H :=
  mu3ExteriorEquivOfCoordinateInjection shape
    (code.card_mixedCell_eq_fortyEight H H C)
    (mu3AllTfCodeCellCoordinate shape H hinternal)
    (mu3AllTfCodeCellCoordinate_injective shape H hinternal)

theorem mu3AllTfCodeCellEquiv_coordinate
    (shape : Mu3AllTfShape) (H : Fin 8 → Fin 8 → Prop)
    [DecidableRel H]
    (C : SimpleGraph (muThreeMixedCell H)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H H C)
    (hinternal : ∀ x y,
      H x y ↔ mu3AllTfInternal shape x.val y.val = true)
    (i : Fin 48) :
    mu3AllTfCodeCellCoordinate shape H hinternal
        (mu3AllTfCodeCellEquiv shape H C code hinternal i) =
      mu3AllTfShapeCellEquiv shape i := by
  exact mu3ExteriorEquivOfCoordinateBijection_coord shape
    (mu3AllTfCodeCellCoordinate shape H hinternal)
    (mu3CoordinateBijection_of_injective shape
      (code.card_mixedCell_eq_fortyEight H H C)
      (mu3AllTfCodeCellCoordinate shape H hinternal)
      (mu3AllTfCodeCellCoordinate_injective shape H hinternal)) i

theorem mu3AllTfCodeCellEquiv_code
    (shape : Mu3AllTfShape) (H : Fin 8 → Fin 8 → Prop)
    [DecidableRel H]
    (C : SimpleGraph (muThreeMixedCell H)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H H C)
    (hinternal : ∀ x y,
      H x y ↔ mu3AllTfInternal shape x.val y.val = true)
    (i : Fin 48) :
    mu3Fin8PairCode
        ((mu3AllTfCodeCellEquiv shape H C code hinternal i).1) =
      (mu3AllTfCells shape).getD i.val 0 := by
  have h := congrArg Subtype.val
    (mu3AllTfCodeCellEquiv_coordinate shape H C code hinternal i)
  rw [mu3AllTfShapeCellEquiv_val] at h
  exact h

end Erdos85

#print axioms Erdos85.mu3AllTf_not_internal_iff_cell_mem
#print axioms Erdos85.mu3AllTfCodeCellEquiv_coordinate
#print axioms Erdos85.mu3AllTfCodeCellEquiv_code

import Proofs.Erdos85MuThreeAllTfActualShape
import Proofs.Erdos85MuThreeAllTfGraphHitTransport
import Mathlib.Data.List.NodupEquivFin

/-! # Canonical occupied-cell coordinates for the three all-TF shapes -/

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
theorem mu3AllTfCells_nodup (shape : Mu3AllTfShape) :
    (mu3AllTfCells shape).Nodup := by
  cases shape <;> native_decide

/-- The list order used by the native certificate is a genuine enumeration
of the 48 occupied cells. -/
def mu3AllTfShapeCellEquiv (shape : Mu3AllTfShape) :
    Fin 48 ≃ {cell : Nat // cell ∈ mu3AllTfCells shape} :=
  (Equiv.cast (congrArg Fin (mu3AllTfCells_length shape).symm)).trans
    ((mu3AllTfCells_nodup shape).getEquiv (mu3AllTfCells shape))

/-- Any bijective exterior coordinate map onto the occupied cells canonically
produces the `Fin 48` enumeration required by the certificate adapter. -/
def mu3ExteriorEquivOfCoordinateBijection
    (shape : Mu3AllTfShape) {W : Type*}
    (coord : W → {cell : Nat // cell ∈ mu3AllTfCells shape})
    (hcoord : Function.Bijective coord) : Fin 48 ≃ W :=
  (mu3AllTfShapeCellEquiv shape).trans (Equiv.ofBijective coord hcoord).symm

theorem mu3ExteriorEquivOfCoordinateBijection_coord
    (shape : Mu3AllTfShape) {W : Type*}
    (coord : W → {cell : Nat // cell ∈ mu3AllTfCells shape})
    (hcoord : Function.Bijective coord) (i : Fin 48) :
    coord (mu3ExteriorEquivOfCoordinateBijection shape coord hcoord i) =
      mu3AllTfShapeCellEquiv shape i := by
  exact (Equiv.ofBijective coord hcoord).apply_symm_apply
    (mu3AllTfShapeCellEquiv shape i)

end

end Erdos85

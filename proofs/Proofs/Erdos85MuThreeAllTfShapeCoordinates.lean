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

theorem mu3CoordinateBijection_of_injective
    (shape : Mu3AllTfShape) {W : Type*} [Fintype W]
    (hcard : Fintype.card W = 48)
    (coord : W → {cell : Nat // cell ∈ mu3AllTfCells shape})
    (hinj : Function.Injective coord) : Function.Bijective coord := by
  apply (Fintype.bijective_iff_injective_and_card coord).2
  refine ⟨hinj, hcard.trans ?_⟩
  exact Fintype.card_congr (mu3AllTfShapeCellEquiv shape)

/-- At order 64, no separate surjectivity proof is needed: an injective map
from the 48 exterior vertices into the 48 occupied cells is automatically the
coordinate bijection used to enumerate the exterior. -/
def mu3ExteriorEquivOfCoordinateInjection
    (shape : Mu3AllTfShape) {W : Type*} [Fintype W]
    (hcard : Fintype.card W = 48)
    (coord : W → {cell : Nat // cell ∈ mu3AllTfCells shape})
    (hinj : Function.Injective coord) : Fin 48 ≃ W :=
  mu3ExteriorEquivOfCoordinateBijection shape coord
    (mu3CoordinateBijection_of_injective shape hcard coord hinj)

end

end Erdos85

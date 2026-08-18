import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! # A non-bipartite countermodel to the bare size-two block package

The commuting regular-block data available for a normalized size-two defect
component do not force that component bipartite.  This finite model records
the precise boundary: further arguments must use ambient selector,
owner-Gram, or C4-free structure.
-/

open SimpleGraph

namespace Erdos85

/-- The internal two-factor in the countermodel. -/
def sizeTwoBareCountermodelH : SimpleGraph (Fin 16) := cycleGraph 16

/-- A 7-regular non-bipartite circulant containing that two-factor. -/
def sizeTwoBareCountermodelD : SimpleGraph (Fin 16) :=
  circulantGraph ({1, 3, 4, 8} : Set (Fin 16))

noncomputable instance : DecidableRel sizeTwoBareCountermodelH.Adj := by
  dsimp [sizeTwoBareCountermodelH]
  infer_instance

noncomputable instance : DecidableRel sizeTwoBareCountermodelD.Adj := by
  dsimp [sizeTwoBareCountermodelD]
  infer_instance

theorem sizeTwoBareCountermodelH_degree :
    ∀ x, sizeTwoBareCountermodelH.degree x = 2 := by
  decide

theorem sizeTwoBareCountermodelD_degree :
    ∀ x, sizeTwoBareCountermodelD.degree x = 7 := by
  decide

theorem sizeTwoBareCountermodelH_le_D :
    sizeTwoBareCountermodelH ≤ sizeTwoBareCountermodelD := by
  intro x y hxy
  revert x y
  decide

theorem sizeTwoBareCountermodel_commute :
    sizeTwoBareCountermodelH.adjMatrix ℤ *
        sizeTwoBareCountermodelD.adjMatrix ℤ =
      sizeTwoBareCountermodelD.adjMatrix ℤ *
        sizeTwoBareCountermodelH.adjMatrix ℤ := by
  decide

theorem sizeTwoBareCountermodel_triangle :
    sizeTwoBareCountermodelD.Adj 0 1 ∧
      sizeTwoBareCountermodelD.Adj 1 4 ∧
      sizeTwoBareCountermodelD.Adj 0 4 := by
  decide

/-- The countermodel also satisfies the ambient cycle constraint that
distance-two vertices of the internal factor are not defect-adjacent. -/
theorem sizeTwoBareCountermodel_distanceTwo_not_adj :
    ∀ x : Fin 16, ¬ sizeTwoBareCountermodelD.Adj x (x + 2) := by
  decide

theorem sizeTwoBareCountermodel_not_bipartite :
    ¬ sizeTwoBareCountermodelD.IsBipartite := by
  rintro ⟨C⟩
  have htri := sizeTwoBareCountermodel_triangle
  have h01 := C.valid htri.1
  have h14 := C.valid htri.2.1
  have h04 := C.valid htri.2.2
  let f : Fin 3 → Fin 2 := fun i =>
    if i = 0 then C 0 else if i = 1 then C 1 else C 4
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hcard := Fintype.card_le_of_injective f hinj
  omega

end Erdos85

#print axioms Erdos85.sizeTwoBareCountermodelH_degree
#print axioms Erdos85.sizeTwoBareCountermodelD_degree
#print axioms Erdos85.sizeTwoBareCountermodelH_le_D
#print axioms Erdos85.sizeTwoBareCountermodel_commute
#print axioms Erdos85.sizeTwoBareCountermodel_distanceTwo_not_adj
#print axioms Erdos85.sizeTwoBareCountermodel_not_bipartite

import Proofs.Erdos85CubicValueFiveMarkedGraph
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # The global value-five graph on the twenty-four cross edges

This file instantiates the generic marked-relation machinery on the canonical
h305 cross-edge population `shoreTypeEdgeFinset R U 1`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The global graph whose vertices are cross-shore exterior edges and whose
edges record cubic residual walk count five. -/
def h305CrossCubicValueFiveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (U : Finset V) : SimpleGraph (shoreTypeEdgeFinset R U 1) :=
  symmetricMarkedGraph
    (fun a b ↦ residualFiberCubicWalkCount R Cedge a.1 b.1 = 5)
    (by
      intro a b hab
      rwa [residualFiberCubicWalkCount_comm R Cedge] at hab)

/-- Once every cross target has its two sharp value-five partners inside the
cross population, the canonical global marked graph is a union of cycles and
has exactly twenty-four undirected marked pairs. -/
theorem h305_crossCubicValueFive_globalGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hRreg : ∀ x, R.degree x = 6)
    (hsharp : let U := (Finset.univ : Finset (ZMod 8)).image u
      let S := shoreTypeEdgeFinset R U 1
      ∀ a ∈ S,
        (S.filter (fun b : R.edgeFinset ↦ a ≠ b ∧
          residualFiberCubicWalkCount R Cedge a b = 5)).card = 2) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    let S := shoreTypeEdgeFinset R U 1
    (h305CrossCubicValueFiveGraph R Cedge U).IsCycles ∧
      (symmetricMarkedEdgeFinset
        (fun a b : S ↦
          residualFiberCubicWalkCount R Cedge a.1 b.1 = 5)
        (by
          intro a b hab
          rwa [residualFiberCubicWalkCount_comm R Cedge] at hab)).card = 24 := by
  classical
  dsimp only at hsharp ⊢
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let S := shoreTypeEdgeFinset R U 1
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover humode hvmode hRreg
  have hScard : S.card = 24 := by
    simpa [S, U] using hpop.2.1
  constructor
  · exact cubicValueFive_markedGraph_isCycles R Cedge S hsharp
  · exact cubicValueFive_markedPairs_card_twentyFour
      R Cedge S hScard hsharp

end

end Erdos85

#print axioms Erdos85.h305_crossCubicValueFive_globalGraph

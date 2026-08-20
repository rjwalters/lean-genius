import Proofs.Erdos85CrossCubicMassUpperProjections
import Proofs.Erdos85CrossEdgeCoordinateRepresentation
import Proofs.Erdos85CrossCubicValueFiveLocalDegree
import Proofs.Erdos85CrossCubicValueFiveGlobalGraph

/-! # Uniform sharp cross-row bounds produce the global marked cycle graph -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If every one of the twenty-four cross-shore targets attains the sharp
cubic residual upper bound, their value-five relation is a two-regular graph
with twenty-four undirected marked pairs. -/
theorem h305_cross_mass_le_550_global_valueFiveGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hzeroUV : ∀ k l,
      Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (hupper : let U := (Finset.univ : Finset (ZMod 8)).image u
      let S := shoreTypeEdgeFinset R U 1
      ∀ a ∈ S, (∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 550) :
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
  dsimp only at hupper ⊢
  refine h305_crossCubicValueFive_globalGraph
    R Cedge u v huinj hvinj hdisj hcover hmodeu hmodev hRreg ?_
  show ∀ a ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1,
    ((shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1).filter
        (fun b : R.edgeFinset ↦ a ≠ b ∧
          residualFiberCubicWalkCount R Cedge a b = 5)).card = 2
  intro a ha
  obtain ⟨i, j, haij⟩ :=
    shoreTypeOneEdge_exists_crossCoordinates R u v hcover a ha
  obtain ⟨hcard, hsub⟩ :=
    h305_cross_mass_le_550_valueFiveEdge_card_two_and_subset
      H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
        hdisj hcover hmodeu hmodev hzeroUV hzeroVU a i j haij
          (hupper a ha)
  exact crossTarget_markedNeighbor_card_two_of_localMatching
    R Cedge _ a hcard hsub

end


end Erdos85

#print axioms Erdos85.h305_cross_mass_le_550_global_valueFiveGraph

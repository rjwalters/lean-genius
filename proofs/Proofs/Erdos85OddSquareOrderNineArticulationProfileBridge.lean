import Proofs.Erdos85OddSquareOrderNineArticulationGraphBridge
import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileBinZeroDefectTypes

/-! # Actual-profile inputs for the q = 9 articulation bridge

Node: B.3 / GAP B-CLASSIFY.  This file specializes the abstract deleted-owner
articulation machinery to the `(53,27,0,1,0)` three-high profile.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the second three-high profile, every defect neighbor of the unique
bin-three owner is a bin-zero vertex.  Consequently owner adjacency is
equivalent to membership in its five-element exceptional bin-zero set. -/
theorem squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    E.card = 5 ∧ D.neighborFinset owner = E ∧
      ∀ u : V, D.Adj u owner ↔ u ∈ E := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := D.neighborFinset owner ∩ B 0
  have hneighbors := squareOrderNine_threeHigh_secondProfile_binThree_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hneighbors
  have hdegree := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard howner
  dsimp only at hdegree
  have hEcard : E.card = 5 := by
    exact hneighbors.1
  have hneighborCard : (D.neighborFinset owner).card = 5 := by
    rw [D.card_neighborFinset_eq_degree, hdegree.1]
  have hneighborEq : D.neighborFinset owner = E := by
    apply Finset.eq_of_subset_of_card_le
    · exact fun u hu => by
        have hcardLe : (D.neighborFinset owner).card ≤ E.card := by
          rw [hneighborCard, hEcard]
        have hinterSubset : E ⊆ D.neighborFinset owner := Finset.inter_subset_left
        exact (Finset.eq_of_subset_of_card_le hinterSubset hcardLe).symm.subset hu
    · rw [hneighborCard, hEcard]
  refine ⟨hEcard, hneighborEq, ?_⟩
  intro u
  rw [D.adj_comm, ← D.mem_neighborFinset]
  exact Iff.of_eq (congrArg (fun s : Finset V => u ∈ s) hneighborEq)

end

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors

end Erdos85

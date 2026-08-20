import Proofs.Erdos85OddSquareOrderNineIncidenceQuotient

/-! # Symmetry of q = 9 incidence-quotient edge counts

Node: B.3 / GAP B-CLASSIFY.  The defect-edge mass between two incidence
bins is symmetric, coupling the per-bin quotient equations into one finite
integer system.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In any finite undirected graph, the number of directed incidences from a
vertex set `S` into `T` equals the number from `T` into `S`. -/
theorem sum_card_neighborFinset_inter_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) :
    (∑ x ∈ S, (G.neighborFinset x ∩ T).card) =
      ∑ y ∈ T, (G.neighborFinset y ∩ S).card := by
  classical
  have hrow (x : V) :
      (G.neighborFinset x ∩ T).card =
        ∑ y ∈ T, if G.Adj x y then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  have hcol (y : V) :
      (G.neighborFinset y ∩ S).card =
        ∑ x ∈ S, if G.Adj x y then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext x
    simp [SimpleGraph.mem_neighborFinset, G.adj_comm, and_comm]
  simp_rw [hrow, hcol]
  exact Finset.sum_comm

/-- Directed defect-edge mass from q=9 low incidence bin `i` into bin `j`. -/
def squareOrderNineDefectBinEdgeCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : ℕ) : ℕ :=
  let D := secondOrderDefectGraph G
  let Bi := squareOrderNineLowIncidenceBin G i
  let Bj := squareOrderNineLowIncidenceBin G j
  ∑ x ∈ Bi, (D.neighborFinset x ∩ Bj).card

/-- The q=9 defect quotient is symmetric across incidence levels. -/
theorem squareOrderNineDefectBinEdgeCount_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (i j : ℕ) :
    squareOrderNineDefectBinEdgeCount G i j =
      squareOrderNineDefectBinEdgeCount G j i := by
  dsimp only [squareOrderNineDefectBinEdgeCount]
  exact sum_card_neighborFinset_inter_comm
    (secondOrderDefectGraph G)
    (squareOrderNineLowIncidenceBin G i)
    (squareOrderNineLowIncidenceBin G j)

end


end Erdos85

#print axioms Erdos85.sum_card_neighborFinset_inter_comm
#print axioms Erdos85.squareOrderNineDefectBinEdgeCount_comm

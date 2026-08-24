import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85PureEndpointFinalLayerPrivateMatching

/-!
# Owner-label disjointness along second-order defect edges

Label a vertex by the chosen centers adjacent to it.  A second-order defect
edge has no common graph neighbor, so its endpoint labels are disjoint.  At
the pure endpoint every label has size at most two and the shore is exactly
the nonempty-label locus, turning the defect graph into a subgraph of the
corresponding subset-disjointness graph.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The centers of `C` which own `x`. -/
def exceptionalOwnerSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V) (x : V) : Finset V :=
  G.neighborFinset x ∩ C

/-- Owner labels are disjoint across every second-order defect edge. -/
theorem secondOrderDefect_adj_ownerSets_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (C : Finset V)
    {x y : V} (hxy : (secondOrderDefectGraph G).Adj x y) :
    Disjoint (exceptionalOwnerSet G C x) (exceptionalOwnerSet G C y) := by
  classical
  let D := secondOrderDefectGraph G
  have hxyNe : x ≠ y := D.ne_of_adj hxy
  have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 :=
    (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hxyNe).mp hxy
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hzCommon : z ∈ G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hzx).1, (Finset.mem_inter.mp hzy).1⟩
  have : 0 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
    Finset.card_pos.mpr ⟨z, hzCommon⟩
  omega

/-- At the pure endpoint, owner labels have size `0`, `1`, or `2`; they are
nonempty exactly on `S`, and defect edges join disjoint labels. -/
theorem c4Free_binarySquare_pureEndpoint_ownerLabel_disjointness_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    (∀ x, (exceptionalOwnerSet G (fullLineCenters G S q) x).card ≤ 2) ∧
    (∀ x, x ∈ S ↔
      (exceptionalOwnerSet G (fullLineCenters G S q) x).card = 1 ∨
      (exceptionalOwnerSet G (fullLineCenters G S q) x).card = 2) ∧
    ∀ {x y}, (secondOrderDefectGraph G).Adj x y →
      Disjoint (exceptionalOwnerSet G (fullLineCenters G S q) x)
        (exceptionalOwnerSet G (fullLineCenters G S q) y) := by
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simpa [exceptionalOwnerSet] using hprofile.2.2.2.2.1 x
  · intro x
    simpa [exceptionalOwnerSet] using hprofile.1 x
  · intro x y hxy
    exact secondOrderDefect_adj_ownerSets_disjoint
      G hfree (fullLineCenters G S q) hxy

end

end Erdos85

#print axioms Erdos85.secondOrderDefect_adj_ownerSets_disjoint
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_ownerLabel_disjointness_profile

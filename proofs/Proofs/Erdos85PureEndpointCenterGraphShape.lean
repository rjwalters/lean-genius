import Proofs.Erdos85PureEndpointInternalDegreeProfile

/-!
# Shape of the graph induced by pure endpoint centers

The companion-defect profile gives a compact graph-facing interface: the
graph induced by the full exceptional centers has maximum degree two.
Moreover, isolated centers lie off the shore and degree-two centers lie on
the shore.  Thus its components are restricted to the path/cycle regime,
with the shore locating both extreme degree classes.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the pure endpoint every full center has at most two neighbors among
the full centers.  Internal degree zero forces the center off the shore,
whereas internal degree two forces it onto the shore. -/
theorem c4Free_binarySquare_pureEndpoint_centerGraph_degree_shape
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
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∀ v ∈ fullLineCenters G S q,
      (G.neighborFinset v ∩ fullLineCenters G S q).card ≤ 2 ∧
      ((G.neighborFinset v ∩ fullLineCenters G S q).card = 0 → v ∉ S) ∧
      ((G.neighborFinset v ∩ fullLineCenters G S q).card = 2 → v ∈ S) := by
  intro v hv
  have hp :=
    c4Free_binarySquare_pureEndpoint_fullCenter_internalDegree_profile
      G hfree hq hqm hreg hcard S hempty hshore htri v hv
  by_cases hvS : v ∈ S
  · rcases hp.1 hvS with hdeg | hdeg
    · exact ⟨by omega, by omega, fun _ => hvS⟩
    · exact ⟨by omega, by omega, fun _ => hvS⟩
  · rcases hp.2 hvS with hdeg | hdeg
    · exact ⟨by omega, fun _ => hvS, by omega⟩
    · exact ⟨by omega, fun _ => hvS, by omega⟩

end

end Erdos85

#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_centerGraph_degree_shape

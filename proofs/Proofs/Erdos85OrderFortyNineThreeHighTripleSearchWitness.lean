import Proofs.Erdos85OrderFortyNineThreeHighTripleJointCandidateSearch
import Proofs.Erdos85ThreeHighJointResolutionSearch
import Proofs.Erdos85ThreeHighCrossPrunedDFS

namespace Erdos85
open SimpleGraph

def threeHighFullCandidateSearch (p : ThreeBlockFullParameters) (q : ThreeHighSecondaryTuple) : Bool :=
  threeHighCrossPrunedDFS (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q)
    (fun cross => threeHighJointResolutionSearch
      (threeHighEmptyAdj (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
      threeHighCanonicalResidual threeHighCanonicalRow)

def threeHighDeficientCandidateSearch (p : ThreeBlockDeficientParameters)
    (q : ThreeHighSecondaryTuple) : Bool :=
  threeHighCrossPrunedDFS (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q)
    (fun cross => threeHighJointResolutionSearch
      (threeHighEmptyAdj (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
      threeHighCanonicalResidual threeHighCanonicalRow)

noncomputable section
attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain threeHighResolutionDomain
  threeHighFullCandidateSearch threeHighDeficientCandidateSearch threeHighJointResolutionSearch

/- The following hypotheses are certificate obligations, not established results. -/
theorem threeHigh_triple_excluded_of_search_certificates
    (hfull : ∀ p ∈ threeBlockFullCandidates, ∀ q ∈ threeHighSecondaryDomain,
      threeHighFullCandidateSearch p q = false)
    (hdeficient : ∀ p ∈ threeBlockDeficientCandidates, ∀ q ∈ threeHighSecondaryDomain,
      threeHighDeficientCandidateSearch p q = false)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) : False := by
  classical
  have hroot := threeHigh_triple_root_empty_neighbor_count G hfree hmin hHigh hone z hz
  change (G.neighborFinset z ∩ threeHighTripleEmptySet G).card = 1 at hroot
  obtain ⟨u,hu'⟩ := Finset.card_pos.mp (show 0 <
      (G.neighborFinset z ∩ threeHighTripleEmptySet G).card by rw [hroot]; omega)
  have hu := (Finset.mem_inter.mp hu').2
  have huz := ((G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hu').1).symm
  obtain ⟨s,t,v,hst,hsv,htv,hS⟩ := Finset.card_eq_three.mp
    (threeHigh_triple_special_singleton_count G hfree hmin hHigh z hz)
  rcases threeHigh_triple_secondary_edges_three_or_four G hfree hmin hHigh hone z hz hu huz with hr | hr
  · exact threeHigh_triple_three_secondary_edges_excluded_of_joint_dfs
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
      (by simpa only [threeHighDeficientCandidateSearch] using hdeficient)
  · exact threeHigh_triple_four_secondary_edges_excluded_of_joint_dfs
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
      (by simpa only [threeHighFullCandidateSearch] using hfull)

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_excluded_of_search_certificates

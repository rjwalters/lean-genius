import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyJointCandidates
import Proofs.Erdos85ThreeHighJointResolutionSearch
import Proofs.Erdos85ThreeHighCrossPrunedDFS

namespace Erdos85
open SimpleGraph
noncomputable section
attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain threeHighResolutionDomain

theorem threeHigh_triple_four_secondary_edges_joint_search_witness
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 4) :
    ∃ (p : ThreeBlockFullParameters) (q : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      p ∈ threeBlockFullCandidates ∧ q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q) ∧
      threeHighJointResolutionSearch (threeHighEmptyAdj (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
        threeHighCanonicalResidual threeHighCanonicalRow = true := by
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_four_secondary_edges_empty_joint_candidate G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨p,q,cross,hp,hq,hc,?_⟩
  exact threeHighJointResolutionSearch_of_families _ _ _ F hF hblock
    (fun i j _ => hcompat i j) hcap

theorem threeHigh_triple_four_secondary_edges_excluded_of_joint_dfs
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 4)
    (hreject : ∀ p ∈ threeBlockFullCandidates, ∀ q ∈ threeHighSecondaryDomain,
      threeHighCrossPrunedDFS (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q)
        (fun cross => threeHighJointResolutionSearch (threeHighEmptyAdj (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
          threeHighCanonicalResidual threeHighCanonicalRow) = false) : False := by
  obtain ⟨p,q,cross,hp,hq,hc,ha⟩ :=
    threeHigh_triple_four_secondary_edges_joint_search_witness
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := threeHighCrossPrunedDFS_witness _ _
    (fun cross => threeHighJointResolutionSearch
      (threeHighEmptyAdj (threeHighFullUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
      threeHighCanonicalResidual threeHighCanonicalRow) cross hc ha
  rw [hreject p hp q hq] at h
  contradiction

theorem threeHigh_triple_three_secondary_edges_joint_search_witness
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 3) :
    ∃ (p : ThreeBlockDeficientParameters) (q : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      p ∈ threeBlockDeficientCandidates ∧ q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q) ∧
      threeHighJointResolutionSearch (threeHighEmptyAdj (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
        threeHighCanonicalResidual threeHighCanonicalRow = true := by
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_three_secondary_edges_empty_joint_candidate G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨p,q,cross,hp,hq,hc,?_⟩
  exact threeHighJointResolutionSearch_of_families _ _ _ F hF hblock
    (fun i j _ => hcompat i j) hcap

theorem threeHigh_triple_three_secondary_edges_excluded_of_joint_dfs
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (s t v : Fin 49) (hst : s ≠ t) (hsv : s ≠ v) (htv : t ≠ v)
    (hS : threeHighTripleSpecialSet G z = {s,t,v})
    (hr : (G.induce (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) :
      Set (Fin 49))).edgeFinset.card = 3)
    (hreject : ∀ p ∈ threeBlockDeficientCandidates, ∀ q ∈ threeHighSecondaryDomain,
      threeHighCrossPrunedDFS (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q)
        (fun cross => threeHighJointResolutionSearch (threeHighEmptyAdj (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
          threeHighCanonicalResidual threeHighCanonicalRow) = false) : False := by
  obtain ⟨p,q,cross,hp,hq,hc,ha⟩ :=
    threeHigh_triple_three_secondary_edges_joint_search_witness
      G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := threeHighCrossPrunedDFS_witness _ _
    (fun cross => threeHighJointResolutionSearch
      (threeHighEmptyAdj (threeHighDeficientUnionAdj p) (threeHighSecondaryTupleAdj q) cross)
      threeHighCanonicalResidual threeHighCanonicalRow) cross hc ha
  rw [hreject p hp q hq] at h
  contradiction

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_joint_search_witness
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_excluded_of_joint_dfs
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_joint_search_witness
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_excluded_of_joint_dfs

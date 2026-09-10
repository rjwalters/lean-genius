import Proofs.Erdos85OrderFortyNineThreeHighTripleCompactJointCandidates
import Proofs.Erdos85ThreeHighCrossPrunedDFS

/- Compact actual candidate witnesses survive prefix family-intersection pruning.
The universal false-search hypotheses below remain explicit certificate obligations. -/

namespace Erdos85
open SimpleGraph

def ThreeHighJointWitness (B : Fin 24 → Fin 24 → Bool) : Prop :=
  ∃ F : Fin 3 → Finset (Finset (Fin 24)),
    (∀ k, F k ∈ threeHighResolutionDomain B (threeHighCanonicalResidual k)) ∧
    (∀ k S, S ∈ F k → encodedTripleBlockCap threeHighCanonicalRow S = true) ∧
    (∀ i j, encodedFamilyCompatibility B (F i) (F j) = true) ∧
    (∀ i j, i ≠ j → encodedFamilyIntersectionCap (F i) (F j) = true)

def ThreeHighTerminalSound (accept : (Fin 24 → Fin 24 → Bool) → Bool) : Prop :=
  ∀ B, ThreeHighJointWitness B → accept B = true

noncomputable section
attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain threeHighResolutionDomain

theorem threeHigh_triple_four_secondary_edges_terminal_search_witness
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
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
    ∃ (p : ThreeBlockFirstRowParameters) (q : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates ∧ q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) ∧
      accept (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
        = true := by
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_four_secondary_edges_compact_joint_candidate G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨p,q,cross,hp,hq,hc,?_⟩
  exact hsound _ ⟨F,hF,hblock,hcompat,hcap⟩

theorem threeHigh_triple_four_secondary_edges_excluded_of_terminal_dfs
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
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
    (hreject : ∀ p, threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates → ∀ q ∈ threeHighSecondaryDomain,
      threeHighCrossPrunedDFS (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q)
        (fun cross => accept (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
          ) = false) : False := by
  obtain ⟨p,q,cross,hp,hq,hc,ha⟩ :=
    threeHigh_triple_four_secondary_edges_terminal_search_witness
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := threeHighCrossPrunedDFS_witness _ _
    (fun cross => accept
      (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
      ) cross hc ha
  rw [hreject p hp q hq] at h
  contradiction

theorem threeHigh_triple_three_secondary_edges_terminal_search_witness
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
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
    ∃ (p : ThreeBlockDeficientFirstRowParameters) (q : ThreeHighSecondaryTuple) (cross : ThreeHighCross),
      threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates ∧ q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) ∧
      accept (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
        = true := by
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_three_secondary_edges_compact_joint_candidate G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨p,q,cross,hp,hq,hc,?_⟩
  exact hsound _ ⟨F,hF,hblock,hcompat,hcap⟩

theorem threeHigh_triple_three_secondary_edges_excluded_of_terminal_dfs
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
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
    (hreject : ∀ p, threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates → ∀ q ∈ threeHighSecondaryDomain,
      threeHighCrossPrunedDFS (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q)
        (fun cross => accept (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
          ) = false) : False := by
  obtain ⟨p,q,cross,hp,hq,hc,ha⟩ :=
    threeHigh_triple_three_secondary_edges_terminal_search_witness
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := threeHighCrossPrunedDFS_witness _ _
    (fun cross => accept
      (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
      ) cross hc ha
  rw [hreject p hp q hq] at h
  contradiction

end

def threeHighFullTerminalCandidateSearch (accept : (Fin 24 → Fin 24 → Bool) → Bool) (p : ThreeBlockFirstRowParameters) (q : ThreeHighSecondaryTuple) : Bool :=
  threeHighCrossPrunedDFS (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q)
    (fun cross => accept
      (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
      )

def threeHighDeficientTerminalCandidateSearch (accept : (Fin 24 → Fin 24 → Bool) → Bool) (p : ThreeBlockDeficientFirstRowParameters)
    (q : ThreeHighSecondaryTuple) : Bool :=
  threeHighCrossPrunedDFS (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q)
    (fun cross => accept
      (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj q) cross)
      )

attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain threeHighResolutionDomain
  threeHighFullTerminalCandidateSearch threeHighDeficientTerminalCandidateSearch

/- The following hypotheses are certificate obligations, not established results. -/
theorem threeHigh_triple_excluded_of_terminal_certificates
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
    (hfull : ∀ p, threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates → ∀ q ∈ threeHighSecondaryDomain,
      threeHighFullTerminalCandidateSearch accept p q = false)
    (hdeficient : ∀ p, threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates → ∀ q ∈ threeHighSecondaryDomain,
      threeHighDeficientTerminalCandidateSearch accept p q = false)
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
  · exact threeHigh_triple_three_secondary_edges_excluded_of_terminal_dfs
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
      (by simpa only [threeHighDeficientTerminalCandidateSearch] using hdeficient)
  · exact threeHigh_triple_four_secondary_edges_excluded_of_terminal_dfs
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
      (by simpa only [threeHighFullTerminalCandidateSearch] using hfull)


end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_terminal_search_witness
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_excluded_of_terminal_dfs
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_terminal_search_witness
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_excluded_of_terminal_dfs

#print axioms Erdos85.threeHigh_triple_excluded_of_terminal_certificates

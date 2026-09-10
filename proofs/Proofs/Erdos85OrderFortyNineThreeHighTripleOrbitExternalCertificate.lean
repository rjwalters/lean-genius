import Proofs.Erdos85OrderFortyNineThreeHighTripleOrbitExternalCandidates
import Proofs.Erdos85OrderFortyNineThreeHighTripleTerminalCertificate
import Proofs.Erdos85ThreeHighExternalPrefixPruning

/- Actual R21 candidates survive external-special-block prefix pruning.
Both universal false-search premises remain unproved certificate obligations. -/
namespace Erdos85
open SimpleGraph

noncomputable section
attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain threeHighResolutionDomain

theorem threeHigh_triple_four_secondary_edges_orbit_external_search_witness
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
    ∃ (p : ThreeBlockFirstRowParameters) (q : Fin 21) (cross : ThreeHighCross),
      threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates ∧ threeHighSecondaryRepresentative q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) threeHighCanonicalRow = true ∧
      accept (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        = true := by
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,hExt,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_four_secondary_edges_orbit_external_candidate G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨p,q,cross,hp,hq,hc,hExt,?_⟩
  exact hsound _ ⟨F,hF,hblock,hcompat,hcap⟩

theorem threeHigh_triple_four_secondary_edges_excluded_of_orbit_external_dfs
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
    (hreject : ∀ p, threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates → ∀ q : Fin 21,
      threeHighExternalPrunedDFS (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) threeHighCanonicalRow
        (fun cross => accept (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
          ) = false) : False := by
  obtain ⟨p,q,cross,hp,hq,hc,hExt,ha⟩ :=
    threeHigh_triple_four_secondary_edges_orbit_external_search_witness
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := threeHighExternalPrunedDFS_witness _ _ threeHighCanonicalRow
    (fun cross => accept
      (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      ) cross hc hExt ha
  rw [hreject p hp q] at h
  contradiction

theorem threeHigh_triple_three_secondary_edges_orbit_external_search_witness
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
    ∃ (p : ThreeBlockDeficientFirstRowParameters) (q : Fin 21) (cross : ThreeHighCross),
      threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates ∧ threeHighSecondaryRepresentative q ∈ threeHighSecondaryDomain ∧
      cross ∈ threeHighCrossDomain (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross) threeHighCanonicalRow = true ∧
      accept (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
        = true := by
  obtain ⟨e,p,q,cross,hp,hq,hc,heu,he,hExt,F,hF,hblock,hcompat,hcap⟩ :=
    threeHigh_triple_three_secondary_edges_orbit_external_candidate G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨p,q,cross,hp,hq,hc,hExt,?_⟩
  exact hsound _ ⟨F,hF,hblock,hcompat,hcap⟩

theorem threeHigh_triple_three_secondary_edges_excluded_of_orbit_external_dfs
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
    (hreject : ∀ p, threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates → ∀ q : Fin 21,
      threeHighExternalPrunedDFS (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) threeHighCanonicalRow
        (fun cross => accept (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
          ) = false) : False := by
  obtain ⟨p,q,cross,hp,hq,hc,hExt,ha⟩ :=
    threeHigh_triple_three_secondary_edges_orbit_external_search_witness
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  have h := threeHighExternalPrunedDFS_witness _ _ threeHighCanonicalRow
    (fun cross => accept
      (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      ) cross hc hExt ha
  rw [hreject p hp q] at h
  contradiction

end

def threeHighFullOrbitExternalCandidateSearch (accept : (Fin 24 → Fin 24 → Bool) → Bool) (p : ThreeBlockFirstRowParameters) (q : Fin 21) : Bool :=
  threeHighExternalPrunedDFS (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) threeHighCanonicalRow
    (fun cross => accept
      (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      )

def threeHighDeficientOrbitExternalCandidateSearch (accept : (Fin 24 → Fin 24 → Bool) → Bool) (p : ThreeBlockDeficientFirstRowParameters)
    (q : Fin 21) : Bool :=
  threeHighExternalPrunedDFS (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) threeHighCanonicalRow
    (fun cross => accept
      (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p)) (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)
      )

attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighCrossDomain threeHighResolutionDomain
  threeHighFullOrbitExternalCandidateSearch threeHighDeficientOrbitExternalCandidateSearch

/- The following hypotheses are certificate obligations, not established results. -/
theorem threeHigh_triple_excluded_of_orbit_external_certificates
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
    (hfull : ∀ p, threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates → ∀ q : Fin 21,
      threeHighFullOrbitExternalCandidateSearch accept p q = false)
    (hdeficient : ∀ p, threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates → ∀ q : Fin 21,
      threeHighDeficientOrbitExternalCandidateSearch accept p q = false)
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
  · exact threeHigh_triple_three_secondary_edges_excluded_of_orbit_external_dfs
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
      (by simpa only [threeHighDeficientOrbitExternalCandidateSearch] using hdeficient)
  · exact threeHigh_triple_four_secondary_edges_excluded_of_orbit_external_dfs
      accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
      (by simpa only [threeHighFullOrbitExternalCandidateSearch] using hfull)


end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_orbit_external_search_witness
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_excluded_of_orbit_external_dfs
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_orbit_external_search_witness
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_excluded_of_orbit_external_dfs

#print axioms Erdos85.threeHigh_triple_excluded_of_orbit_external_certificates

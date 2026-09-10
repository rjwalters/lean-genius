import Proofs.Erdos85OrderFortyNineThreeHighTripleOrbitExternalCertificate
import Proofs.Erdos85ThreeHighAvailableBlockDFS

namespace Erdos85
open SimpleGraph

abbrev ThreeHighExternalSearch :=
  (Fin 15 → Fin 15 → Bool) → (Fin 8 → Fin 8 → Bool) → (ThreeHighCross → Bool) → Bool

/-- The external block cap is retained explicitly in the search interface. -/
def ThreeHighExternalSearchSound (search : ThreeHighExternalSearch) : Prop :=
  ∀ U R accept cross, cross ∈ threeHighCrossDomain U R →
    encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true →
    accept cross = true → search U R accept = true

attribute [local irreducible] threeHighCrossDomain

theorem threeHighAvailableBlockDFS_sound :
    ThreeHighExternalSearchSound threeHighAvailableBlockDFS := by
  intro U R accept cross hc hExt ha
  exact threeHighAvailableBlockDFS_witness U R accept cross hc hExt ha

attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
  threeHighSecondaryDomain threeHighResolutionDomain

/-- Both universal search rejections remain explicit certificate obligations. -/
theorem threeHigh_triple_excluded_of_external_search_certificates
    (search : ThreeHighExternalSearch) (hsearch : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (hsound : ThreeHighTerminalSound accept)
    (hfull : ∀ p, threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates → ∀ q : Fin 21,
      search (threeHighFullUnionAdj (threeBlockFirstRowEmbed p))
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))
        (fun cross => accept (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p))
          (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)) = false)
    (hdeficient : ∀ p, threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates → ∀ q : Fin 21,
      search (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p))
        (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q))
        (fun cross => accept (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p))
          (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) cross)) = false)
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
  · obtain ⟨p,q,cross,hp,hq,hc,hExt,ha⟩ :=
      threeHigh_triple_three_secondary_edges_orbit_external_search_witness
        accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
    have h := hsearch _ _ (fun c => accept (threeHighEmptyAdj
      (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) c)) cross hc hExt ha
    rw [hdeficient p hp q] at h
    contradiction
  · obtain ⟨p,q,cross,hp,hq,hc,hExt,ha⟩ :=
      threeHigh_triple_four_secondary_edges_orbit_external_search_witness
        accept hsound G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
    have h := hsearch _ _ (fun c => accept (threeHighEmptyAdj
      (threeHighFullUnionAdj (threeBlockFirstRowEmbed p))
      (threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative q)) c)) cross hc hExt ha
    rw [hfull p hp q] at h
    contradiction

end Erdos85
#print axioms Erdos85.threeHighAvailableBlockDFS_sound
#print axioms Erdos85.threeHigh_triple_excluded_of_external_search_certificates

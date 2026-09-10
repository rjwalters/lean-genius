import Proofs.Erdos85ThreeBlockCandidateDomains

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Erdos85
open SimpleGraph
noncomputable section
attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates
theorem threeHigh_triple_four_secondary_edges_candidate
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
    ∃ (e : (Fin 3 × Fin 5) ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)))
      (p : ThreeBlockFullParameters),
      p ∈ threeBlockFullCandidates ∧
      ∀ a b, decide (G.Adj (e a).val (e b).val) = threeBlockFullParameterAdj p a b := by
  obtain ⟨e,π,masks,hm,hpass,he⟩ := threeHigh_triple_four_secondary_edges_union_template_admissible
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  let p : ThreeBlockFullParameters := (fun k => ⟨masks k, hm k⟩, π)
  have hfun : threeBlockFullParameterAdj p = threeBlockMatchingAdj masks π := rfl
  refine ⟨e,p,?_,?_⟩
  · apply (threeBlockFullCandidates_mem_iff p).mpr
    rw [hfun]
    exact hpass
  · rw [hfun]
    exact he

theorem threeHigh_triple_three_secondary_edges_candidate
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
    ∃ (e : (Fin 3 × Fin 5) ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)))
      (p : ThreeBlockDeficientParameters),
      p ∈ threeBlockDeficientCandidates ∧
      ∀ a b, decide (G.Adj (e a).val (e b).val) = threeBlockDeficientParameterAdj p a b := by
  obtain ⟨e,π,d,masks,hm,hpass,he⟩ := threeHigh_triple_three_secondary_edges_union_template_admissible
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  let p : ThreeBlockDeficientParameters := ((fun k => ⟨masks k, hm k⟩, π), d)
  have hfun : threeBlockDeficientParameterAdj p = threeBlockDeficientMatchingAdj masks π d := rfl
  refine ⟨e,p,?_,?_⟩
  · apply (threeBlockDeficientCandidates_mem_iff p).mpr
    rw [hfun]
    exact hpass
  · rw [hfun]
    exact he

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_candidate
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_candidate

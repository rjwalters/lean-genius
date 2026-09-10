import Proofs.Erdos85EncodedC4Filter
import Proofs.Erdos85OrderFortyNineThreeHighTripleUnionTemplate
import Proofs.Erdos85OrderFortyNineThreeHighTripleDeficientUnionTemplate

namespace Erdos85
open SimpleGraph
noncomputable section
theorem threeHigh_triple_four_secondary_edges_union_template_admissible
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
      (π : Equiv.Perm (Fin 5)) (masks : Fin 3 → BitVec 10),
      (∀ k, masks k ∈ finFiveTwoEdgeMatchingMasks) ∧
      encodedC4Free (threeBlockMatchingAdj masks π) = true ∧
      ∀ p q, decide (G.Adj (e p).val (e q).val) = threeBlockMatchingAdj masks π p q := by
  classical
  obtain ⟨e,π,masks,hm,he⟩ := threeHigh_triple_four_secondary_edges_union_template
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨e,π,masks,hm,?_,he⟩
  exact encodedC4Free_of_injective_graph G hfree (fun p => (e p).val)
    (fun p q h => e.injective (Subtype.ext h)) _ he

theorem threeHigh_triple_three_secondary_edges_union_template_admissible
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
      (π : Equiv.Perm (Fin 5)) (d : Fin 5) (masks : Fin 3 → BitVec 10),
      (∀ k, masks k ∈ finFiveTwoEdgeMatchingMasks) ∧
      encodedC4Free (threeBlockDeficientMatchingAdj masks π d) = true ∧
      ∀ p q, decide (G.Adj (e p).val (e q).val) = threeBlockDeficientMatchingAdj masks π d p q := by
  classical
  obtain ⟨e,π,d,masks,hm,he⟩ := threeHigh_triple_three_secondary_edges_union_template
    G hfree hmin hHigh hone z hz hu huz s t v hst hsv htv hS hr
  refine ⟨e,π,d,masks,hm,?_,he⟩
  exact encodedC4Free_of_injective_graph G hfree (fun p => (e p).val)
    (fun p q h => e.injective (Subtype.ext h)) _ he

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_four_secondary_edges_union_template_admissible
#print axioms Erdos85.threeHigh_triple_three_secondary_edges_union_template_admissible

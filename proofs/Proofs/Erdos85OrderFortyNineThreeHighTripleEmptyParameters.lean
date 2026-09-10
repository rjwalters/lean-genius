import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyLabelTemplate
import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCoordinateDegrees
import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryParameters

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_empty_parameterization
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (lU : Fin 15 ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49))) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
    ∃ (e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)))
      (choice : Fin 2 → Option (Fin 6)) (ε : Bool) (cross : Fin 15 → Fin 8 → Bool),
      (e 23).val = u ∧
      (∀ i, (e (threeHighEmptyUIndex i)).val = (lU i).val) ∧
      (∀ p q, decide (G.Adj (e p).val (e q).val) = threeHighEmptyAdj
        (fun i j => decide (G.Adj (lU i).val (lU j).val))
        (threeHighSecondaryAdj m choice ε) cross p q) ∧
      (∀ i, (SimpleGraph.comap e (G.induce (↑(threeHighTripleEmptySet G) : Set (Fin 49)))).degree i =
        if i = 23 then 6 else 4) := by
  classical
  obtain ⟨lR, choice, ε, hN, hT, hR⟩ := threeHigh_triple_secondary_parameterization
    G hfree hmin hHigh hone z hz hu huz
  obtain ⟨e, cross, heu, heU, he, hd⟩ := threeHigh_triple_empty_template_of_labelings
    G hfree hmin hHigh hone z hz hu huz lU lR _ hN hT hR
  exact ⟨e, choice, ε, cross, heu, heU, he, hd⟩

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_parameterization

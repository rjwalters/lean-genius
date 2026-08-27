import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveThirdStructural

/-!
# Graph consumer for the adaptive `b1` third split

This converts the finite structural witness table into the form used by the
order-49 graph pipeline.  A C4-free graph realizing the fixed `b1` edges and
the two selected adaptive edges must lie in the explicit sixteen-cube
residual set.
-/

namespace Erdos85

open SimpleGraph

theorem orderFortyNineThreeHighB1AdaptiveResidual_of_graph
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (li ri : Fin 8)
    (hfixed : ∀ i j,
      orderFortyNineThreeHighB1AdaptiveFixedEdge i j = true → G.Adj i j)
    (hleft : G.Adj 18 (orderFortyNineThreeHighB1AdaptiveCandidates li))
    (hright : G.Adj 20 (orderFortyNineThreeHighB1AdaptiveCandidates ri)) :
    orderFortyNineThreeHighB1AdaptiveResidual li ri = true := by
  apply orderFortyNineThreeHighB1AdaptiveResidual_of_c4Free
    (fun i j => decide (G.Adj i j))
  · intro i j hij
    have hcommon := common_le_one_of_not_containsC4 hfree i j hij
    have heq :
        Finset.univ.filter (fun k => decide (G.Adj i k) && decide (G.Adj j k)) =
          G.neighborFinset i ∩ G.neighborFinset j := by
      ext k
      simp [SimpleGraph.mem_neighborFinset]
    rw [heq]
    exact hcommon
  · intro i j hij
    simp only [orderFortyNineThreeHighB1AdaptiveAvailableEdge,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hij
    rcases hij with (hfixedEdge | hleftEdge | hleftEdge') |
      hrightEdge | hrightEdge'
    · simpa only [decide_eq_true_eq] using hfixed i j hfixedEdge
    · rcases hleftEdge with ⟨rfl, rfl⟩
      simpa only [decide_eq_true_eq] using hleft
    · rcases hleftEdge' with ⟨rfl, rfl⟩
      simpa only [decide_eq_true_eq] using (G.adj_comm _ _).mp hleft
    · rcases hrightEdge with ⟨rfl, rfl⟩
      simpa only [decide_eq_true_eq] using hright
    · rcases hrightEdge' with ⟨rfl, rfl⟩
      simpa only [decide_eq_true_eq] using (G.adj_comm _ _).mp hright

end Erdos85

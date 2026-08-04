import Proofs.Erdos85DeletePair

/-!
# Degree-compensated paired repair

This broadens the canonical repair theorem by allowing the old graph to lose
edges before the adjacent pair is attached.  The only degree requirement is
the exact compensated inequality for each surviving vertex.
-/

open SimpleGraph

namespace Erdos85

/-- Add an adjacent pair to an arbitrary finite `C₄`-free graph.  Old vertices
may start below degree `d`, provided membership in `S` and `T` supplies enough
new incident edges to restore degree `d`. -/
theorem c4FreeMinDegreeWitness_add_pair_of_compensated_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {n d : ℕ}
    (hcard : Fintype.card V = n)
    (hfree : ¬ containsC4 V H)
    (S T : Finset V)
    (hS : d - 1 ≤ S.card) (hT : d - 1 ≤ T.card) (hd : 1 ≤ d)
    (hcompat : PairedAttachmentCompatible H S T)
    (hcomp : ∀ v : V,
      d ≤ H.degree v + (if v ∈ S then 1 else 0) +
        (if v ∈ T then 1 else 0)) :
    C4FreeMinDegreeWitness (n + 2) d := by
  let P : SimpleGraph (Option (Option V)) :=
    attachVertex (attachVertex H S) (pairedSelector T)
  apply c4FreeMinDegreeWitness_of_card_eq P
  · simp [hcard]
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    rcases u with _ | (_ | v)
    · exact le_degree_secondEndpoint_of_pred_le H S T hT hd
    · exact le_degree_firstEndpoint_of_pred_le H S T hS hd
    · rw [show P.degree (some (some v)) =
          H.degree v + (if v ∈ S then 1 else 0) +
            (if v ∈ T then 1 else 0) by
        exact pairedAttachment_degree_old_eq H S T v]
      exact hcomp v
  · exact pairedAttachment_not_containsC4 H S T hfree hcompat

/-- **Broad delete-one/add-pair surgery.**  After deleting `x`, one may replace
the induced survivor graph by any spanning subgraph `K`.  Compatibility and
the compensated per-vertex degree inequalities are sufficient to extend the
original order by one.  This includes deleting all cross edges between the two
attachment sets, provided their endpoints have enough attachment/slack to
absorb the loss. -/
theorem c4FreeMinDegreeWitness_delete_add_pair_of_compensated_subgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {n d : ℕ}
    (hn : 1 ≤ n) (hcard : Fintype.card V = n)
    (hfree : ¬ containsC4 V G)
    (K : SimpleGraph {y : V // y ≠ x}) [DecidableRel K.Adj]
    (hKle : K ≤ G.induce {y | y ≠ x})
    (S T : Finset {y : V // y ≠ x})
    (hS : d - 1 ≤ S.card) (hT : d - 1 ≤ T.card) (hd : 1 ≤ d)
    (hcompat : PairedAttachmentCompatible K S T)
    (hcomp : ∀ v : {y : V // y ≠ x},
      d ≤ K.degree v + (if v ∈ S then 1 else 0) +
        (if v ∈ T then 1 else 0)) :
    C4FreeMinDegreeWitness (n + 1) d := by
  have hKfree : ¬ containsC4 {y : V // y ≠ x} K := by
    intro hC4
    apply hfree
    rcases hC4 with ⟨f, hf, hadj⟩
    exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
      fun i j hij => hKle (hadj i j hij)⟩
  have hsubcard : Fintype.card {y : V // y ≠ x} = n - 1 := by
    simp [hcard]
  have hw := c4FreeMinDegreeWitness_add_pair_of_compensated_degrees
    K hsubcard hKfree S T hS hT hd hcompat hcomp
  have heq : n - 1 + 2 = n + 1 := by omega
  rw [← heq]
  exact hw

end Erdos85

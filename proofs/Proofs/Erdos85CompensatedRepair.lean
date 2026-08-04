import Proofs.Erdos85DeletePair

/-!
# Degree-compensated paired repair

This broadens the canonical repair theorem by allowing the old graph to lose
edges before the adjacent pair is attached.  The only degree requirement is
the exact compensated inequality for each surviving vertex.
-/

open SimpleGraph

namespace Erdos85

/-- All unordered edges with one endpoint in `S` and one in `T`. -/
def crossEdgeSet {V : Type*} [DecidableEq V] (S T : Finset V) : Set (Sym2 V) :=
  {e | ∃ s ∈ S, ∃ t ∈ T, e = s(s, t)}

/-- Delete every edge crossing from `S` to `T`. -/
def deleteCrossEdges {V : Type*} [DecidableEq V]
    (H : SimpleGraph V) (S T : Finset V) : SimpleGraph V :=
  H.deleteEdges (crossEdgeSet S T)

/-- The number of edges incident to `v` that are removed when all `S`–`T`
cross edges are deleted. -/
noncomputable def crossEdgeLoss {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V) (v : V) : ℕ :=
  by
    classical
    exact ((H.neighborFinset v).filter
      (fun w => s(v, w) ∈ crossEdgeSet S T)).card

/-- Deleting the cross edges subtracts exactly `crossEdgeLoss` from every
vertex degree.  The additive form avoids truncated subtraction. -/
theorem degree_deleteCrossEdges_add_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V)
    [DecidableRel (deleteCrossEdges H S T).Adj] (v : V) :
    H.degree v = (deleteCrossEdges H S T).degree v + crossEdgeLoss H S T v := by
  letI : DecidablePred (fun w : V => s(v, w) ∈ crossEdgeSet S T) := Classical.decPred _
  have hneighbors : (deleteCrossEdges H S T).neighborFinset v =
      (H.neighborFinset v).filter (fun w => s(v, w) ∉ crossEdgeSet S T) := by
    ext w
    simp [deleteCrossEdges, SimpleGraph.mem_neighborFinset,
      SimpleGraph.deleteEdges_adj]
  simp only [SimpleGraph.degree, hneighbors, crossEdgeLoss]
  rw [add_comm]
  exact (Finset.card_filter_add_card_filter_not
    (fun w => s(v, w) ∈ crossEdgeSet S T)).symm

/-- Common-neighbor independence is preserved when edges are deleted. -/
theorem CommonNeighborIndependent.mono
    {V : Type*} [Fintype V] [DecidableEq V]
    {K H : SimpleGraph V} [DecidableRel K.Adj] [DecidableRel H.Adj]
    {S : Finset V} (hle : K ≤ H) (hsafe : CommonNeighborIndependent H S) :
    CommonNeighborIndependent K S := by
  intro a ha b hb hab
  have hsub : K.neighborFinset a ∩ K.neighborFinset b ⊆
      H.neighborFinset a ∩ H.neighborFinset b := by
    intro z hz
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hz ⊢
    exact ⟨hle hz.1, hle hz.2⟩
  have hzero := hsafe ha hb hab
  exact Nat.eq_zero_of_le_zero ((Finset.card_le_card hsub).trans_eq hzero)

/-- After deleting all `S`–`T` cross edges, the two sets are automatically
cross-anticomplete; their individual safety is inherited from the old graph. -/
theorem pairedAttachmentCompatible_deleteCrossEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V)
    [DecidableRel (deleteCrossEdges H S T).Adj]
    (hSsafe : CommonNeighborIndependent H S)
    (hTsafe : CommonNeighborIndependent H T)
    (hinter : (S ∩ T).card ≤ 1) :
    PairedAttachmentCompatible (deleteCrossEdges H S T) S T := by
  refine ⟨CommonNeighborIndependent.mono (H.deleteEdges_le _) hSsafe,
    CommonNeighborIndependent.mono (H.deleteEdges_le _) hTsafe,
    hinter, ?_⟩
  intro a ha b hb hab
  have hnot : s(a, b) ∉ crossEdgeSet S T := by
    exact (SimpleGraph.deleteEdges_adj.mp hab).2
  exact hnot ⟨a, ha, b, hb, rfl⟩

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

/-- Concrete compensated surgery obtained by deleting all cross edges before
attaching the new pair.  Only the resulting per-vertex degree inequalities
remain to be checked. -/
theorem c4FreeMinDegreeWitness_add_pair_deleteCrossEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {n d : ℕ}
    (hcard : Fintype.card V = n) (hfree : ¬ containsC4 V H)
    (S T : Finset V)
    [DecidableRel (deleteCrossEdges H S T).Adj]
    (hS : d - 1 ≤ S.card) (hT : d - 1 ≤ T.card) (hd : 1 ≤ d)
    (hSsafe : CommonNeighborIndependent H S)
    (hTsafe : CommonNeighborIndependent H T)
    (hinter : (S ∩ T).card ≤ 1)
    (hcomp : ∀ v : V,
      d ≤ (deleteCrossEdges H S T).degree v +
        (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)) :
    C4FreeMinDegreeWitness (n + 2) d := by
  let K := deleteCrossEdges H S T
  apply c4FreeMinDegreeWitness_add_pair_of_compensated_degrees
    K hcard
  · exact fun hC4 => hfree (containsC4_mono (H.deleteEdges_le _) hC4)
  · exact hS
  · exact hT
  · exact hd
  · exact pairedAttachmentCompatible_deleteCrossEdges H S T
      hSsafe hTsafe hinter
  · intro v
    simpa [K] using hcomp v

/-- A directly checkable form of cross-edge compensation.  Each old degree
may pay for the exact number of deleted incident cross edges, while membership
in the attachment sets contributes one new edge apiece. -/
theorem c4FreeMinDegreeWitness_add_pair_deleteCrossEdges_of_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {n d : ℕ}
    (hcard : Fintype.card V = n) (hfree : ¬ containsC4 V H)
    (S T : Finset V)
    [DecidableRel (deleteCrossEdges H S T).Adj]
    (hS : d - 1 ≤ S.card) (hT : d - 1 ≤ T.card) (hd : 1 ≤ d)
    (hSsafe : CommonNeighborIndependent H S)
    (hTsafe : CommonNeighborIndependent H T)
    (hinter : (S ∩ T).card ≤ 1)
    (hloss : ∀ v : V,
      d + crossEdgeLoss H S T v ≤ H.degree v +
        (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)) :
    C4FreeMinDegreeWitness (n + 2) d := by
  apply c4FreeMinDegreeWitness_add_pair_deleteCrossEdges H hcard hfree S T
      hS hT hd hSsafe hTsafe hinter
  intro v
  have hdeg := degree_deleteCrossEdges_add_loss H S T v
  have hv := hloss v
  omega

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

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

@[simp] theorem pair_mem_crossEdgeSet_iff
    {V : Type*} [DecidableEq V] (S T : Finset V) (v w : V) :
    s(v, w) ∈ crossEdgeSet S T ↔
      (v ∈ S ∧ w ∈ T) ∨ (v ∈ T ∧ w ∈ S) := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨hb, ha⟩
  · rintro (⟨hv, hw⟩ | ⟨hv, hw⟩)
    · exact ⟨v, hv, w, hw, rfl⟩
    · exact ⟨w, hw, v, hv, by simp⟩

/-- The number of edges incident to `v` that are removed when all `S`–`T`
cross edges are deleted. -/
noncomputable def crossEdgeLoss {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V) (v : V) : ℕ :=
  by
    classical
    exact ((H.neighborFinset v).filter
      (fun w => s(v, w) ∈ crossEdgeSet S T)).card

/-- For a vertex in `S \ T`, cross-edge loss is its number of neighbors in
`T`. -/
theorem crossEdgeLoss_eq_card_neighbor_inter_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V) (v : V)
    (hvS : v ∈ S) (hvT : v ∉ T) :
    crossEdgeLoss H S T v = (H.neighborFinset v ∩ T).card := by
  classical
  apply congrArg Finset.card
  ext w
  simp [pair_mem_crossEdgeSet_iff, hvS, hvT]

/-- For a vertex in `T \ S`, cross-edge loss is its number of neighbors in
`S`. -/
theorem crossEdgeLoss_eq_card_neighbor_inter_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V) (v : V)
    (hvT : v ∈ T) (hvS : v ∉ S) :
    crossEdgeLoss H S T v = (H.neighborFinset v ∩ S).card := by
  classical
  apply congrArg Finset.card
  ext w
  simp [pair_mem_crossEdgeSet_iff, hvS, hvT]

/-- Vertices outside both attachment sets lose no cross edge. -/
theorem crossEdgeLoss_eq_zero_of_not_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V) (v : V)
    (hvS : v ∉ S) (hvT : v ∉ T) :
    crossEdgeLoss H S T v = 0 := by
  classical
  simp [crossEdgeLoss, pair_mem_crossEdgeSet_iff, hvS, hvT]

/-- Every incident edge selected for cross deletion contributes positive loss
at its endpoint. -/
theorem one_le_crossEdgeLoss_of_adj_of_pair_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V) {v w : V}
    (hvw : H.Adj v w) (hedge : s(v, w) ∈ crossEdgeSet S T) :
    1 ≤ crossEdgeLoss H S T v := by
  classical
  rw [crossEdgeLoss, Finset.one_le_card]
  exact ⟨w, Finset.mem_filter.mpr
    ⟨by simpa using hvw, hedge⟩⟩

theorem one_le_crossEdgeLoss_of_adj_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S T : Finset V) {v w : V}
    (hvw : H.Adj v w) (hvS : v ∈ S) (hwT : w ∈ T) :
    1 ≤ crossEdgeLoss H S T v := by
  apply one_le_crossEdgeLoss_of_adj_of_pair_mem H S T hvw
  exact pair_mem_crossEdgeSet_iff S T v w |>.mpr (Or.inl ⟨hvS, hwT⟩)

/-- A vertex with the one-unit deletion defect must receive at least one of
the two new attachment edges. -/
theorem mem_union_of_one_defect_compensated
    {V : Type*} [DecidableEq V] (S T : Finset V)
    {d degree loss : ℕ} (hd : 1 ≤ d) (v : V) (hdeg : degree = d - 1)
    (hbudget : d + loss ≤ degree +
      (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)) :
    v ∈ S ∪ T := by
  by_contra hv
  have hvS : v ∉ S := fun h => hv (Finset.mem_union_left T h)
  have hvT : v ∉ T := fun h => hv (Finset.mem_union_right S h)
  rw [hdeg] at hbudget
  simp only [if_neg hvS, if_neg hvT, add_zero] at hbudget
  omega

/-- If a one-defect vertex also loses a cross edge, both new attachment edges
are forced. -/
theorem mem_inter_of_one_defect_pos_crossEdgeLoss
    {V : Type*} [DecidableEq V] (S T : Finset V)
    {d degree loss : ℕ} (hd : 1 ≤ d) (v : V) (hdeg : degree = d - 1)
    (hbudget : d + loss ≤ degree +
      (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0))
    (hloss : 1 ≤ loss) :
    v ∈ S ∩ T := by
  rw [Finset.mem_inter]
  constructor
  · by_contra hvS
    rw [hdeg] at hbudget
    simp only [if_neg hvS] at hbudget
    by_cases hvT : v ∈ T
    · simp only [if_pos hvT] at hbudget
      omega
    · simp only [if_neg hvT, add_zero] at hbudget
      omega
  · by_contra hvT
    rw [hdeg] at hbudget
    simp only [if_neg hvT, add_zero] at hbudget
    by_cases hvS : v ∈ S
    · simp only [if_pos hvS] at hbudget
      omega
    · simp only [if_neg hvS, add_zero] at hbudget
      omega

/-- With the paired-attachment intersection bound, at most one one-defect
vertex can suffer positive cross-edge loss. -/
theorem card_one_defect_pos_loss_le_one
    {V : Type*} [DecidableEq V] (D S T : Finset V)
    {d : ℕ} (degree loss : V → ℕ) (hd : 1 ≤ d)
    (hdeg : ∀ v ∈ D, degree v = d - 1)
    (hbudget : ∀ v ∈ D, d + loss v ≤ degree v +
      (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0))
    (hloss : ∀ v ∈ D, 1 ≤ loss v)
    (hinter : (S ∩ T).card ≤ 1) : D.card ≤ 1 := by
  apply (Finset.card_le_card ?_).trans hinter
  intro v hv
  exact mem_inter_of_one_defect_pos_crossEdgeLoss S T hd v
    (hdeg v hv) (hbudget v hv) (hloss v hv)


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

/-- **Maximality of canonical cross deletion.**  Among spanning subgraphs of
`H` compatible with attaching a connected pair along fixed sets `S,T`,
`deleteCrossEdges H S T` is the largest: every compatible subgraph must omit
every original cross edge. -/
theorem le_deleteCrossEdges_of_pairedAttachmentCompatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (S T : Finset V) (hKH : K ≤ H)
    (hcompat : PairedAttachmentCompatible K S T) :
    K ≤ deleteCrossEdges H S T := by
  intro a b hab
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨hKH hab, ?_⟩
  rw [pair_mem_crossEdgeSet_iff]
  rintro (⟨haS, hbT⟩ | ⟨haT, hbS⟩)
  · exact hcompat.2.2.2 haS hbT hab
  · exact hcompat.2.2.2 hbS haT hab.symm

theorem degree_le_deleteCrossEdges_of_pairedAttachmentCompatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (S T : Finset V) [DecidableRel (deleteCrossEdges H S T).Adj]
    (hKH : K ≤ H) (hcompat : PairedAttachmentCompatible K S T) (v : V) :
    K.degree v ≤ (deleteCrossEdges H S T).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro w hw
  rw [SimpleGraph.mem_neighborFinset] at hw ⊢
  exact le_deleteCrossEdges_of_pairedAttachmentCompatible
    H K S T hKH hcompat hw

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

/-- **Delete-one/cross-delete/add-pair surgery.**  Delete `x`, remove all
cross edges between two safe attachment sets in the survivor graph, and then
attach an adjacent pair.  The exact loss inequality is sufficient to obtain
an order-`n+1` witness. -/
theorem c4FreeMinDegreeWitness_delete_add_pair_deleteCrossEdges_of_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) {n d : ℕ}
    (hn : 1 ≤ n) (hcard : Fintype.card V = n)
    (hfree : ¬ containsC4 V G)
    (S T : Finset {y : V // y ≠ x})
    [DecidableRel
      (deleteCrossEdges (G.induce {y | y ≠ x}) S T).Adj]
    (hS : d - 1 ≤ S.card) (hT : d - 1 ≤ T.card) (hd : 1 ≤ d)
    (hSsafe : CommonNeighborIndependent (G.induce {y | y ≠ x}) S)
    (hTsafe : CommonNeighborIndependent (G.induce {y | y ≠ x}) T)
    (hinter : (S ∩ T).card ≤ 1)
    (hloss : ∀ v : {y : V // y ≠ x},
      d + crossEdgeLoss (G.induce {y | y ≠ x}) S T v ≤
        (G.induce {y | y ≠ x}).degree v +
          (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)) :
    C4FreeMinDegreeWitness (n + 1) d := by
  have hHcard : Fintype.card {y : V // y ≠ x} = n - 1 := by
    simp [hcard]
  have hHfree : ¬ containsC4 {y : V // y ≠ x}
      (G.induce {y : V | y ≠ x}) := by
    intro hC4
    apply hfree
    rcases hC4 with ⟨f, hf, hadj⟩
    exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  have hw := c4FreeMinDegreeWitness_add_pair_deleteCrossEdges_of_loss
    (G.induce {y : V | y ≠ x}) hHcard hHfree S T
      hS hT hd hSsafe hTsafe hinter hloss
  have heq : n - 1 + 2 = n + 1 := by omega
  rw [← heq]
  exact hw

/-- A witness has a compensated cross-edge repair when some deleted vertex
and two safe attachment sets satisfy the exact degree-loss budget.  Unlike
`HasRepairSet`, this permits edges between the attachment sets: those edges
are removed and paid for by degree slack or by the new attachments. -/
def HasCompensatedCrossRepair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Prop :=
  ∃ (x : V) (S T : Finset {y : V // y ≠ x}),
    d - 1 ≤ S.card ∧ d - 1 ≤ T.card ∧
    CommonNeighborIndependent (G.induce {y | y ≠ x}) S ∧
    CommonNeighborIndependent (G.induce {y | y ≠ x}) T ∧
    (S ∩ T).card ≤ 1 ∧
    ∀ v : {y : V // y ≠ x},
      d + crossEdgeLoss (G.induce {y | y ≠ x}) S T v ≤
        (G.induce {y | y ≠ x}).degree v +
          (if v ∈ S then 1 else 0) + (if v ∈ T then 1 else 0)

/-- A compensated cross-edge repair extends a positive-degree witness by one
vertex. -/
theorem c4FreeMinDegreeWitness_succ_of_compensatedCrossRepair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {n d : ℕ}
    (hn : 1 ≤ n) (hcard : Fintype.card V = n)
    (hd : 1 ≤ d) (hfree : ¬ containsC4 V G)
    (hrepair : HasCompensatedCrossRepair G d) :
    C4FreeMinDegreeWitness (n + 1) d := by
  obtain ⟨x, S, T, hS, hT, hSsafe, hTsafe, hinter, hloss⟩ := hrepair
  letI : DecidableRel
      (deleteCrossEdges (G.induce {y : V | y ≠ x}) S T).Adj :=
    Classical.decRel _
  exact c4FreeMinDegreeWitness_delete_add_pair_deleteCrossEdges_of_loss
    G x hn hcard hfree S T hS hT hd hSsafe hTsafe hinter hloss

/-- A uniform compensated-repair choice is sufficient for witness extension,
and hence is a new concrete route to eventual monotonicity. -/
theorem witnessExtension_of_compensatedCrossRepair {n : ℕ} (hn : 1 ≤ n)
    (hrepair : ∀ d (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      1 ≤ d → d ≤ G.minDegree → ¬ containsC4 (Fin n) G →
      HasCompensatedCrossRepair G d) :
    C4FreeWitnessExtension n := by
  rintro d ⟨G, hdec, hmin, hfree⟩
  letI : DecidableRel G.Adj := hdec
  by_cases hd0 : d = 0
  · subst d
    refine ⟨⊥, Classical.decRel _, Nat.zero_le _, ?_⟩
    rintro ⟨f, _, hadj⟩
    simpa using hadj 0 1 (by decide)
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
    exact c4FreeMinDegreeWitness_succ_of_compensatedCrossRepair
      G hn (by simp) hd hfree (hrepair d G hdec hd hmin hfree)

end Erdos85

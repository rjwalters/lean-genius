import Proofs.Erdos85ManufacturedSelectorCompatibility

/-!
# Canonical reconstruction after a vertex partition

Split the vertices into a deleted set and its complement, retain the induced
graphs on both sides, and attach each deleted vertex to all of its surviving
old neighbours.  This canonical gadget attachment simply reconstructs the
original graph.  Here this fact is expressed directly through the three exact
common-neighbour budgets, avoiding a separate graph-isomorphism construction.
-/

open SimpleGraph

namespace Erdos85

/-- Common neighbours split between `D` and its complement.  In a `C₄`-free
graph the sum of the two parts is at most one. -/
theorem card_survivingCommon_add_deletedCommon_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hfree : ¬ containsC4 V G)
    {x y : V} (hxy : x ≠ y) :
    (Finset.univ.filter fun z : {v : V // v ∉ D} =>
        G.Adj x z.1 ∧ G.Adj y z.1).card +
      (Finset.univ.filter fun z : {v : V // v ∈ (D : Set V)} =>
        G.Adj x z.1 ∧ G.Adj y z.1).card ≤ 1 := by
  classical
  let eS : {v : V // v ∉ D} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let eD : {v : V // v ∈ (D : Set V)} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let S : Finset V :=
    (Finset.univ.filter fun z : {v : V // v ∉ D} =>
      G.Adj x z.1 ∧ G.Adj y z.1).map eS
  let T : Finset V :=
    (Finset.univ.filter fun z : {v : V // v ∈ (D : Set V)} =>
      G.Adj x z.1 ∧ G.Adj y z.1).map eD
  have hSsub : S ⊆ G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    change z ∈ (Finset.univ.filter fun z : {v : V // v ∉ D} =>
      G.Adj x z.1 ∧ G.Adj y z.1).map eS at hz
    rw [Finset.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
    simpa [eS] using hv
  have hTsub : T ⊆ G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    change z ∈ (Finset.univ.filter fun z : {v : V // v ∈ (D : Set V)} =>
      G.Adj x z.1 ∧ G.Adj y z.1).map eD at hz
    rw [Finset.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
    simpa [eD] using hv
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    change z ∈ (Finset.univ.filter fun z : {v : V // v ∉ D} =>
      G.Adj x z.1 ∧ G.Adj y z.1).map eS at hzS
    change z ∈ (Finset.univ.filter fun z : {v : V // v ∈ (D : Set V)} =>
      G.Adj x z.1 ∧ G.Adj y z.1).map eD at hzT
    rw [Finset.mem_map] at hzS hzT
    obtain ⟨s, _hs, rfl⟩ := hzS
    obtain ⟨t, _ht, hst⟩ := hzT
    dsimp [eS, eD] at hst
    exact s.2 (hst ▸ t.2)
  have hunion : S ∪ T ⊆
      G.neighborFinset x ∩ G.neighborFinset y :=
    Finset.union_subset hSsub hTsub
  have hcard : S.card + T.card ≤ 1 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_card hunion).trans
      ((not_containsC4_iff_forall_common_le_one G).mp hfree x y hxy)
  simpa [S, T] using hcard

/-- **Canonical reconstruction compatibility.**  The deleted induced graph,
the surviving induced graph, and all original cross edges form a compatible
gadget attachment whenever the original graph is `C₄`-free. -/
theorem canonicalReconstruction_gadgetCompatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hfree : ¬ containsC4 V G) :
    GadgetAttachmentCompatible
      (deleteVertexSetGraph G D)
      (G.induce (D : Set V))
      (fun w : {x : V // x ∈ (D : Set V)} =>
        survivingNeighborSelector G D w.1) := by
  apply (canonicalSurvivingSelectors_compatible_iff
    G D hfree (G.induce (D : Set V))
      (fun w : {x : V // x ∈ (D : Set V)} => w.1)
      (fun w => by simpa using w.2) Subtype.val_injective).2
  constructor
  · intro u w huw
    have hpart := card_survivingCommon_add_deletedCommon_le_one
      G D hfree (x := u.1) (y := w.1)
        (fun h => huw (Subtype.ext h))
    have hsurv : survivingNeighborSelector G D u.1 ∩
        survivingNeighborSelector G D w.1 =
        Finset.univ.filter fun z : {v : V // v ∉ D} =>
          G.Adj u.1 z.1 ∧ G.Adj w.1 z.1 := by
      ext z
      simp
    have hdel : (G.induce (D : Set V)).neighborFinset u ∩
        (G.induce (D : Set V)).neighborFinset w =
        Finset.univ.filter fun z : {v : V // v ∈ (D : Set V)} =>
          G.Adj u.1 z.1 ∧ G.Adj w.1 z.1 := by
      ext z
      rw [Finset.mem_inter]
      rw [mem_neighborFinset, mem_neighborFinset]
      simp only [SimpleGraph.induce_adj, Function.Embedding.coe_subtype]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsurv, hdel]
    exact hpart
  · intro x w
    have hpart := card_survivingCommon_add_deletedCommon_le_one
      G D hfree (x := x.1) (y := w.1)
        (fun heq => x.2 (heq ▸ w.2))
    have hdel : ((G.induce (D : Set V)).neighborFinset w |>.filter
        fun u => G.Adj u.1 x.1) =
        Finset.univ.filter fun u : {v : V // v ∈ (D : Set V)} =>
          G.Adj x.1 u.1 ∧ G.Adj w.1 u.1 := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [mem_neighborFinset]
      simp only [SimpleGraph.induce_adj, Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨hwu, hux⟩
        exact ⟨hux.symm, hwu⟩
      · rintro ⟨hxu, hwu⟩
        exact ⟨hwu, hxu.symm⟩
    rw [hdel]
    simpa [and_comm] using hpart

/-- In the canonical reconstruction, every new (deleted-side) vertex recovers
exactly its original degree. -/
theorem canonicalReconstruction_degree_new
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (w : {x : V // x ∈ (D : Set V)}) :
    (attachGadget (deleteVertexSetGraph G D) (G.induce (D : Set V))
      (fun u : {x : V // x ∈ (D : Set V)} =>
        survivingNeighborSelector G D u.1)).degree (.inr w) =
      G.degree w.1 := by
  classical
  rw [attachGadget_degree_new]
  rw [← G.card_neighborFinset_eq_degree w.1]
  let eS : {v : V // v ∉ D} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let eD : {v : V // v ∈ (D : Set V)} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let S := (survivingNeighborSelector G D w.1).map eS
  let T := ((G.induce (D : Set V)).neighborFinset w).map eD
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro z hzS hzT
    change z ∈ (survivingNeighborSelector G D w.1).map eS at hzS
    change z ∈ ((G.induce (D : Set V)).neighborFinset w).map eD at hzT
    rw [Finset.mem_map] at hzS hzT
    obtain ⟨s, _hs, rfl⟩ := hzS
    obtain ⟨t, _ht, hst⟩ := hzT
    dsimp [eS, eD] at hst
    exact s.2 (hst ▸ t.2)
  have hunion : S ∪ T = G.neighborFinset w.1 := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp hz with hz | hz
      · change z ∈ (survivingNeighborSelector G D w.1).map eS at hz
        rw [Finset.mem_map] at hz
        obtain ⟨s, hs, rfl⟩ := hz
        rw [mem_neighborFinset]
        exact (mem_survivingNeighborSelector G D w.1 s).mp hs
      · change z ∈ ((G.induce (D : Set V)).neighborFinset w).map eD at hz
        rw [Finset.mem_map] at hz
        obtain ⟨t, ht, rfl⟩ := hz
        rw [mem_neighborFinset]
        have ht' : (G.induce (D : Set V)).Adj w t :=
          ((G.induce (D : Set V)).mem_neighborFinset w t).mp ht
        dsimp [eD]
        simpa only [SimpleGraph.induce_adj, Function.Embedding.coe_subtype] using ht'
    · intro hz
      rw [mem_neighborFinset] at hz
      by_cases hzD : z ∈ D
      · apply Finset.mem_union_right S
        rw [Finset.mem_map]
        refine ⟨⟨z, hzD⟩, ?_, rfl⟩
        apply ((G.induce (D : Set V)).mem_neighborFinset w ⟨z, by simpa using hzD⟩).mpr
        simpa only [SimpleGraph.induce_adj, Function.Embedding.coe_subtype]
      · apply Finset.mem_union_left T
        rw [Finset.mem_map]
        refine ⟨⟨z, hzD⟩, ?_, rfl⟩
        exact (mem_survivingNeighborSelector G D w.1 ⟨z, hzD⟩).2 hz
  rw [← hunion, Finset.card_union_of_disjoint hdisj]
  simp [S, T]

end Erdos85

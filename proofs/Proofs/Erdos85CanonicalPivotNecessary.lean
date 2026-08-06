import Proofs.Erdos85ManufacturedDefectClique

/-!
# Necessary conditions for canonical pivot gadgets

Canonical selectors manufactured from deleted pivots are safe individually,
but gadget edges impose additional geometry: the two corresponding survivor
blocks must be cross-anticomplete.  In a regular ambient graph, the new-vertex
degree budget also forces the gadget degree at a pivot to pay for every
deleted neighbour of that pivot.
-/

open SimpleGraph

namespace Erdos85

/-- An edge is allowed between two canonical pivots only when their surviving
neighbour blocks are anticomplete in the ambient graph. -/
def CanonicalPivotAllowed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (x y : V) : Prop :=
  ∀ a : {v : V // v ∉ D}, a ∈ survivingNeighborSelector G D x →
    ∀ b : {v : V // v ∉ D}, b ∈ survivingNeighborSelector G D y →
      ¬ G.Adj a.1 b.1

/-- Every gadget edge forces cross-anticompleteness of its two selector
blocks.  In particular this applies to arbitrary subselectors of canonical
pivot blocks. -/
theorem cross_anticomplete_of_gadget_edge
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D})
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F A)
    {u w : W} (huw : F.Adj u w) :
    ∀ a, a ∈ A u → ∀ b, b ∈ A w → ¬ G.Adj a.1 b.1 := by
  intro a ha b hb hab
  have hempty := hcompat.neighbor_inter_selector_eq_empty_of_adj
    (deleteVertexSetGraph G D) F A huw ha
  have hbmem : b ∈
      (deleteVertexSetGraph G D).neighborFinset a ∩ A w := by
    rw [Finset.mem_inter, mem_neighborFinset]
    exact ⟨hab, hb⟩
  rw [hempty] at hbmem
  exact Finset.notMem_empty b hbmem

/-- Hence a gadget edge between full canonical selectors belongs to the
allowed-pivot relation. -/
theorem canonicalPivotAllowed_of_gadget_edge
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (pivot : W → V)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F
      (fun z ↦ survivingNeighborSelector G D (pivot z)))
    {u w : W} (huw : F.Adj u w) :
    CanonicalPivotAllowed G D (pivot u) (pivot w) := by
  intro a ha b hb
  exact cross_anticomplete_of_gadget_edge
    G D F (fun z ↦ survivingNeighborSelector G D (pivot z))
    hcompat huw a ha b hb

/-- The full canonical selector partitions a pivot's neighbourhood into its
surviving and deleted parts. -/
theorem card_survivingNeighborSelector_add_deleted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (x : V) :
    (survivingNeighborSelector G D x).card +
        (G.neighborFinset x ∩ D).card = G.degree x := by
  classical
  let e : {v : V // v ∉ D} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (survivingNeighborSelector G D x).map e =
      G.neighborFinset x \ D := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨a, ha, rfl⟩ := hy
      rw [Finset.mem_sdiff, mem_neighborFinset]
      change G.Adj x a.1 ∧ a.1 ∉ D
      exact ⟨(mem_survivingNeighborSelector G D x a).mp ha, a.2⟩
    · intro hy
      rw [Finset.mem_sdiff, mem_neighborFinset] at hy
      let a : {v : V // v ∉ D} := ⟨y, hy.2⟩
      rw [Finset.mem_map]
      refine ⟨a, ?_, rfl⟩
      rw [mem_survivingNeighborSelector]
      exact hy.1
  have hcard := Finset.card_sdiff_add_card_inter (G.neighborFinset x) D
  rw [← Finset.card_map e, hmap]
  simpa [G.card_neighborFinset_eq_degree] using hcard

/-- **Dominating-degree necessity.**  In a `d`-regular ambient graph, if a
new gadget vertex uses the full canonical selector of its pivot and must
reach degree `d`, then its internal gadget degree is at least the number of
deleted neighbours of that pivot. -/
theorem deletedNeighbor_card_le_gadget_degree_of_full_canonical
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (pivot : W → V) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hnew : ∀ w, d ≤
      (survivingNeighborSelector G D (pivot w)).card + F.degree w) :
    ∀ w, (G.neighborFinset (pivot w) ∩ D).card ≤ F.degree w := by
  intro w
  have hpartition := card_survivingNeighborSelector_add_deleted
    G D (pivot w)
  rw [hreg] at hpartition
  have hw := hnew w
  omega

/-- Packaged necessary criterion: full canonical compatible selectors make
`F` a subgraph of the allowed-pivot relation, while their new-degree budgets
dominate the deleted-neighbour degree at every pivot. -/
theorem canonicalPivot_allowed_and_dominating
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (pivot : W → V) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G D) F
      (fun z ↦ survivingNeighborSelector G D (pivot z)))
    (hnew : ∀ w, d ≤
      (survivingNeighborSelector G D (pivot w)).card + F.degree w) :
    (∀ u w, F.Adj u w →
      CanonicalPivotAllowed G D (pivot u) (pivot w)) ∧
    (∀ w, (G.neighborFinset (pivot w) ∩ D).card ≤ F.degree w) := by
  exact ⟨fun _ _ huw ↦
      canonicalPivotAllowed_of_gadget_edge G D F pivot hcompat huw,
    deletedNeighbor_card_le_gadget_degree_of_full_canonical
      G D F pivot hreg hnew⟩

end Erdos85

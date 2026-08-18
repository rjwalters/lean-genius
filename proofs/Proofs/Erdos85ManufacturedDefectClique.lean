import Proofs.Erdos85DeleteGadget

/-!
# Defect cliques manufactured by deleting vertices

Deleting a vertex destroys the common neighbour it supplied to every pair
of its surviving neighbours.  In a `C₄`-free graph there was no second
common neighbour, so those surviving neighbours form a safe selector in the
deleted graph.  This is the local geometric source of the manufactured
cliques used in delete-set/add-gadget surgery.
-/

open SimpleGraph

namespace Erdos85

/-- The neighbours of `x` which survive deletion of `D`, regarded as
vertices of the deleted graph. -/
def survivingNeighborSelector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (x : V) : Finset {v : V // v ∉ D} :=
  Finset.univ.filter fun v => G.Adj x v.1

@[simp] theorem mem_survivingNeighborSelector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (x : V) (v : {v : V // v ∉ D}) :
    v ∈ survivingNeighborSelector G D x ↔ G.Adj x v.1 := by
  simp [survivingNeighborSelector]

/-- Every deleted pivot manufactures a common-neighbour-independent
selector consisting of all its surviving neighbours. -/
theorem commonNeighborIndependent_survivingNeighborSelector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (x : V) (hx : x ∈ D)
    (hfree : ¬ containsC4 V G) :
    CommonNeighborIndependent (deleteVertexSetGraph G D)
      (survivingNeighborSelector G D x) := by
  intro a ha b hb hab
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro z hz
  rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hz
  have hax : G.Adj a.1 x :=
    (mem_survivingNeighborSelector G D x a).mp ha |>.symm
  have hbx : G.Adj b.1 x :=
    (mem_survivingNeighborSelector G D x b).mp hb |>.symm
  have haz : G.Adj a.1 z.1 :=
    hz.1
  have hbz : G.Adj b.1 z.1 :=
    hz.2
  have hxz : x ≠ z.1 := by
    intro h
    apply z.2
    rwa [← h]
  exact hfree (containsC4_of_two_common
    (fun h => hab (Subtype.ext h)) hxz
    hax.symm hbx.symm haz.symm hbz.symm)

/-- Any family obtained by taking subsets of manufactured pivot selectors is
automatically supported on vertices damaged by the deletion.  This supplies
the support hypothesis of the manufactured-clique counting pivot; the
remaining construction problem is compatibility and degree coverage. -/
theorem selectorFamily_deleted_support_of_subset_survivingNeighborSelector
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (pivot : W → V)
    (hpivot : ∀ w, pivot w ∈ D)
    (A : W → Finset {v : V // v ∉ D})
    (hA : ∀ w, A w ⊆ survivingNeighborSelector G D (pivot w)) :
    ∀ ⦃v⦄, v ∈ Finset.univ.biUnion A →
      1 ≤ (G.neighborFinset v.1 ∩ D).card := by
  intro v hv
  rw [Finset.mem_biUnion] at hv
  obtain ⟨w, _, hvw⟩ := hv
  rw [Finset.one_le_card]
  refine ⟨pivot w, Finset.mem_inter.mpr ⟨?_, hpivot w⟩⟩
  rw [mem_neighborFinset]
  exact ((mem_survivingNeighborSelector G D (pivot w) v).mp
    (hA w hvw)).symm

end Erdos85

import Proofs.Erdos85ManufacturedDefectClique

/-!
# Compatibility of manufactured pivot selectors

This file evaluates the three gadget-compatibility budgets for the canonical
selector family consisting of all surviving neighbours of deleted pivots.
For distinct pivots in a `C₄`-free graph, the old--old budget is automatic:
surviving common neighbours and deleted pivots represented by selectors are
disjoint parts of the original common-neighbour set.  The new--new and mixed
budgets remain as the exact construction constraints.
-/

open SimpleGraph

namespace Erdos85

/-- Canonical selectors belonging to distinct deleted pivots meet in at most
one survivor. -/
theorem card_inter_survivingNeighborSelector_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hfree : ¬ containsC4 V G)
    {x y : V} (hxy : x ≠ y) :
    (survivingNeighborSelector G D x ∩
      survivingNeighborSelector G D y).card ≤ 1 := by
  classical
  let e : {v : V // v ∉ D} ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  have hmap :
      ((survivingNeighborSelector G D x ∩
        survivingNeighborSelector G D y).map e) ⊆
          G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    rw [Finset.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [Finset.mem_inter] at hv ⊢
    simp only [mem_survivingNeighborSelector] at hv
    rw [mem_neighborFinset, mem_neighborFinset]
    dsimp [e]
    exact hv
  rw [← Finset.card_map e]
  exact (Finset.card_le_card hmap).trans
    ((not_containsC4_iff_forall_common_le_one G).mp hfree x y hxy)

/-- For an injectively indexed family of deleted pivots, the old--old
compatibility budget of the canonical selector family is automatic. -/
theorem canonicalSurvivingSelectors_old_budget
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hfree : ¬ containsC4 V G)
    (pivot : W → V) (hpivot : ∀ w, pivot w ∈ D)
    (hpivotinj : Function.Injective pivot) :
    ∀ a b : {v : V // v ∉ D}, a ≠ b →
      ((deleteVertexSetGraph G D).neighborFinset a ∩
          (deleteVertexSetGraph G D).neighborFinset b).card +
        (Finset.univ.filter fun w =>
          a ∈ survivingNeighborSelector G D (pivot w) ∧
          b ∈ survivingNeighborSelector G D (pivot w)).card ≤ 1 := by
  classical
  intro a b hab
  let valEmb : {v : V // v ∉ D} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let pivotEmb : W ↪ V := ⟨pivot, hpivotinj⟩
  let S : Finset V :=
    ((deleteVertexSetGraph G D).neighborFinset a ∩
      (deleteVertexSetGraph G D).neighborFinset b).map valEmb
  let I : Finset W := Finset.univ.filter fun w =>
    a ∈ survivingNeighborSelector G D (pivot w) ∧
    b ∈ survivingNeighborSelector G D (pivot w)
  let P : Finset V := I.map pivotEmb
  have hSsub : S ⊆ G.neighborFinset a.1 ∩ G.neighborFinset b.1 := by
    intro z hz
    change z ∈ ((deleteVertexSetGraph G D).neighborFinset a ∩
      (deleteVertexSetGraph G D).neighborFinset b).map valEmb at hz
    rw [Finset.mem_map] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    rw [Finset.mem_inter] at hv ⊢
    rw [mem_neighborFinset, mem_neighborFinset]
    dsimp [valEmb]
    rw [mem_neighborFinset, mem_neighborFinset] at hv
    simpa only [deleteVertexSetGraph, SimpleGraph.induce_adj,
      Function.Embedding.coe_subtype] using hv
  have hPsub : P ⊆ G.neighborFinset a.1 ∩ G.neighborFinset b.1 := by
    intro z hz
    change z ∈ I.map pivotEmb at hz
    rw [Finset.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    change w ∈ Finset.univ.filter (fun w =>
      a ∈ survivingNeighborSelector G D (pivot w) ∧
      b ∈ survivingNeighborSelector G D (pivot w)) at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_survivingNeighborSelector] at hw
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset]
    exact ⟨hw.1.symm, hw.2.symm⟩
  have hdisj : Disjoint S P := by
    rw [Finset.disjoint_left]
    intro z hzS hzP
    change z ∈ I.map pivotEmb at hzP
    rw [Finset.mem_map] at hzP
    obtain ⟨w, _hw, rfl⟩ := hzP
    have hpD := hpivot w
    change pivot w ∈
      ((deleteVertexSetGraph G D).neighborFinset a ∩
        (deleteVertexSetGraph G D).neighborFinset b).map valEmb at hzS
    rw [Finset.mem_map] at hzS
    obtain ⟨v, _hv, hv⟩ := hzS
    dsimp [valEmb, pivotEmb] at hv
    exact v.2 (hv.symm ▸ hpD)
  have hunion : S ∪ P ⊆
      G.neighborFinset a.1 ∩ G.neighborFinset b.1 :=
    Finset.union_subset hSsub hPsub
  have hcommon := (not_containsC4_iff_forall_common_le_one G).mp hfree
    a.1 b.1 (fun h ↦ hab (Subtype.ext h))
  have hcard : S.card + P.card ≤ 1 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_card hunion).trans hcommon
  simpa [S, P, I] using hcard

/-- The mixed budget for canonical pivot selectors, rewritten entirely in
ambient-graph language. -/
theorem canonicalSurvivingSelectors_mixed_budget_iff
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (F : SimpleGraph W) [DecidableRel F.Adj]
    (pivot : W → V) :
    (∀ x : {v : V // v ∉ D}, ∀ w : W,
      ((deleteVertexSetGraph G D).neighborFinset x ∩
          survivingNeighborSelector G D (pivot w)).card +
        (F.neighborFinset w |>.filter fun u =>
          x ∈ survivingNeighborSelector G D (pivot u)).card ≤ 1) ↔
    (∀ x : {v : V // v ∉ D}, ∀ w : W,
      (Finset.univ.filter fun y : {v : V // v ∉ D} =>
          G.Adj x.1 y.1 ∧ G.Adj (pivot w) y.1).card +
        (F.neighborFinset w |>.filter fun u =>
          G.Adj (pivot u) x.1).card ≤ 1) := by
  have hleft : ∀ (x : {v : V // v ∉ D}) (w : W),
      (deleteVertexSetGraph G D).neighborFinset x ∩
          survivingNeighborSelector G D (pivot w) =
        Finset.univ.filter fun y : {v : V // v ∉ D} =>
          G.Adj x.1 y.1 ∧ G.Adj (pivot w) y.1 := by
    intro x w
    ext y
    rw [Finset.mem_inter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and,
      mem_neighborFinset, mem_survivingNeighborSelector]
    simp only [deleteVertexSetGraph, SimpleGraph.induce_adj,
      Function.Embedding.coe_subtype]
  have hright : ∀ (x : {v : V // v ∉ D}) (w : W),
      (F.neighborFinset w |>.filter fun u =>
          x ∈ survivingNeighborSelector G D (pivot u)) =
        (F.neighborFinset w |>.filter fun u =>
          G.Adj (pivot u) x.1) := by
    intro x w
    ext u
    simp [mem_survivingNeighborSelector]
  constructor <;> intro h x w
  · simpa only [hleft x w, hright x w] using h x w
  · simpa only [hleft x w, hright x w] using h x w

/-- **Exact compatibility characterization.**  For injectively indexed
deleted pivots in a `C₄`-free graph, canonical surviving-neighbour selectors
are compatible exactly when the new--new and mixed budgets hold. -/
theorem canonicalSurvivingSelectors_compatible_iff
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) (hfree : ¬ containsC4 V G)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (pivot : W → V) (hpivot : ∀ w, pivot w ∈ D)
    (hpivotinj : Function.Injective pivot) :
    GadgetAttachmentCompatible (deleteVertexSetGraph G D) F
        (fun w => survivingNeighborSelector G D (pivot w)) ↔
      (∀ u w : W, u ≠ w →
        (survivingNeighborSelector G D (pivot u) ∩
            survivingNeighborSelector G D (pivot w)).card +
          (F.neighborFinset u ∩ F.neighborFinset w).card ≤ 1) ∧
      (∀ x : {v : V // v ∉ D}, ∀ w : W,
        (Finset.univ.filter fun y : {v : V // v ∉ D} =>
            G.Adj x.1 y.1 ∧ G.Adj (pivot w) y.1).card +
          (F.neighborFinset w |>.filter fun u =>
            G.Adj (pivot u) x.1).card ≤ 1) := by
  constructor
  · intro hcompat
    refine ⟨hcompat.2.1, ?_⟩
    exact (canonicalSurvivingSelectors_mixed_budget_iff
      G D F pivot).mp hcompat.2.2
  · rintro ⟨hnew, hmixed⟩
    refine ⟨canonicalSurvivingSelectors_old_budget
      G D hfree pivot hpivot hpivotinj, hnew, ?_⟩
    exact (canonicalSurvivingSelectors_mixed_budget_iff
      G D F pivot).mpr hmixed

end Erdos85

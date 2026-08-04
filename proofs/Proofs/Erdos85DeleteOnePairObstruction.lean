import Proofs.Erdos85ReplacementGadgetObstruction

/-!
# Delete-one/add-pair obstruction at Moore-layer order

For a regular Moore-layer graph, deleting one vertex creates unit loss exactly
on its old neighborhood.  Pairwise selector intersection bounds the weighted
loss by `d+1`, while the replacement degree-square inequality requires at
least `2(d-2)`.  Hence no arbitrary compatible two-vertex replacement exists
once `d ≥ 6`.
-/

open SimpleGraph

namespace Erdos85

/-- Surviving old neighbors of the deleted vertex. -/
def deletedNeighborSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Finset {v : V // v ∉ ({x} : Finset V)} :=
  Finset.univ.filter fun v => G.Adj v.1 x

/-- The deleted-neighbor support has size `deg(x)`. -/
theorem card_deletedNeighborSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    (deletedNeighborSupport G x).card = G.degree x := by
  let e : {v : V // v ∉ ({x} : Finset V)} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : (deletedNeighborSupport G x).map e = G.neighborFinset x := by
    ext y
    constructor
    · intro hy
      rw [Finset.mem_map] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      exact (G.mem_neighborFinset x v.1).mpr
        ((Finset.mem_filter.mp hv).2).symm
    · intro hy
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).mp hy
      have hyx : y ∉ ({x} : Finset V) := by
        simp only [Finset.mem_singleton]
        exact (G.ne_of_adj hxy).symm
      rw [Finset.mem_map]
      refine ⟨⟨y, hyx⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy.symm⟩
  rw [← G.card_neighborFinset_eq_degree x, ← hmap, Finset.card_map]

/-- With no additional survivor-edge deletion, replacement loss after
deleting one vertex is at most one. -/
theorem replacementDegreeLoss_delete_one_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (v : {v : V // v ∉ ({x} : Finset V)}) :
    replacementDegreeLoss G {x} (deleteVertexSetGraph G {x}) v ≤ 1 := by
  simp only [replacementDegreeLoss, subgraphDegreeLoss, Nat.sub_self,
    Nat.add_zero]
  exact (Finset.card_le_card Finset.inter_subset_right).trans (by simp)

/-- Positive delete-one replacement loss is supported on the old
neighborhood of the deleted vertex. -/
theorem mem_deletedNeighborSupport_of_pos_replacementDegreeLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (v : {v : V // v ∉ ({x} : Finset V)})
    (hpos : 0 < replacementDegreeLoss G {x}
      (deleteVertexSetGraph G {x}) v) :
    v ∈ deletedNeighborSupport G x := by
  simp only [replacementDegreeLoss, subgraphDegreeLoss, Nat.sub_self,
    Nat.add_zero] at hpos
  rw [deletedNeighborSupport, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  by_contra hadj
  have hinter : G.neighborFinset v.1 ∩ ({x} : Finset V) = ∅ := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, hadj]
  rw [hinter] at hpos
  simp at hpos

/-- The attachment-weighted loss after deleting one vertex is at most
`degree(x) + choose(m,2)`. -/
theorem sum_delete_one_replacementLoss_le_degree_add_choose
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ ({x} : Finset V)})
    (hcompat : GadgetAttachmentCompatible (deleteVertexSetGraph G {x}) F A) :
    (∑ w : W, ∑ a ∈ A w,
      replacementDegreeLoss G {x} (deleteVertexSetGraph G {x}) a) ≤
      G.degree x + (Fintype.card W).choose 2 := by
  rw [sum_sum_weight_eq_sum_weight_mul_attachmentMultiplicity]
  have hbound := hcompat.sum_weight_mul_attachmentMultiplicity_le
    (deleteVertexSetGraph G {x}) F A
    (fun v => replacementDegreeLoss G {x} (deleteVertexSetGraph G {x}) v)
    (deletedNeighborSupport G x)
    (replacementDegreeLoss_delete_one_le_one G x)
    (mem_deletedNeighborSupport_of_pos_replacementDegreeLoss G x)
  simpa [card_deletedNeighborSupport] using hbound

/-- **Arbitrary delete-one/add-pair no-go.**  In a `d`-regular graph of order
`d(d-1)+1`, no compatible two-vertex replacement can give both new vertices
degree at least `d` when `d ≥ 6`, even with completely arbitrary selectors. -/
theorem not_gadgetCompatible_delete_one_add_pair_of_moore_regular
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ ({x} : Finset V)})
    {d : ℕ} (hd : 6 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hreg : ∀ v : V, G.degree v = d)
    (hWcard : Fintype.card W = 2)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    ¬ GadgetAttachmentCompatible (deleteVertexSetGraph G {x}) F A := by
  intro hcompat
  letI : Nonempty V := ⟨x⟩
  have hmin : d ≤ G.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    rw [hreg v]
  have hlower :=
    card_succ_mul_degree_pred_sub_card_le_replacementLoss_of_mooreOrder
      G ({x} : Finset V) (deleteVertexSetGraph G {x}) (le_refl _)
        F A (d := d) (k := 1) (by omega) (by omega) hcard
        (by simp) hWcard hmin hnew hcompat
  have hupper := sum_delete_one_replacementLoss_le_degree_add_choose
    G x F A hcompat
  rw [hreg x, hWcard] at hupper
  norm_num at hupper
  have hsub : d - 1 - 1 + 2 = d := by omega
  nlinarith

end Erdos85

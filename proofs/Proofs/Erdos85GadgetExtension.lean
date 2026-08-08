import Proofs.Erdos85Extension

/-!
# Finite gadget extensions for Erdős Problem 85

This file generalizes one-vertex and connected-pair attachment to an arbitrary
finite graph of new vertices.  The organizing invariant is the exact
common-neighbour budget: a graph is `C₄`-free precisely when every distinct
pair has at most one common neighbour.
-/

namespace Erdos85

open SimpleGraph

/-- Exact common-neighbour characterization of `C₄`-freeness. -/
theorem not_containsC4_iff_forall_common_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ¬ containsC4 V G ↔
      ∀ x y : V, x ≠ y →
        (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
  constructor
  · intro hfree x y hxy
    by_contra hle
    have htwo : 1 < (G.neighborFinset x ∩ G.neighborFinset y).card := by omega
    obtain ⟨v, hv, v', hv', hvv'⟩ := Finset.one_lt_card.mp htwo
    have hvxy := Finset.mem_inter.mp hv
    have hv'xy := Finset.mem_inter.mp hv'
    apply hfree
    exact containsC4_of_two_common hxy hvv'
      ((G.mem_neighborFinset x v).mp hvxy.1).symm
      ((G.mem_neighborFinset y v).mp hvxy.2).symm
      ((G.mem_neighborFinset x v').mp hv'xy.1).symm
      ((G.mem_neighborFinset y v').mp hv'xy.2).symm
  · exact not_containsC4_of_forall_common_le_one

/-- Attach a finite gadget `F` to an old graph `G`.  A new vertex `w` is
joined to precisely the old vertices in `A w`. -/
def attachGadget {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (F : SimpleGraph W) (A : W → Finset V) :
    SimpleGraph (V ⊕ W) where
  Adj
    | Sum.inl x, Sum.inl y => G.Adj x y
    | Sum.inr u, Sum.inr w => F.Adj u w
    | Sum.inl x, Sum.inr w => x ∈ A w
    | Sum.inr w, Sum.inl x => x ∈ A w
  symm := by
    constructor
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y => exact G.adj_symm h
        | inr w => exact h
    | inr u =>
        cases y with
        | inl x => exact h
        | inr w => exact F.adj_symm h
  loopless := by
    constructor
    intro x h
    cases x with
    | inl x => exact G.loopless.irrefl x h
    | inr w => exact F.loopless.irrefl w h

instance attachGadget.instDecidableAdj
    {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (F : SimpleGraph W) (A : W → Finset V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] :
    DecidableRel (attachGadget G F A).Adj := by
  intro x y
  cases x <;> cases y <;> simp only [attachGadget] <;> infer_instance

@[simp] theorem attachGadget_adj_old_old {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (F : SimpleGraph W) (A : W → Finset V) (x y : V) :
    (attachGadget G F A).Adj (.inl x) (.inl y) ↔ G.Adj x y := Iff.rfl

@[simp] theorem attachGadget_adj_new_new {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (F : SimpleGraph W) (A : W → Finset V) (u w : W) :
    (attachGadget G F A).Adj (.inr u) (.inr w) ↔ F.Adj u w := Iff.rfl

@[simp] theorem attachGadget_adj_old_new {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (F : SimpleGraph W) (A : W → Finset V) (x : V) (w : W) :
    (attachGadget G F A).Adj (.inl x) (.inr w) ↔ x ∈ A w := Iff.rfl

@[simp] theorem attachGadget_adj_new_old {V W : Type*} [DecidableEq V]
    (G : SimpleGraph V) (F : SimpleGraph W) (A : W → Finset V) (w : W) (x : V) :
    (attachGadget G F A).Adj (.inr w) (.inl x) ↔ x ∈ A w := Iff.rfl

private def sumInlEmbedding (V W : Type*) : V ↪ V ⊕ W :=
  ⟨Sum.inl, Sum.inl_injective⟩

private def sumInrEmbedding (V W : Type*) : W ↪ V ⊕ W :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- Old-old common neighbours split into old common neighbours and gadget
vertices whose selectors contain both old vertices. -/
theorem attachGadget_common_old_old
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (x y : V) :
    (attachGadget G F A).neighborFinset (.inl x) ∩
        (attachGadget G F A).neighborFinset (.inl y) =
      ((G.neighborFinset x ∩ G.neighborFinset y).map (sumInlEmbedding V W)) ∪
      ((Finset.univ.filter fun w => x ∈ A w ∧ y ∈ A w).map
        (sumInrEmbedding V W)) := by
  ext z
  cases z with
  | inl z => simp [SimpleGraph.mem_neighborFinset, sumInlEmbedding, sumInrEmbedding]
  | inr z => simp [SimpleGraph.mem_neighborFinset, sumInlEmbedding, sumInrEmbedding]

theorem card_attachGadget_common_old_old
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (x y : V) :
    ((attachGadget G F A).neighborFinset (.inl x) ∩
      (attachGadget G F A).neighborFinset (.inl y)).card =
      (G.neighborFinset x ∩ G.neighborFinset y).card +
        (Finset.univ.filter fun w => x ∈ A w ∧ y ∈ A w).card := by
  rw [attachGadget_common_old_old]
  rw [Finset.card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left, sumInlEmbedding, sumInrEmbedding]

/-- New-new common neighbours split into common old attachments and common
neighbours internal to the gadget. -/
theorem attachGadget_common_new_new
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (u w : W) :
    (attachGadget G F A).neighborFinset (.inr u) ∩
        (attachGadget G F A).neighborFinset (.inr w) =
      ((A u ∩ A w).map (sumInlEmbedding V W)) ∪
      ((F.neighborFinset u ∩ F.neighborFinset w).map
        (sumInrEmbedding V W)) := by
  ext z
  cases z with
  | inl z => simp [SimpleGraph.mem_neighborFinset, sumInlEmbedding, sumInrEmbedding]
  | inr z => simp [SimpleGraph.mem_neighborFinset, sumInlEmbedding, sumInrEmbedding]

theorem card_attachGadget_common_new_new
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (u w : W) :
    ((attachGadget G F A).neighborFinset (.inr u) ∩
      (attachGadget G F A).neighborFinset (.inr w)).card =
      (A u ∩ A w).card +
        (F.neighborFinset u ∩ F.neighborFinset w).card := by
  rw [attachGadget_common_new_new]
  rw [Finset.card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left, sumInlEmbedding, sumInrEmbedding]

/-- Mixed common neighbours split into old vertices of the new selector
adjacent to the old vertex, and gadget neighbours whose selectors contain the
old vertex. -/
theorem attachGadget_common_old_new
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (x : V) (w : W) :
    (attachGadget G F A).neighborFinset (.inl x) ∩
        (attachGadget G F A).neighborFinset (.inr w) =
      ((G.neighborFinset x ∩ A w).map (sumInlEmbedding V W)) ∪
      ((F.neighborFinset w |>.filter fun u => x ∈ A u).map
        (sumInrEmbedding V W)) := by
  ext z
  cases z with
  | inl z => simp [SimpleGraph.mem_neighborFinset, sumInlEmbedding, sumInrEmbedding]
  | inr z =>
      simp [SimpleGraph.mem_neighborFinset, sumInlEmbedding, sumInrEmbedding,
        and_comm]

theorem card_attachGadget_common_old_new
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (x : V) (w : W) :
    ((attachGadget G F A).neighborFinset (.inl x) ∩
      (attachGadget G F A).neighborFinset (.inr w)).card =
      (G.neighborFinset x ∩ A w).card +
        (F.neighborFinset w |>.filter fun u => x ∈ A u).card := by
  rw [attachGadget_common_old_new]
  rw [Finset.card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left, sumInlEmbedding, sumInrEmbedding]

/-- The three exact common-neighbour budgets for a gadget extension. -/
def GadgetAttachmentCompatible
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) : Prop :=
  (∀ x y : V, x ≠ y →
    (G.neighborFinset x ∩ G.neighborFinset y).card +
      (Finset.univ.filter fun w => x ∈ A w ∧ y ∈ A w).card ≤ 1) ∧
  (∀ u w : W, u ≠ w →
    (A u ∩ A w).card +
      (F.neighborFinset u ∩ F.neighborFinset w).card ≤ 1) ∧
  (∀ x : V, ∀ w : W,
    (G.neighborFinset x ∩ A w).card +
      (F.neighborFinset w |>.filter fun u => x ∈ A u).card ≤ 1)

/-- Every individual selector in a compatible gadget attachment is
common-neighbor independent in the old graph. -/
theorem GadgetAttachmentCompatible.selector_safe
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    (w : W) : CommonNeighborIndependent G (A w) := by
  intro a ha b hb hab
  have hw : w ∈ Finset.univ.filter (fun u => a ∈ A u ∧ b ∈ A u) := by
    simp [ha, hb]
  have hone : 1 ≤
      (Finset.univ.filter (fun u => a ∈ A u ∧ b ∈ A u)).card :=
    Finset.one_le_card.mpr ⟨w, hw⟩
  have hbudget := hcompat.1 a b hab
  omega

/-- Selectors belonging to two distinct neighbours of one gadget vertex are
disjoint.  Otherwise an old vertex in both selectors would consume at least
two units of that vertex's mixed common-neighbour budget. -/
theorem GadgetAttachmentCompatible.disjoint_selectors_of_adjacent_to
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    {w u v : W} (huw : F.Adj w u) (hvw : F.Adj w v) (huv : u ≠ v) :
    Disjoint (A u) (A v) := by
  rw [Finset.disjoint_left]
  intro x hxu hxv
  have hu : u ∈ (F.neighborFinset w).filter fun t => x ∈ A t := by
    simp [SimpleGraph.mem_neighborFinset, huw, hxu]
  have hv : v ∈ (F.neighborFinset w).filter fun t => x ∈ A t := by
    simp [SimpleGraph.mem_neighborFinset, hvw, hxv]
  have htwo : 2 ≤ ((F.neighborFinset w).filter fun t => x ∈ A t).card := by
    have hsub : {u, v} ⊆ (F.neighborFinset w).filter fun t => x ∈ A t := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hu
      · exact hv
    rw [← Finset.card_pair huv]
    exact Finset.card_le_card hsub
  have hbudget := hcompat.2.2 x w
  omega

/-- Distinct compatible gadget selectors intersect in at most one old
vertex. -/
theorem GadgetAttachmentCompatible.card_selector_inter_le_one
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    {u w : W} (huw : u ≠ w) : (A u ∩ A w).card ≤ 1 := by
  have hbudget := hcompat.2.1 u w huw
  omega

/-- If `u` and `w` are adjacent inside the gadget, every old vertex attached
to `u` is anticomplete to the selector of `w`.  This is the general form of
the cross-anticompleteness constraint in connected-pair repair. -/
theorem GadgetAttachmentCompatible.neighbor_inter_selector_eq_empty_of_adj
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    {u w : W} (huw : F.Adj u w) {x : V} (hxu : x ∈ A u) :
    G.neighborFinset x ∩ A w = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  have hu : u ∈ (F.neighborFinset w).filter (fun z => x ∈ A z) := by
    simp [SimpleGraph.mem_neighborFinset, huw.symm, hxu]
  have hone : 1 ≤
      ((F.neighborFinset w).filter (fun z => x ∈ A z)).card :=
    Finset.one_le_card.mpr ⟨u, hu⟩
  have hbudget := hcompat.2.2 x w
  have hpos : 1 ≤ (G.neighborFinset x ∩ A w).card :=
    Finset.one_le_card.mpr ⟨y, hy⟩
  omega

/-- Compatibility forces the old graph itself to be `C₄`-free. -/
theorem GadgetAttachmentCompatible.old_not_containsC4
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A) :
    ¬ containsC4 V G := by
  apply (not_containsC4_iff_forall_common_le_one G).2
  intro x y hxy
  have hbudget := hcompat.1 x y hxy
  omega

/-- Compatibility also forces the internal gadget graph to be `C₄`-free. -/
theorem GadgetAttachmentCompatible.gadget_not_containsC4
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A) :
    ¬ containsC4 W F := by
  apply (not_containsC4_iff_forall_common_le_one F).2
  intro u w huw
  have hbudget := hcompat.2.1 u w huw
  omega

/-- Exact safety theorem for an arbitrary finite gadget attachment.  No
additional hypotheses are hidden: the old-old, new-new, and mixed budgets are
jointly necessary and sufficient. -/
theorem attachGadget_not_containsC4_iff_compatible
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) :
    ¬ containsC4 (V ⊕ W) (attachGadget G F A) ↔
      GadgetAttachmentCompatible G F A := by
  rw [not_containsC4_iff_forall_common_le_one]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro x y hxy
      simpa [card_attachGadget_common_old_old] using
        h (.inl x) (.inl y) (by simpa using hxy)
    · intro u w huw
      simpa [card_attachGadget_common_new_new] using
        h (.inr u) (.inr w) (by simpa using huw)
    · intro x w
      simpa [card_attachGadget_common_old_new] using
        h (.inl x) (.inr w) (by simp)
  · rintro ⟨hold, hnew, hmixed⟩ x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            rw [card_attachGadget_common_old_old]
            exact hold x y (by simpa using hxy)
        | inr w =>
            rw [card_attachGadget_common_old_new]
            exact hmixed x w
    | inr u =>
        cases y with
        | inl x =>
            rw [Finset.inter_comm, card_attachGadget_common_old_new]
            exact hmixed x u
        | inr w =>
            rw [card_attachGadget_common_new_new]
            exact hnew u w (by simpa using hxy)

/-- Degree of an old vertex after gadget attachment. -/
theorem attachGadget_degree_old
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (x : V) :
    (attachGadget G F A).degree (.inl x) = G.degree x +
      (Finset.univ.filter fun w => x ∈ A w).card := by
  have h := card_attachGadget_common_old_old G F A x x
  simpa [SimpleGraph.card_neighborFinset_eq_degree] using h

/-- Degree of a gadget vertex after attachment. -/
theorem attachGadget_degree_new
    {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (w : W) :
    (attachGadget G F A).degree (.inr w) = (A w).card + F.degree w := by
  have h := card_attachGadget_common_new_new G F A w w
  simpa [SimpleGraph.card_neighborFinset_eq_degree] using h

/-- Gadget attachment transported to the standard `Fin (n + m)` vertex type. -/
def gadgetAttachFin {n m : ℕ} (G : SimpleGraph (Fin n))
    (F : SimpleGraph (Fin m)) (A : Fin m → Finset (Fin n)) :
    SimpleGraph (Fin (n + m)) :=
  SimpleGraph.comap finSumFinEquiv.symm (attachGadget G F A)

instance gadgetAttachFin.instDecidableAdj {n m : ℕ}
    (G : SimpleGraph (Fin n)) (F : SimpleGraph (Fin m))
    (A : Fin m → Finset (Fin n)) [DecidableRel G.Adj] [DecidableRel F.Adj] :
    DecidableRel (gadgetAttachFin G F A).Adj :=
  fun x y => inferInstanceAs
    (Decidable ((attachGadget G F A).Adj
      (finSumFinEquiv.symm x) (finSumFinEquiv.symm y)))

/-- Relabelling the gadget extension onto `Fin (n + m)` preserves every
degree (the inequality form is all witness construction needs). -/
theorem gadgetAttachFin_degree_ge {n m : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : SimpleGraph (Fin m)) [DecidableRel F.Adj]
    (A : Fin m → Finset (Fin n)) (u : Fin (n + m)) :
    (attachGadget G F A).degree (finSumFinEquiv.symm u) ≤
      (gadgetAttachFin G F A).degree u := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card_of_injOn (fun w => finSumFinEquiv w)
  · intro w hw
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hw ⊢
    change (attachGadget G F A).Adj (finSumFinEquiv.symm u)
      (finSumFinEquiv.symm (finSumFinEquiv w))
    rw [Equiv.symm_apply_apply]
    exact hw
  · intro w₁ _ w₂ _ h
    exact finSumFinEquiv.injective h

/-- `C₄`-freeness transports across the canonical sum equivalence. -/
theorem gadgetAttachFin_not_containsC4 {n m : ℕ}
    (G : SimpleGraph (Fin n)) (F : SimpleGraph (Fin m))
    (A : Fin m → Finset (Fin n))
    (hfree : ¬ containsC4 (Fin n ⊕ Fin m) (attachGadget G F A)) :
    ¬ containsC4 (Fin (n + m)) (gadgetAttachFin G F A) := by
  rintro ⟨f, hinj, hadj⟩
  apply hfree
  refine ⟨fun i => finSumFinEquiv.symm (f i),
    finSumFinEquiv.symm.injective.comp hinj, ?_⟩
  intro i j hij
  exact hadj i j hij

/-- **Arbitrary finite-gadget witness extension.**  Internal gadget degree
can replace old attachments one-for-one.  The exact compatibility budgets are
the sole `C₄`-freeness requirement. -/
theorem c4FreeMinDegreeWitness_add_of_gadgetCompatible
    {n m d : ℕ} [Nonempty (Fin (n + m))]
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (F : SimpleGraph (Fin m)) [DecidableRel F.Adj]
    (A : Fin m → Finset (Fin n))
    (hdeg : d ≤ G.minDegree)
    (hnew : ∀ w : Fin m, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    C4FreeMinDegreeWitness (n + m) d := by
  refine ⟨gadgetAttachFin G F A, inferInstance, ?_, ?_⟩
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    refine le_trans ?_ (gadgetAttachFin_degree_ge G F A u)
    rcases h : finSumFinEquiv.symm u with x | w
    · rw [attachGadget_degree_old]
      exact le_trans (le_trans hdeg (G.minDegree_le_degree x)) (Nat.le_add_right _ _)
    · rw [attachGadget_degree_new]
      exact hnew w
  · apply gadgetAttachFin_not_containsC4 G F A
    exact (attachGadget_not_containsC4_iff_compatible G F A).2 hcompat

end Erdos85

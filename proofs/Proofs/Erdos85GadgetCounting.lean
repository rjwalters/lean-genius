import Proofs.Erdos85GadgetExtension

/-!
# Global counting constraints for finite gadget extensions

Summing the mixed common-neighbor budgets reveals a quantitative tradeoff:
internal gadget degree reduces the number of old attachments a new vertex
needs, but every such internal edge also consumes mixed compatibility budget.
-/

open SimpleGraph

namespace Erdos85

/-- Double-count membership in a finite family of finite sets. -/
theorem sum_card_filter_mem_eq_sum_card
    {X I : Type*} [Fintype X] [DecidableEq X] [DecidableEq I]
    (A : I → Finset X) (J : Finset I) :
    (∑ x : X, (J.filter fun i => x ∈ A i).card) =
      ∑ i ∈ J, (A i).card := by
  classical
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
      true_and] at hp ⊢
    exact hp
  · intro p hp q hq heq
    cases p
    cases q
    cases heq
    rfl
  · intro p hp
    simp only [Finset.mem_sigma] at hp
    refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter,
        true_and]
      exact hp
    · cases p
      rfl

/-- Sum of incidences between all vertices and a fixed finite set. -/
theorem sum_card_neighbor_inter_eq_sum_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ x : V, (G.neighborFinset x ∩ S).card) =
      ∑ a ∈ S, G.degree a := by
  classical
  have h := sum_card_filter_mem_eq_sum_card
    (fun a : V => G.neighborFinset a) S
  calc
    (∑ x : V, (G.neighborFinset x ∩ S).card) =
        ∑ x : V, (S.filter fun a => x ∈ G.neighborFinset a).card := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ext a
      simp [SimpleGraph.mem_neighborFinset, and_comm, G.adj_comm]
    _ = ∑ a ∈ S, (G.neighborFinset a).card := h
    _ = ∑ a ∈ S, G.degree a := by
      apply Finset.sum_congr rfl
      intro a _
      exact G.card_neighborFinset_eq_degree a

/-- Weighted adjacency is symmetric: summing the weight at the far endpoint
over all oriented gadget edges gives degree times weight. -/
theorem sum_neighbor_weight_eq_sum_degree_mul
    {W : Type*} [Fintype W] [DecidableEq W]
    (F : SimpleGraph W) [DecidableRel F.Adj] (weight : W → ℕ) :
    (∑ w : W, ∑ u ∈ F.neighborFinset w, weight u) =
      ∑ u : W, F.degree u * weight u := by
  classical
  calc
    (∑ w : W, ∑ u ∈ F.neighborFinset w, weight u) =
        ∑ w : W, ∑ u : W, if u ∈ F.neighborFinset w then weight u else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext u
        simp
      · intro u hu
        rfl
    _ = ∑ u : W, ∑ w : W,
        if u ∈ F.neighborFinset w then weight u else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ u : W, F.degree u * weight u := by
      apply Finset.sum_congr rfl
      intro u _
      rw [← Finset.sum_filter]
      have hfilter : Finset.univ.filter (fun w => u ∈ F.neighborFinset w) =
          F.neighborFinset u := by
        ext w
        simp [SimpleGraph.mem_neighborFinset, F.adj_comm]
      rw [hfilter, Finset.sum_const, F.card_neighborFinset_eq_degree]
      simp [Nat.mul_comm]

/-- Around a fixed gadget vertex, compatibility makes all neighbouring
selectors pairwise disjoint, so their total size is at most the number of old
vertices. -/
theorem GadgetAttachmentCompatible.sum_card_neighbor_selectors_le_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    (w : W) :
    (∑ u ∈ F.neighborFinset w, (A u).card) ≤ Fintype.card V := by
  classical
  have hpair : (F.neighborFinset w : Set W).Pairwise
      (fun u v => Disjoint (A u) (A v)) := by
    intro u hu v hv huv
    exact hcompat.disjoint_selectors_of_adjacent_to G F A
      ((F.mem_neighborFinset w u).mp hu)
      ((F.mem_neighborFinset w v).mp hv) huv
  calc
    (∑ u ∈ F.neighborFinset w, (A u).card) =
        ((F.neighborFinset w).biUnion A).card := by
      rw [Finset.card_biUnion hpair]
    _ ≤ Fintype.card V := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ _)

/-- Degree-sequence form of the same hub budget.  If every new vertex reaches
degree `q`, the sum of its attachment deficits `q-deg_F(u)` over the
neighbours of any gadget vertex is bounded by the old graph order. -/
theorem GadgetAttachmentCompatible.sum_neighbor_degree_deficits_le_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    (q : ℕ)
    (hnewDegree : ∀ u, q ≤ (attachGadget G F A).degree (.inr u))
    (w : W) :
    (∑ u ∈ F.neighborFinset w, (q - F.degree u)) ≤ Fintype.card V := by
  apply le_trans (Finset.sum_le_sum fun u _ => ?_)
    (hcompat.sum_card_neighbor_selectors_le_card G F A w)
  have hu := hnewDegree u
  rw [attachGadget_degree_new] at hu
  omega

/-- The gadget-side distance-two budget at a hub.  After removing the hub,
the neighbour sets of its distinct neighbours are pairwise disjoint; hence
the sum of their excess degrees is at most the number of other gadget
vertices. -/
theorem GadgetAttachmentCompatible.sum_neighbor_degree_sub_one_le
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    (w : W) :
    (∑ u ∈ F.neighborFinset w, (F.degree u - 1)) ≤
      Fintype.card W - 1 := by
  classical
  let branch : W → Finset W := fun u => F.neighborFinset u \ {w}
  have hpair : (F.neighborFinset w : Set W).Pairwise
      (fun u v => Disjoint (branch u) (branch v)) := by
    intro u hu v hv huv
    rw [Finset.disjoint_left]
    intro z hzu hzv
    have hzu' := (Finset.mem_sdiff.mp hzu).1
    have hzv' := (Finset.mem_sdiff.mp hzv).1
    have hzw : z ≠ w := by simpa using (Finset.mem_sdiff.mp hzu).2
    have hwcommon : w ∈ F.neighborFinset u ∩ F.neighborFinset v := by
      rw [Finset.mem_inter]
      have hwu : F.Adj w u := by
        simpa [SimpleGraph.mem_neighborFinset] using hu
      have hwv : F.Adj w v := by
        simpa [SimpleGraph.mem_neighborFinset] using hv
      exact ⟨by simpa [SimpleGraph.mem_neighborFinset] using F.adj_symm hwu,
        by simpa [SimpleGraph.mem_neighborFinset] using F.adj_symm hwv⟩
    have hzcommon : z ∈ F.neighborFinset u ∩ F.neighborFinset v :=
      Finset.mem_inter.mpr ⟨hzu', hzv'⟩
    have htwo : 2 ≤ (F.neighborFinset u ∩ F.neighborFinset v).card := by
      have hsub : {w, z} ⊆ F.neighborFinset u ∩ F.neighborFinset v := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hwcommon
        · exact hzcommon
      rw [← Finset.card_pair (Ne.symm hzw)]
      exact Finset.card_le_card hsub
    have hbudget := hcompat.2.1 u v huv
    omega
  have hbranch_card : ∀ u ∈ F.neighborFinset w,
      (branch u).card = F.degree u - 1 := by
    intro u hu
    dsimp [branch]
    rw [Finset.card_sdiff]
    have hmem : w ∈ F.neighborFinset u := by
      have hwu : F.Adj w u := by
        simpa [SimpleGraph.mem_neighborFinset] using hu
      simpa [SimpleGraph.mem_neighborFinset] using F.adj_symm hwu
    have hinter : {w} ∩ F.neighborFinset u = {w} :=
      Finset.inter_eq_left.mpr (by simpa using hmem)
    rw [hinter]
    simp [F.card_neighborFinset_eq_degree]
  have hunion_sub : (F.neighborFinset w).biUnion branch ⊆
      Finset.univ \ {w} := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨u, hu, hzu⟩ := hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      (Finset.mem_sdiff.mp hzu).2⟩
  calc
    (∑ u ∈ F.neighborFinset w, (F.degree u - 1)) =
        ∑ u ∈ F.neighborFinset w, (branch u).card := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hbranch_card u hu]
    _ = ((F.neighborFinset w).biUnion branch).card := by
      rw [Finset.card_biUnion hpair]
    _ ≤ (Finset.univ \ {w}).card := Finset.card_le_card hunion_sub
    _ = Fintype.card W - 1 := by
      rw [Finset.card_sdiff]
      simp

/-- Combined old-side and gadget-side hub inequality.  When gadget degrees
are at most the target `q`, every neighbour of `w` contributes exactly
`q-1` across the two budgets. -/
theorem GadgetAttachmentCompatible.degree_mul_target_sub_one_le_cards
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A)
    (q : ℕ) (hdegree : ∀ u, F.degree u ≤ q)
    (hnewDegree : ∀ u, q ≤ (attachGadget G F A).degree (.inr u))
    (w : W) :
    F.degree w * (q - 1) ≤ Fintype.card V + Fintype.card W - 1 := by
  have hold := hcompat.sum_neighbor_degree_deficits_le_card
    G F A q hnewDegree w
  have hnew := hcompat.sum_neighbor_degree_sub_one_le G F A w
  have hW : 1 ≤ Fintype.card W :=
    Fintype.card_pos_iff.mpr ⟨w⟩
  have heq : (∑ u ∈ F.neighborFinset w,
      ((q - F.degree u) + (F.degree u - 1))) =
      F.degree w * (q - 1) := by
    calc
      _ = ∑ _u ∈ F.neighborFinset w, (q - 1) := by
        apply Finset.sum_congr rfl
        intro u hu
        have huone : 1 ≤ F.degree u := by
          rw [← F.card_neighborFinset_eq_degree]
          exact Finset.one_le_card.mpr ⟨w, by
            have hwu : F.Adj w u := by
              simpa [SimpleGraph.mem_neighborFinset] using hu
            simpa [SimpleGraph.mem_neighborFinset] using F.adj_symm hwu⟩
        have hule := hdegree u
        omega
      _ = F.degree w * (q - 1) := by
        rw [Finset.sum_const, F.card_neighborFinset_eq_degree]
        simp [Nat.mul_comm]
  calc
    F.degree w * (q - 1) =
        (∑ u ∈ F.neighborFinset w, (q - F.degree u)) +
        (∑ u ∈ F.neighborFinset w, (F.degree u - 1)) := by
      rw [← heq, Finset.sum_add_distrib]
    _ ≤ Fintype.card V + (Fintype.card W - 1) :=
      Nat.add_le_add hold hnew
    _ = Fintype.card V + Fintype.card W - 1 := by omega

/-- Global form of all mixed compatibility budgets. -/
theorem GadgetAttachmentCompatible.sum_mixed_budgets_le
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) (hcompat : GadgetAttachmentCompatible G F A) :
    (∑ x : V, ∑ w : W,
      ((G.neighborFinset x ∩ A w).card +
        ((F.neighborFinset w).filter fun u => x ∈ A u).card)) ≤
      Fintype.card V * Fintype.card W := by
  calc
    _ ≤ ∑ _x : V, ∑ _w : W, 1 :=
      Finset.sum_le_sum fun x _ =>
        Finset.sum_le_sum fun w _ => hcompat.2.2 x w
    _ = Fintype.card V * Fintype.card W := by simp

/-- Exact rewriting of the global mixed-budget left side as old attachment
degree plus gadget-degree-weighted attachment size. -/
theorem sum_mixed_budgets_eq_attachment_cost
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) :
    (∑ x : V, ∑ w : W,
      ((G.neighborFinset x ∩ A w).card +
        ((F.neighborFinset w).filter fun u => x ∈ A u).card)) =
      (∑ w : W, ∑ a ∈ A w, G.degree a) +
        ∑ w : W, F.degree w * (A w).card := by
  classical
  rw [← Finset.sum_add_distrib]
  simp only [Finset.sum_add_distrib]
  have hold : (∑ x : V, ∑ w : W, (G.neighborFinset x ∩ A w).card) =
      ∑ w : W, ∑ a ∈ A w, G.degree a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    exact sum_card_neighbor_inter_eq_sum_degree G (A w)
  have hnew : (∑ x : V, ∑ w : W,
      ((F.neighborFinset w).filter fun u => x ∈ A u).card) =
      ∑ w : W, F.degree w * (A w).card := by
    rw [Finset.sum_comm]
    calc
      (∑ w : W, ∑ x : V,
          ((F.neighborFinset w).filter fun u => x ∈ A u).card) =
          ∑ w : W, ∑ u ∈ F.neighborFinset w, (A u).card := by
        apply Finset.sum_congr rfl
        intro w _
        exact sum_card_filter_mem_eq_sum_card A (F.neighborFinset w)
      _ = ∑ w : W, F.degree w * (A w).card :=
        sum_neighbor_weight_eq_sum_degree_mul F fun w => (A w).card
  omega

/-- **Finite-gadget counting obstruction.**  If old vertices already have
minimum degree `d` and every gadget vertex reaches degree `d`, compatibility
forces `Σ_w (d-r_w)(d+r_w) ≤ |V||W|`, where `r_w` is the internal
gadget degree.  For a connected pair (`|W|=2`, `r_w=1`) this recovers the
coarse `|V| ≥ d²-1` repair obstruction. -/
theorem sum_sub_degree_mul_add_degree_le_card_mul_card_of_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    (∑ w : W, (d - F.degree w) * (d + F.degree w)) ≤
      Fintype.card V * Fintype.card W := by
  have hcost := hcompat.sum_mixed_budgets_le G F A
  rw [sum_mixed_budgets_eq_attachment_cost G F A] at hcost
  have hold : (∑ w : W, d * (A w).card) ≤
      ∑ w : W, ∑ a ∈ A w, G.degree a := by
    apply Finset.sum_le_sum
    intro w _
    calc
      d * (A w).card = ∑ _a ∈ A w, d := by simp [Nat.mul_comm]
      _ ≤ ∑ a ∈ A w, G.degree a := by
        exact Finset.sum_le_sum fun a _ => hmin.trans (G.minDegree_le_degree a)
  have hattach : (∑ w : W, (A w).card * (d + F.degree w)) ≤
      Fintype.card V * Fintype.card W := by
    calc
      (∑ w : W, (A w).card * (d + F.degree w)) =
          ∑ w : W, (d * (A w).card + F.degree w * (A w).card) := by
        apply Finset.sum_congr rfl
        intro w _
        rw [Nat.mul_add, Nat.mul_comm (A w).card d,
          Nat.mul_comm (A w).card (F.degree w)]
      _ = (∑ w : W, d * (A w).card) +
          ∑ w : W, F.degree w * (A w).card := by
        rw [Finset.sum_add_distrib]
      _ ≤ (∑ w : W, ∑ a ∈ A w, G.degree a) +
          ∑ w : W, F.degree w * (A w).card := Nat.add_le_add_right hold _
      _ ≤ Fintype.card V * Fintype.card W := hcost
  apply le_trans (Finset.sum_le_sum fun w _ => ?_) hattach
  have hw := hnew w
  by_cases hr : F.degree w ≤ d
  · have hsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hr
    nlinarith
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hr)]

/-- For a nonempty `r`-regular gadget, the global obstruction simplifies to
the per-gadget-vertex bound `(d-r)(d+r) ≤ |V|`. -/
theorem sub_mul_add_le_card_of_regular_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d r : ℕ}
    (hW : 0 < Fintype.card W) (hreg : ∀ w, F.degree w = r)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    (d - r) * (d + r) ≤ Fintype.card V := by
  have hsum :=
    sum_sub_degree_mul_add_degree_le_card_mul_card_of_gadgetCompatible
      G F A hmin hnew hcompat
  simp_rw [hreg] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hsum' : ((d - r) * (d + r)) * Fintype.card W ≤
      Fintype.card V * Fintype.card W := by
    simpa [Nat.mul_comm] using hsum
  exact Nat.le_of_mul_le_mul_right hsum' hW

/-- In particular, any compatible 1-regular gadget (including the connected
pair) forces the old graph order to be at least `d²-1`. -/
theorem degree_sq_sub_one_le_card_of_one_regular_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hW : 0 < Fintype.card W) (hreg : ∀ w, F.degree w = 1)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    d * d - 1 ≤ Fintype.card V := by
  have hbound := sub_mul_add_le_card_of_regular_gadgetCompatible
    G F A hW hreg hmin hnew hcompat
  have heq : (d - 1) * (d + 1) = d * d - 1 := by
    rw [Nat.sub_mul]
    simp only [one_mul]
    have hpoly : d * (d + 1) = d * d + d := by ring
    rw [hpoly]
    omega
  rw [← heq]
  exact hbound

/-- **Universal gadget-size obstruction.**  An `m`-vertex simple gadget has
internal degree at most `m-1`.  Consequently, when `m-1 ≤ d`, every
compatible degree-`d` attachment forces
`(d-(m-1))(d+(m-1)) ≤ |V|`. -/
theorem sub_card_pred_mul_add_card_pred_le_card_of_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    (d - (Fintype.card W - 1)) * (d + (Fintype.card W - 1)) ≤
      Fintype.card V := by
  let s := Fintype.card W - 1
  let B := (d - s) * (d + s)
  have hsum :=
    sum_sub_degree_mul_add_degree_le_card_mul_card_of_gadgetCompatible
      G F A hmin hnew hcompat
  have hlower : (∑ _w : W, B) ≤
      ∑ w : W, (d - F.degree w) * (d + F.degree w) := by
    apply Finset.sum_le_sum
    intro w _
    have hrlt := F.degree_lt_card_verts w
    have hrs : F.degree w ≤ s := by
      dsimp [s]
      omega
    have hrle : F.degree w ≤ d := hrs.trans hsize
    have hdsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hrle
    have hssub : d - s + s = d := Nat.sub_add_cancel hsize
    dsimp [B]
    nlinarith
  have hmul : B * Fintype.card W ≤
      Fintype.card V * Fintype.card W := by
    apply le_trans ?_ hsum
    simpa [B, Nat.mul_comm] using hlower
  have hcancel := Nat.le_of_mul_le_mul_right hmul hW
  simpa [B, s] using hcancel

/-- Difference-of-squares form of the universal obstruction.  Thus a gadget
on `m` vertices can beat the `d²` scale only through a correction of at most
`(m-1)²`; bounded gadgets cannot remove a linear-in-`d` Moore deficit. -/
theorem degree_sq_sub_card_pred_sq_le_card_of_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    d * d - (Fintype.card W - 1) * (Fintype.card W - 1) ≤
      Fintype.card V := by
  let s := Fintype.card W - 1
  have hbound :=
    sub_card_pred_mul_add_card_pred_le_card_of_gadgetCompatible
      G F A hW hsize hmin hnew hcompat
  have heq : (d - s) * (d + s) = d * d - s * s := by
    rw [Nat.sub_mul]
    have hpoly : d * (d + s) = d * d + d * s := by ring
    have hpoly' : s * (d + s) = d * s + s * s := by ring
    rw [hpoly, hpoly']
    omega
  change d * d - s * s ≤ Fintype.card V
  rw [← heq]
  simpa [s] using hbound

/-- Below the difference-of-squares bound, no compatible gadget attachment
can give all new vertices degree `d`. -/
theorem not_gadgetCompatible_of_card_lt_degree_sq_sub_card_pred_sq
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hsmall : Fintype.card V <
      d * d - (Fintype.card W - 1) * (Fintype.card W - 1)) :
    ¬ GadgetAttachmentCompatible G F A := by
  intro hcompat
  exact (not_lt_of_ge
    (degree_sq_sub_card_pred_sq_le_card_of_gadgetCompatible
      G F A hW hsize hmin hnew hcompat)) hsmall

/-- At the Moore-layer order `d(d-1)+1`, a compatible gadget must have
`(m-1)² ≥ d-1`.  In particular its size cannot remain bounded while `d`
grows. -/
theorem degree_sub_one_le_card_pred_sq_of_mooreOrder_gadgetCompatible
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ} (hd : 1 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible G F A) :
    d - 1 ≤ (Fintype.card W - 1) * (Fintype.card W - 1) := by
  let s := Fintype.card W - 1
  have hbound := degree_sq_sub_card_pred_sq_le_card_of_gadgetCompatible
    G F A hW hsize hmin hnew hcompat
  change d * d - s * s ≤ Fintype.card V at hbound
  change d - 1 ≤ s * s
  by_contra hnot
  have hs : s * s < d - 1 := Nat.lt_of_not_ge hnot
  have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hssq : s * s ≤ d * d := by nlinarith
  have hdiff : d * d - s * s + s * s = d * d := Nat.sub_add_cancel hssq
  rw [hcard] at hbound
  nlinarith

end Erdos85

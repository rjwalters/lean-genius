import Proofs.Erdos85GadgetDegreeSquares

/-!
# Obstructions for true delete-set/replacement-gadget surgery

This incorporates both sources of survivor degree loss: neighbors deleted
with the vertex set and additional survivor edges deleted before attachment.
The resulting inequalities apply directly to delete-`k`/add-`k+1`
order-raising repair.
-/

open SimpleGraph

namespace Erdos85

/-- Total degree lost by a survivor: incident deleted vertices plus additional
incident survivor edges removed when the induced graph is replaced by `K`. -/
def replacementDegreeLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (v : {v : V // v ∉ D}) : ℕ :=
  (G.neighborFinset v.1 ∩ D).card +
    subgraphDegreeLoss (deleteVertexSetGraph G D) K v

/-- The final survivor degree plus its total replacement loss is the original
degree. -/
theorem degree_add_replacementDegreeLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D) (v : {v : V // v ∉ D}) :
    K.degree v + replacementDegreeLoss G D K v = G.degree v.1 := by
  have hsplit := degree_subgraph_add_losses G D K hKle v
  simp only [replacementDegreeLoss]
  omega

/-- Loss-corrected mixed-budget obstruction measured against the original
pre-deletion minimum degree. -/
theorem sum_sub_degree_mul_add_degree_le_survivor_mul_gadget_add_replacementLoss
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d : ℕ}
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    (∑ w : W, (d - F.degree w) * (d + F.degree w)) ≤
      Fintype.card {v : V // v ∉ D} * Fintype.card W +
        ∑ w : W, ∑ a ∈ A w, replacementDegreeLoss G D K a := by
  have hcost := hcompat.sum_mixed_budgets_le K F A
  rw [sum_mixed_budgets_eq_attachment_cost K F A] at hcost
  let L := ∑ w : W, ∑ a ∈ A w, replacementDegreeLoss G D K a
  have hold : (∑ w : W, d * (A w).card) ≤
      (∑ w : W, ∑ a ∈ A w, K.degree a) + L := by
    calc
      (∑ w : W, d * (A w).card) =
          ∑ w : W, ∑ _a ∈ A w, d := by
        apply Finset.sum_congr rfl
        intro w _
        simp [Nat.mul_comm]
      _ ≤ ∑ w : W, ∑ a ∈ A w,
          (K.degree a + replacementDegreeLoss G D K a) := by
        apply Finset.sum_le_sum
        intro w _
        exact Finset.sum_le_sum fun a _ => by
          rw [degree_add_replacementDegreeLoss G D K hKle a]
          exact hmin.trans (G.minDegree_le_degree a.1)
      _ = (∑ w : W, ∑ a ∈ A w, K.degree a) + L := by
        simp only [Finset.sum_add_distrib]
        rfl
  have hattach : (∑ w : W, (A w).card * (d + F.degree w)) ≤
      Fintype.card {v : V // v ∉ D} * Fintype.card W + L := by
    calc
      (∑ w : W, (A w).card * (d + F.degree w)) =
          (∑ w : W, d * (A w).card) +
            ∑ w : W, F.degree w * (A w).card := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w _
        rw [Nat.mul_add, Nat.mul_comm (A w).card d,
          Nat.mul_comm (A w).card (F.degree w)]
      _ ≤ ((∑ w : W, ∑ a ∈ A w, K.degree a) + L) +
          ∑ w : W, F.degree w * (A w).card :=
        Nat.add_le_add_right hold _
      _ = ((∑ w : W, ∑ a ∈ A w, K.degree a) +
          ∑ w : W, F.degree w * (A w).card) + L := by omega
      _ ≤ Fintype.card {v : V // v ∉ D} * Fintype.card W + L :=
        Nat.add_le_add_right hcost L
  apply le_trans (Finset.sum_le_sum fun w _ => ?_) hattach
  have hw := hnew w
  by_cases hr : F.degree w ≤ d
  · have hsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hr
    nlinarith
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hr)]

/-- Degree-square form for true replacement surgery. -/
theorem card_gadget_mul_degree_sq_le_survivor_mul_gadget_add_two_gadget_pred_add_replacementLoss
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d : ℕ}
    (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    Fintype.card W * (d * d) ≤
      Fintype.card {v : V // v ∉ D} * Fintype.card W +
        2 * (Fintype.card W * (Fintype.card W - 1)) +
          ∑ w : W, ∑ a ∈ A w, replacementDegreeLoss G D K a := by
  have hsum :=
    sum_sub_degree_mul_add_degree_le_survivor_mul_gadget_add_replacementLoss
      G D K hKle F A hmin hnew hcompat
  have hsq := sum_degree_sq_le_two_mul_card_mul_pred_of_not_containsC4
    F (hcompat.gadget_not_containsC4 K F A)
  have hidentity :
      (∑ w : W, (d - F.degree w) * (d + F.degree w)) +
          ∑ w : W, F.degree w * F.degree w =
        Fintype.card W * (d * d) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ w : W, ((d - F.degree w) * (d + F.degree w) +
          F.degree w * F.degree w)) = ∑ _w : W, d * d := by
        apply Finset.sum_congr rfl
        intro w _
        have hr : F.degree w ≤ d := by
          have hrlt := F.degree_lt_card_verts w
          omega
        have hsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hr
        nlinarith
      _ = Fintype.card W * (d * d) := by simp
  rw [← hidentity]
  omega

/-- **Moore-order replacement loss bound.**  Deleting `k` vertices and adding
a compatible `k+1` vertex gadget requires total attachment-weighted survivor
loss at least `(k+1)(d-1-k)`. -/
theorem card_succ_mul_degree_pred_sub_card_le_replacementLoss_of_mooreOrder
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d k : ℕ}
    (hd : 1 ≤ d) (hk : k ≤ d - 1)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hDcard : D.card = k) (hWcard : Fintype.card W = k + 1)
    (hmin : d ≤ G.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    (k + 1) * (d - 1 - k) ≤
      ∑ w : W, ∑ a ∈ A w, replacementDegreeLoss G D K a := by
  have hsize : Fintype.card W - 1 ≤ d := by omega
  have hbound :=
    card_gadget_mul_degree_sq_le_survivor_mul_gadget_add_two_gadget_pred_add_replacementLoss
      G D K hKle F A hsize hmin hnew hcompat
  have hUcard : Fintype.card {v : V // v ∉ D} =
      (d * (d - 1) + 1) - k := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ D)]
    simp [hcard, hDcard]
  rw [hUcard, hWcard] at hbound
  have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hksub : d - 1 - k + k = d - 1 := Nat.sub_add_cancel hk
  have hkbase : k ≤ d * (d - 1) + 1 := by nlinarith
  have hbasesub : d * (d - 1) + 1 - k + k = d * (d - 1) + 1 :=
    Nat.sub_add_cancel hkbase
  have hinner : d * d =
      (d * (d - 1) + 1 - k) + 2 * k + (d - 1 - k) := by
    nlinarith
  have heq : (k + 1) * (d * d) =
      (d * (d - 1) + 1 - k) * (k + 1) +
        2 * ((k + 1) * k) + (k + 1) * (d - 1 - k) := by
    rw [hinner, Nat.mul_add, Nat.mul_add]
    ring
  rw [heq] at hbound
  simp only [Nat.add_sub_cancel] at hbound
  omega

/-- At an original degree-`d` tight survivor, total replacement loss must be
repaid by selector multiplicity. -/
theorem replacementDegreeLoss_le_attachmentMultiplicity_of_tight
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (A : W → Finset {v : V // v ∉ D}) {d : ℕ}
    (v : {v : V // v ∉ D}) (htight : G.degree v.1 = d)
    (hfinal : d ≤ K.degree v + attachmentMultiplicity A v) :
    replacementDegreeLoss G D K v ≤ attachmentMultiplicity A v := by
  have hsplit := degree_add_replacementDegreeLoss G D K hKle v
  omega

/-- Total-loss cascade bound for true replacement surgery. -/
theorem card_tight_replacementLoss_ge_mul_choose_le_choose_card
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d q : ℕ}
    (hfinal : ∀ v : {v : V // v ∉ D},
      d ≤ K.degree v + attachmentMultiplicity A v)
    (hcompat : GadgetAttachmentCompatible K F A) :
    ((Finset.univ.filter fun v : {v : V // v ∉ D} =>
        G.degree v.1 = d ∧ q ≤ replacementDegreeLoss G D K v).card) *
        q.choose 2 ≤ (Fintype.card W).choose 2 := by
  classical
  let S := Finset.univ.filter fun v : {v : V // v ∉ D} =>
    G.degree v.1 = d ∧ q ≤ replacementDegreeLoss G D K v
  have hpair := hcompat.sum_choose_two_attachmentMultiplicity_le K F A
  calc
    S.card * q.choose 2 = ∑ _v ∈ S, q.choose 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ S, (attachmentMultiplicity A v).choose 2 := by
      apply Finset.sum_le_sum
      intro v hv
      have hvdata : G.degree v.1 = d ∧
          q ≤ replacementDegreeLoss G D K v := by
        simpa [S] using hv
      have hloss := replacementDegreeLoss_le_attachmentMultiplicity_of_tight
        G D K hKle A v hvdata.1 (hfinal v)
      exact Nat.choose_le_choose 2 (hvdata.2.trans hloss)
    _ ≤ ∑ v : {v : V // v ∉ D},
        (attachmentMultiplicity A v).choose 2 := by
      exact Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    _ ≤ (Fintype.card W).choose 2 := hpair

/-- In an original `d`-regular graph, the tightness clause is automatic. -/
theorem card_replacementLoss_ge_mul_choose_le_choose_card_of_regular
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D}) {d q : ℕ}
    (hreg : ∀ x : V, G.degree x = d)
    (hfinal : ∀ v : {v : V // v ∉ D},
      d ≤ K.degree v + attachmentMultiplicity A v)
    (hcompat : GadgetAttachmentCompatible K F A) :
    ((Finset.univ.filter fun v : {v : V // v ∉ D} =>
        q ≤ replacementDegreeLoss G D K v).card) * q.choose 2 ≤
      (Fintype.card W).choose 2 := by
  have h := card_tight_replacementLoss_ge_mul_choose_le_choose_card
    G D K hKle F A (d := d) (q := q) hfinal hcompat
  simpa [hreg] using h

end Erdos85

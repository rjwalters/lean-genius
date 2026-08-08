import Proofs.Erdos85DeleteGadget
import Proofs.Erdos85GadgetCounting

/-!
# Edge-compensated finite-gadget surgery

After deleting a vertex set, we may also replace the induced survivor graph
by any spanning subgraph before attaching a finite gadget.  This unifies the
cross-edge deletion method with arbitrary delete-set/add-gadget repair.
-/

open SimpleGraph

namespace Erdos85

/-- Degree lost when a spanning graph `H` is replaced by a subgraph `K`. -/
def subgraphDegreeLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (v : V) : ℕ := H.degree v - K.degree v

/-- The subgraph degree plus its exact loss is the original degree. -/
theorem degree_add_subgraphDegreeLoss
    {V : Type*} [Fintype V] [DecidableEq V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H) (v : V) :
    K.degree v + subgraphDegreeLoss H K v = H.degree v := by
  have hle : K.degree v ≤ H.degree v := K.degree_le_of_le hKH
  exact Nat.add_sub_of_le hle

/-- Exact degree decomposition after deleting a vertex set and then deleting
additional edges among the survivors. -/
theorem degree_subgraph_add_losses
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D) (v : {v : V // v ∉ D}) :
    K.degree v + subgraphDegreeLoss (deleteVertexSetGraph G D) K v +
        (G.neighborFinset v.1 ∩ D).card = G.degree v.1 := by
  have hedge := degree_add_subgraphDegreeLoss
    (deleteVertexSetGraph G D) K hKle v
  have hdelete := degree_deleteVertexSetGraph_add G D v
  omega

/-- Attach a gadget after replacing the survivor graph by an arbitrary graph
`K`.  Compatibility and the displayed final degrees are sufficient. -/
theorem c4FreeMinDegreeWitness_delete_set_add_gadget_of_survivorGraph
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (D : Finset V) (K : SimpleGraph {v : V // v ∉ D})
    [DecidableRel K.Adj]
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D})
    {N k m d : ℕ}
    (hVcard : Fintype.card V = N) (hDcard : D.card = k)
    (hWcard : Fintype.card W = m) (hfinal : 1 ≤ N - k + m)
    (hcompat : GadgetAttachmentCompatible K F A)
    (hcomp : ∀ v : {v : V // v ∉ D},
      d ≤ K.degree v +
        (Finset.univ.filter fun w => v ∈ A w).card)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    C4FreeMinDegreeWitness (N - k + m) d := by
  let P : SimpleGraph ({v : V // v ∉ D} ⊕ W) := attachGadget K F A
  have hHcard : Fintype.card {v : V // v ∉ D} = N - k := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ D)]
    simp [hVcard, hDcard]
  have hPcard : Fintype.card ({v : V // v ∉ D} ⊕ W) = N - k + m := by
    simp [hHcard, hWcard]
  letI : Nonempty ({v : V // v ∉ D} ⊕ W) :=
    Fintype.card_pos_iff.mp (hPcard.trans_gt hfinal)
  apply c4FreeMinDegreeWitness_of_card_eq P hPcard
  · apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro u
    rcases u with v | w
    · rw [show P.degree (.inl v) = K.degree v +
          (Finset.univ.filter fun w => v ∈ A w).card by
        exact attachGadget_degree_old K F A v]
      exact hcomp v
    · rw [show P.degree (.inr w) = (A w).card + F.degree w by
        exact attachGadget_degree_new K F A w]
      exact hnew w
  · exact (attachGadget_not_containsC4_iff_compatible K F A).2 hcompat

/-- **Edge-compensated delete-set/add-gadget surgery.**  Every survivor pays
for its deleted neighbors and for all additional incident edges removed from
the survivor graph, while gadget attachments credit one degree each. -/
theorem c4FreeMinDegreeWitness_delete_set_add_gadget_of_compensated_subgraph
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D})
    {N k m d : ℕ}
    (hVcard : Fintype.card V = N) (hDcard : D.card = k)
    (hWcard : Fintype.card W = m) (hfinal : 1 ≤ N - k + m)
    (hcompat : GadgetAttachmentCompatible K F A)
    (hcomp : ∀ v : {v : V // v ∉ D},
      d + (G.neighborFinset v.1 ∩ D).card +
          subgraphDegreeLoss (deleteVertexSetGraph G D) K v ≤
        G.degree v.1 + (Finset.univ.filter fun w => v ∈ A w).card)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    C4FreeMinDegreeWitness (N - k + m) d := by
  apply c4FreeMinDegreeWitness_delete_set_add_gadget_of_survivorGraph
    D K F A hVcard hDcard hWcard hfinal hcompat
  · intro v
    have hsplit := degree_subgraph_add_losses G D K hKle v
    have hv := hcomp v
    omega
  · exact hnew

/-- Order-raising specialization of the fully compensated surgery. -/
theorem c4FreeMinDegreeWitness_succ_of_delete_set_add_gadget_of_compensated_subgraph
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (K : SimpleGraph {v : V // v ∉ D}) [DecidableRel K.Adj]
    (hKle : K ≤ deleteVertexSetGraph G D)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset {v : V // v ∉ D})
    {N k d : ℕ}
    (hVcard : Fintype.card V = N) (hDcard : D.card = k)
    (hWcard : Fintype.card W = k + 1)
    (hcompat : GadgetAttachmentCompatible K F A)
    (hcomp : ∀ v : {v : V // v ∉ D},
      d + (G.neighborFinset v.1 ∩ D).card +
          subgraphDegreeLoss (deleteVertexSetGraph G D) K v ≤
        G.degree v.1 + (Finset.univ.filter fun w => v ∈ A w).card)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w) :
    C4FreeMinDegreeWitness (N + 1) d := by
  have hk : k ≤ N := by
    rw [← hDcard, ← hVcard]
    exact Finset.card_le_univ D
  have hw :=
    c4FreeMinDegreeWitness_delete_set_add_gadget_of_compensated_subgraph
      G D K hKle F A hVcard hDcard hWcard (by omega)
        hcompat hcomp hnew
  have heq : N - k + (k + 1) = N + 1 := by omega
  rw [← heq]
  exact hw

/-- A uniform compensated delete/subgraph/gadget construction for every
witness implies one-step witness extension.  This is the broadest finite
surgery criterion in the development: it allows structured vertex deletion,
old-edge deletion, and an arbitrary `k+1` vertex replacement gadget. -/
theorem witnessExtension_of_compensated_delete_set_add_gadget {n k : ℕ}
    (hsurgery : ∀ d (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      d ≤ G.minDegree → ¬ containsC4 (Fin n) G →
      ∃ D : Finset (Fin n), D.card = k ∧
      ∃ K : SimpleGraph {v : Fin n // v ∉ D},
        letI : DecidableRel K.Adj := Classical.decRel K.Adj
        K ≤ deleteVertexSetGraph G D ∧
        ∃ F : SimpleGraph (Fin (k + 1)),
          letI : DecidableRel F.Adj := Classical.decRel F.Adj
          ∃ A : Fin (k + 1) → Finset {v : Fin n // v ∉ D},
            GadgetAttachmentCompatible K F A ∧
            (∀ v : {v : Fin n // v ∉ D},
              d + (G.neighborFinset v.1 ∩ D).card +
                  subgraphDegreeLoss (deleteVertexSetGraph G D) K v ≤
                G.degree v.1 +
                  (Finset.univ.filter fun w => v ∈ A w).card) ∧
            (∀ w : Fin (k + 1), d ≤ (A w).card + F.degree w)) :
    C4FreeWitnessExtension n := by
  rintro d ⟨G, hdec, hmin, hfree⟩
  letI : DecidableRel G.Adj := hdec
  obtain ⟨D, hDcard, K, hKdata⟩ := hsurgery d G hdec hmin hfree
  letI : DecidableRel K.Adj := Classical.decRel K.Adj
  obtain ⟨hKle, F, hFdata⟩ := hKdata
  letI : DecidableRel F.Adj := Classical.decRel F.Adj
  obtain ⟨A, hcompat, hcomp, hnew⟩ := hFdata
  exact
    c4FreeMinDegreeWitness_succ_of_delete_set_add_gadget_of_compensated_subgraph
      G D K hKle F A (by simp) hDcard (by simp) hcompat hcomp hnew

/-- **Loss-corrected global gadget obstruction.**  Replacing `H` by a
spanning subgraph `K` can beat the pure attachment bound only by paying
attachment-weighted degree loss.  Each removed edge incident to a vertex is
counted once for every gadget selector containing that vertex. -/
theorem sum_sub_degree_mul_add_degree_le_card_mul_card_add_weightedLoss
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hmin : d ≤ H.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    (∑ w : W, (d - F.degree w) * (d + F.degree w)) ≤
      Fintype.card V * Fintype.card W +
        ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a := by
  have hcost := hcompat.sum_mixed_budgets_le K F A
  rw [sum_mixed_budgets_eq_attachment_cost K F A] at hcost
  let L := ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a
  have hold : (∑ w : W, d * (A w).card) ≤
      (∑ w : W, ∑ a ∈ A w, K.degree a) + L := by
    calc
      (∑ w : W, d * (A w).card) =
          ∑ w : W, ∑ _a ∈ A w, d := by
        apply Finset.sum_congr rfl
        intro w _
        simp [Nat.mul_comm]
      _ ≤ ∑ w : W, ∑ a ∈ A w,
          (K.degree a + subgraphDegreeLoss H K a) := by
        apply Finset.sum_le_sum
        intro w _
        exact Finset.sum_le_sum fun a _ => by
          rw [degree_add_subgraphDegreeLoss H K hKH a]
          exact hmin.trans (H.minDegree_le_degree a)
      _ = (∑ w : W, ∑ a ∈ A w, K.degree a) + L := by
        simp only [Finset.sum_add_distrib]
        rfl
  have hattach : (∑ w : W, (A w).card * (d + F.degree w)) ≤
      Fintype.card V * Fintype.card W + L := by
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
      _ ≤ Fintype.card V * Fintype.card W + L :=
        Nat.add_le_add_right hcost L
  apply le_trans (Finset.sum_le_sum fun w _ => ?_) hattach
  have hw := hnew w
  by_cases hr : F.degree w ≤ d
  · have hsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hr
    nlinarith
  · simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hr)]

/-- Universal size form with edge-loss correction.  If `m-1 ≤ d`, then
`m(d²-(m-1)²) ≤ |V|m + L`, where `L` is the attachment-weighted old
degree loss. -/
theorem card_mul_degree_sq_sub_card_pred_sq_le_card_mul_card_add_weightedLoss
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ}
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hmin : d ≤ H.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    Fintype.card W *
        (d * d - (Fintype.card W - 1) * (Fintype.card W - 1)) ≤
      Fintype.card V * Fintype.card W +
        ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a := by
  let s := Fintype.card W - 1
  let B := d * d - s * s
  have hsum :=
    sum_sub_degree_mul_add_degree_le_card_mul_card_add_weightedLoss
      H K hKH F A hmin hnew hcompat
  have heq : (d - s) * (d + s) = B := by
    dsimp [B]
    rw [Nat.sub_mul]
    have hpoly : d * (d + s) = d * d + d * s := by ring
    have hpoly' : s * (d + s) = d * s + s * s := by ring
    rw [hpoly, hpoly']
    omega
  have hlower : (∑ _w : W, B) ≤
      ∑ w : W, (d - F.degree w) * (d + F.degree w) := by
    apply Finset.sum_le_sum
    intro w _
    have hrs : F.degree w ≤ s := by
      have := F.degree_lt_card_verts w
      dsimp [s]
      omega
    have hrle : F.degree w ≤ d := hrs.trans hsize
    have hdsub : d - F.degree w + F.degree w = d := Nat.sub_add_cancel hrle
    have hssub : d - s + s = d := Nat.sub_add_cancel hsize
    rw [← heq]
    nlinarith
  apply le_trans ?_ hsum
  simpa [B, s, Nat.mul_comm] using hlower

/-- At Moore-layer order, every unit by which gadget size misses the pure
attachment threshold must be paid once per gadget vertex in
attachment-weighted old-edge loss. -/
theorem card_mul_degree_pred_sub_card_pred_sq_le_weightedLoss_of_mooreOrder
    {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hKH : K ≤ H)
    (F : SimpleGraph W) [DecidableRel F.Adj]
    (A : W → Finset V) {d : ℕ} (hd : 1 ≤ d)
    (hcard : Fintype.card V = d * (d - 1) + 1)
    (hW : 0 < Fintype.card W) (hsize : Fintype.card W - 1 ≤ d)
    (hsq : (Fintype.card W - 1) * (Fintype.card W - 1) ≤ d - 1)
    (hmin : d ≤ H.minDegree)
    (hnew : ∀ w : W, d ≤ (A w).card + F.degree w)
    (hcompat : GadgetAttachmentCompatible K F A) :
    Fintype.card W *
        (d - 1 - (Fintype.card W - 1) * (Fintype.card W - 1)) ≤
      ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a := by
  let m := Fintype.card W
  let s := m - 1
  let t := d - 1 - s * s
  let L := ∑ w : W, ∑ a ∈ A w, subgraphDegreeLoss H K a
  have hbound :=
    card_mul_degree_sq_sub_card_pred_sq_le_card_mul_card_add_weightedLoss
      H K hKH F A hW hsize hmin hnew hcompat
  change m * (d * d - s * s) ≤ Fintype.card V * m + L at hbound
  have hdsub : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have htsub : t + s * s = d - 1 := by
    dsimp [t]
    exact Nat.sub_add_cancel hsq
  have hsqdd : s * s ≤ d * d := by nlinarith
  have hleft : d * d - s * s + s * s = d * d := Nat.sub_add_cancel hsqdd
  have hinner : d * d - s * s = (d * (d - 1) + 1) + t := by
    nlinarith
  have heq : m * (d * d - s * s) = Fintype.card V * m + m * t := by
    rw [hinner, Nat.mul_add, hcard]
    rw [Nat.mul_comm m (d * (d - 1) + 1)]
  rw [heq] at hbound
  change m * t ≤ L
  omega

end Erdos85

import Proofs.Erdos85OrderFortyNineBitRelabel

/-!
# Relabeling invariance of the order-49 Boolean terminal

The `t = 0` normalization constructs a permutation of the 42 low vertices.
This file isolates the generic fact that the relation-level SAT terminal is
unchanged by any permutation which fixes the high prefix and preserves the
prescribed support mask of every vertex.
-/

namespace Erdos85

theorem univ_filter_card_comp_equiv {α : Type*} [Fintype α] [DecidableEq α]
    (e : α ≃ α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x => p (e x)).card =
      (Finset.univ.filter p).card := by
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx
    simpa using (Finset.mem_filter.mp hx).2
  · intro x₁ hx₁ x₂ hx₂ he
    exact e.injective he
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    simpa using (Finset.mem_filter.mp hy).2

/-- Relabeling invariance for the complete relation-level terminal.  The
equivalence may permute low vertices freely inside their prescribed support
fibers; fixing the high prefix ensures that the distinguished support columns
continue to name the same high vertices. -/
theorem orderFortyNineRelationConstraints_relabel
    (h : Nat) (masks : Array Nat) (adj : Fin 49 → Fin 49 → Bool)
    (e : Fin 49 ≃ Fin 49)
    (hconstraints : orderFortyNineRelationConstraints h masks adj)
    (hfix : ∀ w : Fin 9, w.val < h →
      e ⟨w.val, by omega⟩ = ⟨w.val, by omega⟩)
    (hprefix : ∀ i : Fin 49, (e i).val < h ↔ i.val < h)
    (hmask : ∀ i : Fin 49,
      orderFortyNineSupportMask masks (e i) =
        orderFortyNineSupportMask masks i) :
    orderFortyNineRelationConstraints h masks
      (fun i j => adj (e i) (e j)) := by
  rcases hconstraints with ⟨hsize, hh, hdegree, hc4, hsupport, hpartition⟩
  refine ⟨hsize, hh, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [univ_filter_card_comp_equiv e
      (fun j => adj (e i) j), hdegree (e i)]
    split <;> rename_i hi
    · rw [if_pos ((hprefix i).mp hi)]
    · rw [if_neg (fun hi' => hi ((hprefix i).mpr hi'))]
  · intro i j hij
    rw [univ_filter_card_comp_equiv e
      (fun k => adj (e i) k && adj (e j) k)]
    exact hc4 (e i) (e j) (fun heq => hij (e.injective heq))
  · intro i w hw
    change adj (e i) (e ⟨w.val, by omega⟩) = _
    rw [hfix w hw]
    exact (hsupport (e i) w hw).trans (congrArg (fun mask => mask.getLsbD w.val)
      (hmask i))
  · intro i hi w hw
    change (Finset.univ.filter fun k =>
      adj (e i) (e k) &&
        (orderFortyNineSupportMask masks k).getLsbD w.val).card = 1
    have hcard := univ_filter_card_comp_equiv e (fun k =>
      adj (e i) k &&
        (orderFortyNineSupportMask masks (e.symm k)).getLsbD w.val)
    simp only [e.symm_apply_apply] at hcard
    rw [hcard]
    have hei : h ≤ (e i).val :=
      Nat.le_of_not_gt (fun hei =>
        (Nat.not_lt_of_ge hi) ((hprefix i).mp hei))
    have hp := hpartition (e i) hei w hw
    have hsets :
        (Finset.univ.filter fun k =>
          adj (e i) k &&
            (orderFortyNineSupportMask masks (e.symm k)).getLsbD w.val) =
        (Finset.univ.filter fun k =>
          adj (e i) k &&
            (orderFortyNineSupportMask masks k).getLsbD w.val) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← hmask (e.symm k), e.apply_symm_apply]
    rw [hsets]
    exact hp

/-- Bit-vector form of `orderFortyNineRelationConstraints_relabel`.  This is
the adapter used by normalization: the constructed target-to-source vertex
equivalence is turned into an actual 1176-bit edge vector, while all Boolean
terminal constraints are transported automatically. -/
theorem orderFortyNineBooleanConstraints_relabel
    (h : Nat) (masks : Array Nat) (edges : BitVec 1176)
    (e : Fin 49 ≃ Fin 49)
    (hconstraints : orderFortyNineBooleanConstraints h masks edges)
    (hfix : ∀ w : Fin 9, w.val < h →
      e ⟨w.val, by omega⟩ = ⟨w.val, by omega⟩)
    (hprefix : ∀ i : Fin 49, (e i).val < h ↔ i.val < h)
    (hmask : ∀ i : Fin 49,
      orderFortyNineSupportMask masks (e i) =
        orderFortyNineSupportMask masks i) :
    orderFortyNineBooleanConstraints h masks
      (orderFortyNineRelabelEdges edges e) := by
  unfold orderFortyNineBooleanConstraints at hconstraints ⊢
  simpa only [orderFortyNineBitAdj_relabelEdges] using
    orderFortyNineRelationConstraints_relabel h masks
      (orderFortyNineBitAdj edges) e hconstraints hfix hprefix hmask

end Erdos85

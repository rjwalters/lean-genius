import Proofs.Erdos85OrderFortyNineBitRelabel
import Proofs.Erdos85OrderFortyNineSevenHighProfileMasks

/-!
# Relabeling tools for the order-49 Boolean terminal

The `t = 0` normalization constructs a permutation of the 42 low vertices.
Degree and common-neighbor constraints transport under every permutation;
partition constraints transport when the permutation identifies the target
block with the corresponding source support fiber.  A stronger terminal-wide
corollary is also recorded for genuinely mask-preserving permutations (the
cube normalization itself deliberately is not mask-preserving).
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

theorem orderFortyNineDegreeConstraints_relabel
    (adj : Fin 49 → Fin 49 → Bool) (e : Fin 49 ≃ Fin 49)
    (hdegree : ∀ i : Fin 49,
      (Finset.univ.filter fun j => adj i j).card =
        if i.val < 7 then 8 else 7)
    (hprefix : ∀ i : Fin 49, (e i).val < 7 ↔ i.val < 7) :
    ∀ i : Fin 49,
      (Finset.univ.filter fun j => adj (e i) (e j)).card =
        if i.val < 7 then 8 else 7 := by
  intro i
  rw [univ_filter_card_comp_equiv e (fun j => adj (e i) j), hdegree (e i)]
  split <;> rename_i hi
  · rw [if_pos ((hprefix i).mp hi)]
  · rw [if_neg (fun hi' => hi ((hprefix i).mpr hi'))]

theorem orderFortyNineC4Constraints_relabel
    (adj : Fin 49 → Fin 49 → Bool) (e : Fin 49 ≃ Fin 49)
    (hc4 : ∀ i j : Fin 49, i ≠ j →
      (Finset.univ.filter fun k => adj i k && adj j k).card ≤ 1) :
    ∀ i j : Fin 49, i ≠ j →
      (Finset.univ.filter fun k =>
        adj (e i) (e k) && adj (e j) (e k)).card ≤ 1 := by
  intro i j hij
  rw [univ_filter_card_comp_equiv e
    (fun k => adj (e i) k && adj (e j) k)]
  exact hc4 (e i) (e j) (fun heq => hij (e.injective heq))

theorem orderFortyNineHighIndependent_relabel
    (adj : Fin 49 → Fin 49 → Bool) (e : Fin 49 ≃ Fin 49)
    (hfix : ∀ i : Fin 49, i.val < 7 → e i = i)
    (hind : ∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
      adj i j = false) :
    ∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
      adj (e i) (e j) = false := by
  intro i j hi hj hij
  simpa [hfix i hi, hfix j hj] using hind i j hi hj hij

theorem orderFortyNineHighCommonWitness_relabel
    (adj : Fin 49 → Fin 49 → Bool) (e : Fin 49 ≃ Fin 49)
    (hfix : ∀ i : Fin 49, i.val < 7 → e i = i)
    (hprefix : ∀ i : Fin 49, (e i).val < 7 ↔ i.val < 7)
    (hcommon : ∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
      ∃ w : Fin 49, 7 ≤ w.val ∧ adj i w = true ∧ adj j w = true) :
    ∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
      ∃ w : Fin 49, 7 ≤ w.val ∧
        adj (e i) (e w) = true ∧ adj (e j) (e w) = true := by
  intro i j hi hj hij
  obtain ⟨w, hw, hiw, hjw⟩ := hcommon i j hi hj hij
  refine ⟨e.symm w, ?_, ?_, ?_⟩
  · have hw' : ¬w.val < 7 := Nat.not_lt_of_ge hw
    have := (hprefix (e.symm w)).not.mp (by simpa using hw')
    omega
  · simpa [hfix i hi] using hiw
  · simpa [hfix j hj] using hjw

/-- Transport one named high-support column to a normalized target block. -/
theorem orderFortyNineSupportColumn_relabel
    (adj : Fin 49 → Fin 49 → Bool) (e : Fin 49 ≃ Fin 49)
    (high : Fin 49) (source target : Finset (Fin 49))
    (hsymm : ∀ i j, adj i j = adj j i)
    (hfix : e high = high)
    (hsource : ∀ y : Fin 49, adj y high = decide (y ∈ source))
    (hblock : ∀ y : Fin 49, y ∈ target ↔ e y ∈ source) :
    ∀ y : Fin 49, adj (e high) (e y) = decide (y ∈ target) := by
  intro y
  rw [hfix, hsymm, hsource]
  by_cases hy : y ∈ target
  · simp [hy, (hblock y).mp hy]
  · have hey : e y ∉ source := fun hey => hy ((hblock y).mpr hey)
    simp [hy, hey]

set_option maxRecDepth 100000 in
theorem sevenHighT0Masks_pairWitness :
    ∀ i j : Fin 7, i ≠ j →
      ∃ w : Fin 49, 7 ≤ w.val ∧
        (orderFortyNineSupportMask
          (OrderFortyNineSevenHighCensus.representativeMasks 0 0) w).getLsbD
            i.val = true ∧
        (orderFortyNineSupportMask
          (OrderFortyNineSevenHighCensus.representativeMasks 0 0) w).getLsbD
            j.val = true := by
  native_decide

/-- Every pair of canonical high vertices has its prescribed pair-support
low vertex.  This supplies the positive common clause after relabeling. -/
theorem sevenHighT0_source_high_commonWitness
    (edges : BitVec 1176)
    (h : orderFortyNineBooleanConstraints 7
      (OrderFortyNineSevenHighCensus.representativeMasks 0 0) edges) :
    ∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
      ∃ w : Fin 49, 7 ≤ w.val ∧
        orderFortyNineBitAdj edges i w = true ∧
        orderFortyNineBitAdj edges j w = true := by
  rcases h with ⟨_, _, _, _, hsupport, _⟩
  intro i j hi hj hij
  let i7 : Fin 7 := ⟨i.val, hi⟩
  let j7 : Fin 7 := ⟨j.val, hj⟩
  have hij7 : i7 ≠ j7 := by
    intro heq
    apply hij
    have hv : i7.val = j7.val :=
      congrArg (fun z : Fin 7 => z.val) heq
    apply Fin.ext
    exact hv
  obtain ⟨w, hw, hwi, hwj⟩ :=
    sevenHighT0Masks_pairWitness i7 j7 hij7
  refine ⟨w, hw, ?_, ?_⟩
  · rw [orderFortyNineBitAdj_comm]
    exact (hsupport w ⟨i.val, by omega⟩ hi).trans hwi
  · rw [orderFortyNineBitAdj_comm]
    exact (hsupport w ⟨j.val, by omega⟩ hj).trans hwj

/-- Transport an exact-one neighbor law from a source support fiber to its
normalized target block.  Unlike terminal-wide invariance, this is precisely
the form needed when normalization deliberately changes the mask layout. -/
theorem orderFortyNinePartitionConstraint_relabel
    (adj : Fin 49 → Fin 49 → Bool) (e : Fin 49 ≃ Fin 49)
    (i : Fin 49) (source target : Finset (Fin 49))
    (hblock : ∀ k : Fin 49, k ∈ target ↔ e k ∈ source)
    (hsource : (Finset.univ.filter fun k =>
      adj (e i) k && decide (k ∈ source)).card = 1) :
    (Finset.univ.filter fun k =>
      adj (e i) (e k) && decide (k ∈ target)).card = 1 := by
  have hcard := univ_filter_card_comp_equiv e (fun k =>
    adj (e i) k && decide (k ∈ source))
  have htarget :
      (Finset.univ.filter fun k =>
        adj (e i) (e k) && decide (k ∈ target)) =
      (Finset.univ.filter fun k =>
        adj (e i) (e k) && decide (e k ∈ source)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact and_congr Iff.rfl (hblock k)
  rw [htarget, hcard]
  exact hsource

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

/- Bit-vector form of `orderFortyNineRelationConstraints_relabel`.  This is
the adapter used by normalization: the constructed target-to-source vertex
equivalence is turned into an actual 1176-bit edge vector, while all Boolean
terminal constraints are transported automatically. -/
set_option maxRecDepth 100000 in
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
  have hadj : orderFortyNineBitAdj (orderFortyNineRelabelEdges edges e) =
      fun i j => orderFortyNineBitAdj edges (e i) (e j) := by
    funext i j
    exact orderFortyNineBitAdj_relabelEdges edges e i j
  rw [hadj]
  exact orderFortyNineRelationConstraints_relabel h masks
    (orderFortyNineBitAdj edges) e hconstraints hfix hprefix hmask

end Erdos85

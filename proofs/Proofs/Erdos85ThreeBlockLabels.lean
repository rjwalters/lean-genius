import Mathlib

/-! Three disjoint labeled blocks give labels on their entire union. -/
namespace Erdos85
noncomputable section

theorem three_disjoint_block_labels
    {V : Type*} [DecidableEq V] (A B C U : Finset V)
    (hU : U = A ∪ B ∪ C) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (l0 : Fin 5 ≃ (↑A : Set V)) (l1 : Fin 5 ≃ (↑B : Set V)) (l2 : Fin 5 ≃ (↑C : Set V)) :
    ∃ e : (Fin 3 × Fin 5) ≃ (↑U : Set V),
      (∀ i, (e (0,i)).val = (l0 i).val) ∧
      (∀ i, (e (1,i)).val = (l1 i).val) ∧
      (∀ i, (e (2,i)).val = (l2 i).val) := by
  classical
  let f : Fin 3 × Fin 5 → V := fun p =>
    if p.1 = 0 then (l0 p.2).val else if p.1 = 1 then (l1 p.2).val else (l2 p.2).val
  have hf0 (i : Fin 5) : f (0,i) = (l0 i).val := by simp [f]
  have hf1 (i : Fin 5) : f (1,i) = (l1 i).val := by simp [f]
  have hf2 (i : Fin 5) : f (2,i) = (l2 i).val := by simp [f]
  have hmem (p : Fin 3 × Fin 5) : f p ∈ U := by
    rcases p with ⟨k,i⟩
    rw [hU]
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk with rfl | rfl | rfl
    · rw [hf0]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (l0 i).property)
    · rw [hf1]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (l1 i).property)
    · rw [hf2]
      exact Finset.mem_union_right _ (l2 i).property
  have hab (i j : Fin 5) : (l0 i).val ≠ (l1 j).val := by
    intro h
    exact Finset.disjoint_left.mp hAB (l0 i).property (h.symm ▸ (l1 j).property)
  have hac (i j : Fin 5) : (l0 i).val ≠ (l2 j).val := by
    intro h
    exact Finset.disjoint_left.mp hAC (l0 i).property (h.symm ▸ (l2 j).property)
  have hbc (i j : Fin 5) : (l1 i).val ≠ (l2 j).val := by
    intro h
    exact Finset.disjoint_left.mp hBC (l1 i).property (h.symm ▸ (l2 j).property)
  have hinj : Function.Injective f := by
    rintro ⟨k,i⟩ ⟨l,j⟩ h
    have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    have hl : l = 0 ∨ l = 1 ∨ l = 2 := by omega
    rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl
    · rw [hf0,hf0] at h
      exact Prod.ext rfl (l0.injective (Subtype.ext h))
    · rw [hf0,hf1] at h
      exact (hab i j h).elim
    · rw [hf0,hf2] at h
      exact (hac i j h).elim
    · rw [hf1,hf0] at h
      exact (hab j i h.symm).elim
    · rw [hf1,hf1] at h
      exact Prod.ext rfl (l1.injective (Subtype.ext h))
    · rw [hf1,hf2] at h
      exact (hbc i j h).elim
    · rw [hf2,hf0] at h
      exact (hac j i h.symm).elim
    · rw [hf2,hf1] at h
      exact (hbc j i h.symm).elim
    · rw [hf2,hf2] at h
      exact Prod.ext rfl (l2.injective (Subtype.ext h))
  let g : (Fin 3 × Fin 5) → (↑U : Set V) := fun p => ⟨f p,hmem p⟩
  have hginj : Function.Injective g := by
    intro p q h
    exact hinj (congrArg Subtype.val h)
  have hgsurj : Function.Surjective g := by
    intro x
    have hx : x.val ∈ A ∪ B ∪ C := by simpa only [hU, Finset.mem_coe] using x.property
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · refine ⟨(0,l0.symm ⟨x.val,hx⟩),?_⟩
        apply Subtype.ext
        change f (0,l0.symm ⟨x.val,hx⟩) = x.val
        rw [hf0,l0.apply_symm_apply]
      · refine ⟨(1,l1.symm ⟨x.val,hx⟩),?_⟩
        apply Subtype.ext
        change f (1,l1.symm ⟨x.val,hx⟩) = x.val
        rw [hf1,l1.apply_symm_apply]
    · refine ⟨(2,l2.symm ⟨x.val,hx⟩),?_⟩
      apply Subtype.ext
      change f (2,l2.symm ⟨x.val,hx⟩) = x.val
      rw [hf2,l2.apply_symm_apply]
  refine ⟨Equiv.ofBijective g ⟨hginj,hgsurj⟩,?_,?_,?_⟩
  · exact hf0
  · exact hf1
  · exact hf2

end
end Erdos85
#print axioms Erdos85.three_disjoint_block_labels

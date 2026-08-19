import Proofs.Erdos85SizeTwoMuNegThreeEightEightNormalForm

/-! # Explicit phases for cyclic orientations on ZMod 8 -/

namespace Erdos85

/-- A forward cyclic recurrence on `ZMod 8` is translation by its value at
zero. -/
theorem zmodEight_forward_orientation_eq_phase_add
    (φ : ZMod 8 → ZMod 8)
    (hφ : ∀ i, φ (i + 1) = φ i + 1) :
    ∀ i, φ i = φ 0 + i := by
  have h1 : φ 1 = φ 0 + 1 := by simpa using hφ 0
  have h2 : φ 2 = φ 0 + 2 := by
    calc
      φ 2 = φ (1 + 1) := by norm_num
      _ = φ 1 + 1 := hφ 1
      _ = φ 0 + 2 := by rw [h1]; ring
  have h3 : φ 3 = φ 0 + 3 := by
    calc
      φ 3 = φ (2 + 1) := by norm_num
      _ = φ 2 + 1 := hφ 2
      _ = φ 0 + 3 := by rw [h2]; ring
  have h4 : φ 4 = φ 0 + 4 := by
    calc
      φ 4 = φ (3 + 1) := by norm_num
      _ = φ 3 + 1 := hφ 3
      _ = φ 0 + 4 := by rw [h3]; ring
  have h5 : φ 5 = φ 0 + 5 := by
    calc
      φ 5 = φ (4 + 1) := by norm_num
      _ = φ 4 + 1 := hφ 4
      _ = φ 0 + 5 := by rw [h4]; ring
  have h6 : φ 6 = φ 0 + 6 := by
    calc
      φ 6 = φ (5 + 1) := by norm_num
      _ = φ 5 + 1 := hφ 5
      _ = φ 0 + 6 := by rw [h5]; ring
  have h7 : φ 7 = φ 0 + 7 := by
    calc
      φ 7 = φ (6 + 1) := by norm_num
      _ = φ 6 + 1 := hφ 6
      _ = φ 0 + 7 := by rw [h6]; ring
  intro i
  fin_cases i
  · change φ 0 = φ 0 + 0
    exact (add_zero _).symm
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-- A reverse cyclic recurrence on `ZMod 8` is reflection about its value
at zero. -/
theorem zmodEight_reverse_orientation_eq_phase_sub
    (φ : ZMod 8 → ZMod 8)
    (hφ : ∀ i, φ (i + 1) = φ i - 1) :
    ∀ i, φ i = φ 0 - i := by
  have h1 : φ 1 = φ 0 - 1 := by simpa using hφ 0
  have h2 : φ 2 = φ 0 - 2 := by
    calc
      φ 2 = φ (1 + 1) := by norm_num
      _ = φ 1 - 1 := hφ 1
      _ = φ 0 - 2 := by rw [h1]; ring
  have h3 : φ 3 = φ 0 - 3 := by
    calc
      φ 3 = φ (2 + 1) := by norm_num
      _ = φ 2 - 1 := hφ 2
      _ = φ 0 - 3 := by rw [h2]; ring
  have h4 : φ 4 = φ 0 - 4 := by
    calc
      φ 4 = φ (3 + 1) := by norm_num
      _ = φ 3 - 1 := hφ 3
      _ = φ 0 - 4 := by rw [h3]; ring
  have h5 : φ 5 = φ 0 - 5 := by
    calc
      φ 5 = φ (4 + 1) := by norm_num
      _ = φ 4 - 1 := hφ 4
      _ = φ 0 - 5 := by rw [h4]; ring
  have h6 : φ 6 = φ 0 - 6 := by
    calc
      φ 6 = φ (5 + 1) := by norm_num
      _ = φ 5 - 1 := hφ 5
      _ = φ 0 - 6 := by rw [h5]; ring
  have h7 : φ 7 = φ 0 - 7 := by
    calc
      φ 7 = φ (6 + 1) := by norm_num
      _ = φ 6 - 1 := hφ 6
      _ = φ 0 - 7 := by rw [h6]; ring
  intro i
  fin_cases i
  · change φ 0 = φ 0 - 0
    exact (sub_zero _).symm
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

/-- The recurrence-valued normal form is exactly one of sixteen explicit
orientation/phase cases. -/
theorem zmodEight_cyclic_orientation_exists_explicit_phase
    (φ : ZMod 8 → ZMod 8)
    (hφ : (∀ i, φ (i + 1) = φ i + 1) ∨
      (∀ i, φ (i + 1) = φ i - 1)) :
    ∃ t : ZMod 8,
      (∀ i, φ i = t + i) ∨ (∀ i, φ i = t - i) := by
  refine ⟨φ 0, ?_⟩
  rcases hφ with hf | hr
  · exact Or.inl (zmodEight_forward_orientation_eq_phase_add φ hf)
  · exact Or.inr (zmodEight_reverse_orientation_eq_phase_sub φ hr)

end Erdos85

#print axioms Erdos85.zmodEight_forward_orientation_eq_phase_add
#print axioms Erdos85.zmodEight_reverse_orientation_eq_phase_sub
#print axioms Erdos85.zmodEight_cyclic_orientation_exists_explicit_phase

import Proofs.Erdos85SizeTwoMuNegThreeEightEightDiagonalSameShape
import Proofs.Erdos85EvenCycleOrientation

/-! # The cross same-sign matching in the `mu=-3`, `k=1` C8+C8 case -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- Masking a C8 intertwiner by equality of two alternating sign lines
preserves the cycle-intertwining recurrence. -/
theorem alternating_sameSign_mask_cycleIntertwine
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1))
    (hfflip : ∀ i, f (i + 1) = -f i)
    (hgflip : ∀ j, g (j + 1) = -g j) :
    let P : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ if f i = g j then M i j else 0
    ∀ i j,
      P (i - 1) j + P (i + 1) j = P i (j + 1) + P i (j - 1) := by
  dsimp only
  intro i j
  have hfplus : f (i + 1) = -f i := hfflip i
  have hfminus : f (i - 1) = -f i := by
    have h := hfflip (i - 1)
    have hi : (i - 1) + 1 = i := by ring
    rw [hi] at h
    omega
  have hgplus : g (j + 1) = -g j := hgflip j
  have hgminus : g (j - 1) = -g j := by
    have h := hgflip (j - 1)
    have hj : (j - 1) + 1 = j := by ring
    rw [hj] at h
    omega
  by_cases h : -f i = g j
  · have hLminus : f (i - 1) = g j := hfminus.trans h
    have hLplus : f (i + 1) = g j := hfplus.trans h
    have hRplus : f i = g (j + 1) := by rw [hgplus, ← h]; ring
    have hRminus : f i = g (j - 1) := by rw [hgminus, ← h]; ring
    simp only [if_pos hLminus, if_pos hLplus, if_pos hRplus, if_pos hRminus]
    exact hinter i j
  · have hLminus : f (i - 1) ≠ g j := by
      rw [hfminus]
      exact h
    have hLplus : f (i + 1) ≠ g j := by
      rw [hfplus]
      exact h
    have hRplus : f i ≠ g (j + 1) := by
      rw [hgplus]
      intro heq
      apply h
      linear_combination -heq
    have hRminus : f i ≠ g (j - 1) := by
      rw [hgminus]
      intro heq
      apply h
      linear_combination -heq
    simp [hLminus, hLplus, hRplus, hRminus]

/-- A binary C8 intertwiner with alternating row and column signs and one
same-sign entry in every row is an oriented perfect matching after masking. -/
theorem binary_C8Intertwiner_sameSign_rowOne_orientation
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1))
    (hbinary : ∀ i j, M i j = 0 ∨ M i j = 1)
    (hfflip : ∀ i, f (i + 1) = -f i)
    (hgflip : ∀ j, g (j + 1) = -g j)
    (hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f i = g j ∧ M i j = 1).card = 1) :
    ∃ φ : ZMod 8 → ZMod 8,
      (∀ i j, (f i = g j ∧ M i j = 1) ↔ j = φ i) ∧
      ((∀ i, φ (i + 1) = φ i + 1) ∨
        (∀ i, φ (i + 1) = φ i - 1)) := by
  classical
  let P : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ if f i = g j then M i j else 0
  have hinterP := alternating_sameSign_mask_cycleIntertwine
    M f g hinter hfflip hgflip
  have hbinaryP : ∀ i j, P i j = 0 ∨ P i j = 1 := by
    intro i j
    dsimp [P]
    split
    · exact hbinary i j
    · exact Or.inl rfl
  have hone : ∀ i j, P i j = 1 ↔ f i = g j ∧ M i j = 1 := by
    intro i j
    dsimp [P]
    by_cases hsign : f i = g j
    · simp [hsign]
    · simp [hsign]
  have hrow : ∀ i, ∑ j, P i j = 1 := by
    intro i
    calc
      ∑ j, P i j = ∑ j, if P i j = 1 then (1 : ℤ) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rcases hbinaryP i j with hz | ho
        · simp [hz]
        · simp [ho]
      _ = (((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          P i j = 1).card : ℤ) := by
        simpa only using (Finset.sum_boole (R := ℤ)
          (fun j : ZMod 8 ↦ P i j = 1) Finset.univ)
      _ = 1 := by
        rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            P i j = 1) = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            f i = g j ∧ M i j = 1) by
          ext j; simp [hone]]
        exact_mod_cast hdegree i
  obtain ⟨φ, hφ, horient⟩ := binary_rowOne_cycleIntertwiner_orientation
    (r := 8) (by omega) P hinterP hbinaryP hrow
  refine ⟨φ, ?_, horient⟩
  intro i j
  rw [← hφ i j, hone i j]

end

end Erdos85

#print axioms Erdos85.binary_C8Intertwiner_sameSign_rowOne_orientation

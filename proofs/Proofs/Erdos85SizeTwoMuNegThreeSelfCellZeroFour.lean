import Proofs.Erdos85ZModEightMixedSelfIntertwinerExclusion

/-!
# Killing the μ=-3 self-switch cell (k,r) = (0,4)

Node: outline F.3 (μ=-3 lane; recipe from squad msgs 13574/13575).

The `(0,4)` self cell is forced both-all-TF, so both `±1` diagonal
entries are triangle-free defect edges (present), the same-sign row is
empty (`k = 0`), and the row total is `7 - r = 3`.  Subtracting the
ambient cycle circulant — itself a C8 self-intertwiner — leaves a
binary symmetric row-one intertwiner supported on odd offsets away from
`±1`: an oriented odd matching avoiding the cycle, which is impossible
(`zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle`).
-/

open Finset

namespace Erdos85

/-- The ambient C8 cycle circulant on `ZMod 8`. -/
def zmodEightCycleMatrix : Matrix (ZMod 8) (ZMod 8) ℤ :=
  fun x y => if y - x = 1 ∨ y - x = 7 then 1 else 0

theorem zmodEightCycleMatrix_entry_intertwine (x y : ZMod 8) :
    zmodEightCycleMatrix (x - 1) y +
        zmodEightCycleMatrix (x + 1) y =
      zmodEightCycleMatrix x (y + 1) +
        zmodEightCycleMatrix x (y - 1) := by
  revert x y
  decide

theorem zmodEightCycleMatrix_row_sum (x : ZMod 8) :
    ∑ y, zmodEightCycleMatrix x y = 2 := by
  revert x
  decide

/-- **The `(k,r) = (0,4)` self-cell kernel.**  A binary symmetric loopless
C8 self-intertwiner with row sum `3`, no same-parity entries, and both
ambient cycle entries present is impossible. -/
theorem zmodEight_selfIntertwiner_oppositeOnly_rowThree_with_cycle_impossible
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hsymm : ∀ x y, H x y = H y x)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y = H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (hrow : ∀ x, ∑ y, H x y = 3)
    (heven0 : ∀ x y, ZModEightEvenOffset (y - x) → H x y = 0)
    (hcycle : ∀ x, H x (x - 1) = 1 ∧ H x (x + 1) = 1) : False := by
  classical
  let C := zmodEightCycleMatrix
  let P : Matrix (ZMod 8) (ZMod 8) ℤ := H - C
  have hCoff : ∀ x y : ZMod 8, ¬ (y - x = 1 ∨ y - x = 7) → C x y = 0 := by
    intro x y h
    simp [C, zmodEightCycleMatrix, h]
  have hHone : ∀ x y : ZMod 8, (y - x = 1 ∨ y - x = 7) → H x y = 1 := by
    intro x y h
    rcases h with h | h
    · have : y = x + 1 := by
        have := h
        linear_combination this
      rw [this]
      exact (hcycle x).2
    · have : y = x - 1 := by
        have h7 : y - x = -1 := by
          rw [h]
          decide
        linear_combination h7
      rw [this]
      exact (hcycle x).1
  have hinterP : ∀ x y,
      P (x - 1) y + P (x + 1) y = P x (y + 1) + P x (y - 1) := by
    intro x y
    have hH := hinter x y
    have hC := zmodEightCycleMatrix_entry_intertwine x y
    dsimp only [P, C]
    simp only [Matrix.sub_apply]
    linear_combination hH - hC
  have hbinaryP : ∀ x y, P x y = 0 ∨ P x y = 1 := by
    intro x y
    by_cases hc : y - x = 1 ∨ y - x = 7
    · left
      have hH := hHone x y hc
      simp [P, C, zmodEightCycleMatrix, hc, hH]
    · have hC := hCoff x y hc
      rcases hbinary x y with hH | hH
      · left
        simp [P, Matrix.sub_apply, hH, hC]
      · right
        simp [P, Matrix.sub_apply, hH, hC]
  have hrowP : ∀ x, ∑ y, P x y = 1 := by
    intro x
    calc
      ∑ y, P x y = (∑ y, H x y) - ∑ y, C x y := by
        simp only [P, Matrix.sub_apply, Finset.sum_sub_distrib]
      _ = 3 - 2 := by rw [hrow, zmodEightCycleMatrix_row_sum]
      _ = 1 := by norm_num
  obtain ⟨f, hf, horient⟩ :=
    binary_rowOne_cycleIntertwiner_orientation (r := 8) (by omega)
      P hinterP hbinaryP hrowP
  have hPf : ∀ x, P x (f x) = 1 := fun x ↦ (hf x (f x)).mpr rfl
  have hfOdd : ∀ x, ¬ ZModEightEvenOffset (f x - x) := by
    intro x he
    have hH : H x (f x) = 0 := heven0 x (f x) he
    have hC : C x (f x) = 0 := by
      apply hCoff
      rintro (h | h)
      · rw [h] at he
        exact absurd he (by decide)
      · rw [h] at he
        exact absurd he (by decide)
    have := hPf x
    simp [P, Matrix.sub_apply, hH, hC] at this
  have hfAvoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1 := by
    intro x
    constructor
    · intro h
      have hH : H x (f x) = 1 := by
        rw [h]
        exact (hcycle x).1
      have hC : C x (f x) = 1 := by
        rw [h]
        have h7 : x - 1 - x = (7 : ZMod 8) := by
          have hm : x - 1 - x = (-1 : ZMod 8) := by ring
          rw [hm]
          decide
        simp [C, zmodEightCycleMatrix, h7]
      have := hPf x
      simp [P, Matrix.sub_apply, hH, hC] at this
    · intro h
      have hH : H x (f x) = 1 := by
        rw [h]
        exact (hcycle x).2
      have hC : C x (f x) = 1 := by
        rw [h]
        have h1 : x + 1 - x = (1 : ZMod 8) := by ring
        simp [C, zmodEightCycleMatrix, h1]
      have := hPf x
      simp [P, Matrix.sub_apply, hH, hC] at this
  have hsymmP : ∀ x y, P x y = P y x := by
    intro x y
    have hC : C x y = C y x := by
      by_cases h : y - x = 1 ∨ y - x = 7
      · have h' : x - y = 1 ∨ x - y = 7 := by
          rcases h with h | h
          · right
            have hm : x - y = -1 := by linear_combination -h
            rw [hm]
            decide
          · left
            have hm : x - y = -7 := by linear_combination -h
            rw [hm]
            decide
        simp [C, zmodEightCycleMatrix, h, h']
      · have h' : ¬ (x - y = 1 ∨ x - y = 7) := by
          rintro (h1 | h7)
          · apply h
            right
            have hm : y - x = -1 := by linear_combination -h1
            rw [hm]
            decide
          · apply h
            left
            have hm : y - x = -7 := by linear_combination -h7
            rw [hm]
            decide
        simp [C, zmodEightCycleMatrix, h, h']
    simp only [P, Matrix.sub_apply, hsymm x y, hC]
  have hfInvol : ∀ x, f (f x) = x := by
    intro x
    have h1 : P (f x) x = 1 := by
      rw [hsymmP]
      exact hPf x
    exact ((hf (f x) x).mp h1).symm
  exact zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    f hfInvol hfOdd hfAvoid horient

end Erdos85

#print axioms Erdos85.zmodEight_selfIntertwiner_oppositeOnly_rowThree_with_cycle_impossible

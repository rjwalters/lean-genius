import Proofs.Erdos85MuNegThreeOneThreeShoreGeometry
import Proofs.Erdos85SizeTwoMuNegThreeSelfCellZeroFour

/-! # Algebraic commutation kill for the `mu=-3`, `(k,r)=(1,3)` endpoint -/

open Finset Matrix

namespace Erdos85

noncomputable section

def zmodEightAntipodeMatrix : Matrix (ZMod 8) (ZMod 8) ℤ :=
  fun i j ↦ if j - i = 4 then 1 else 0

theorem zmodEightAntipodeMatrix_symm (i j : ZMod 8) :
    zmodEightAntipodeMatrix i j = zmodEightAntipodeMatrix j i := by
  revert i j
  decide

theorem zmodEightAntipodeMatrix_entry_intertwine (i j : ZMod 8) :
    zmodEightAntipodeMatrix (i - 1) j +
      zmodEightAntipodeMatrix (i + 1) j =
    zmodEightAntipodeMatrix i (j + 1) +
      zmodEightAntipodeMatrix i (j - 1) := by
  revert i j
  decide

theorem zmodEightAntipodeMatrix_row_sum (i : ZMod 8) :
    ∑ j, zmodEightAntipodeMatrix i j = 1 := by
  revert i
  decide

/-- Removing the forced antipodal matching from h313 leaves precisely the
impossible opposite-sign row-three cycle intertwiner. -/
theorem MuNegThreeExplicitParameterLedger.oneThree_false_of_intertwine
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegThreeExplicitParameterLedger N M f g 1 3)
    (hshape : ZModEightSameSignShape N f 1)
    (hcycle : ∀ i, N i (i - 1) = 1 ∧ N i (i + 1) = 1)
    (hsymm : ∀ i j, N i j = N j i)
    (hinter : ∀ i j,
      N (i - 1) j + N (i + 1) j = N i (j + 1) + N i (j - 1))
    (hbinary : ∀ i j, N i j = 0 ∨ N i j = 1) : False := by
  classical
  let A := zmodEightAntipodeMatrix
  let P := N - A
  have honeShape : ∀ i j, f j = f i → (N i j = 1 ↔ j - i = 4) := by
    rcases hshape with hzero | hone | htwo
    · omega
    · exact hone.2
    · omega
  have hAone : ∀ i j, j - i = 4 → N i j = 1 := by
    intro i j hoff
    have heven : ZModEightEvenOffset (j - i) := by rw [hoff]; decide
    have hsame := (zmodEight_alternating_sign_eq_iff_evenOffset
      f L.f_sign L.f_flip i j).mpr heven
    exact (honeShape i j hsame).mpr hoff
  have hPinter : ∀ i j,
      P (i - 1) j + P (i + 1) j = P i (j + 1) + P i (j - 1) := by
    intro i j
    have hN := hinter i j
    have hA := zmodEightAntipodeMatrix_entry_intertwine i j
    dsimp only [P, A]
    simp only [Matrix.sub_apply]
    linear_combination hN - hA
  have hPsymm : ∀ i j, P i j = P j i := by
    intro i j
    dsimp only [P, A]
    simp only [Matrix.sub_apply, hsymm, zmodEightAntipodeMatrix_symm]
  have hPbinary : ∀ i j, P i j = 0 ∨ P i j = 1 := by
    intro i j
    by_cases hoff : j - i = 4
    · left
      simp [P, A, zmodEightAntipodeMatrix, hoff, hAone i j hoff]
    · have hAz : A i j = 0 := by simp [A, zmodEightAntipodeMatrix, hoff]
      rcases hbinary i j with hz | ho
      · left; simp [P, Matrix.sub_apply, hz, hAz]
      · right; simp [P, Matrix.sub_apply, ho, hAz]
  have hNrow : ∀ i, ∑ j, N i j = 4 := by
    intro i
    have hsum : ∑ j, N i j =
        (((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N i j = 1).card : ℤ) := by
      calc
        ∑ j, N i j = ∑ j, if N i j = 1 then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rcases hbinary i j with hz | ho
          · simp [hz]
          · simp [ho]
        _ = _ := by simpa using
          (Finset.sum_boole (R := ℤ) (fun j : ZMod 8 ↦ N i j = 1) Finset.univ)
    rw [hsum, L.internal_row]
    norm_num
  have hProw : ∀ i, ∑ j, P i j = 3 := by
    intro i
    calc
      ∑ j, P i j = (∑ j, N i j) - ∑ j, A i j := by
        simp [P, Matrix.sub_apply, Finset.sum_sub_distrib]
      _ = 4 - 1 := by rw [hNrow, zmodEightAntipodeMatrix_row_sum]
      _ = 3 := by norm_num
  have hPeven0 : ∀ i j, ZModEightEvenOffset (j - i) → P i j = 0 := by
    intro i j heven
    have hsame := (zmodEight_alternating_sign_eq_iff_evenOffset
      f L.f_sign L.f_flip i j).mpr heven
    by_cases hoff : j - i = 4
    · simp [P, A, zmodEightAntipodeMatrix, hoff, hAone i j hoff]
    · have hNne : N i j ≠ 1 := fun h ↦ hoff ((honeShape i j hsame).mp h)
      have hNz : N i j = 0 := (hbinary i j).resolve_right hNne
      simp [P, A, zmodEightAntipodeMatrix, hoff, hNz]
  have hPcycle : ∀ i, P i (i - 1) = 1 ∧ P i (i + 1) = 1 := by
    intro i
    rcases hcycle i with ⟨hm, hp⟩
    constructor
    · have hoff : (i - 1) - i ≠ (4 : ZMod 8) := by
        intro h
        have : ¬ ((-1 : ZMod 8) = 4) := by decide
        apply this
        linear_combination h
      have hA0 : A i (i - 1) = 0 := by
        simp only [A, zmodEightAntipodeMatrix, hoff, if_false]
      change N i (i - 1) - A i (i - 1) = 1
      rw [hm, hA0]
      norm_num
    · have hoff : (i + 1) - i ≠ (4 : ZMod 8) := by
        intro h
        have : ¬ ((1 : ZMod 8) = 4) := by decide
        apply this
        linear_combination h
      have hA0 : A i (i + 1) = 0 := by
        simp only [A, zmodEightAntipodeMatrix, hoff, if_false]
      change N i (i + 1) - A i (i + 1) = 1
      rw [hp, hA0]
      norm_num
  exact zmodEight_selfIntertwiner_oppositeOnly_rowThree_with_cycle_impossible
    P hPsymm hPinter hPbinary hProw hPeven0 hPcycle

end

end Erdos85

#print axioms Erdos85.MuNegThreeExplicitParameterLedger.oneThree_false_of_intertwine

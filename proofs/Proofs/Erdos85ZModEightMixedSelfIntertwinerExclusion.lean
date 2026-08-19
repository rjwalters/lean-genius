import Proofs.Erdos85ZModEightSameParitySingleIntertwiner

/-!
# Excluding a mixed-parity row-two self-intertwiner on C8

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The residual odd perfect matching left after removing a same-parity
half-turn cannot have either cyclic orientation: the forward orientation is
incompatible with symmetry, while every odd reverse matching contains a
cycle edge.
-/

namespace Erdos85

/-- A symmetric odd-parity perfect matching on `ZMod 8`, avoiding the two
cycle neighbors, cannot have either of the two cyclic orientations. -/
theorem zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    (f : ZMod 8 → ZMod 8)
    (hinvol : ∀ x, f (f x) = x)
    (hodd : ∀ x, ¬ ZModEightEvenOffset (f x - x))
    (havoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1)
    (horient : (∀ x, f (x + 1) = f x + 1) ∨
      (∀ x, f (x + 1) = f x - 1)) : False := by
  rcases horient with hfor | hrev
  · have hformula : ∀ y : ZMod 8, f y = f 0 + y := by
      intro y
      have hind : ∀ n : ℕ,
          f (n : ZMod 8) = f 0 + (n : ZMod 8) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Nat.cast_succ, hfor, ih]
            ring
      simpa only [ZMod.natCast_zmod_val] using hind y.val
    have hdouble : f 0 + f 0 = 0 := by
      have hi := hinvol 0
      rw [hformula] at hi
      simpa using hi
    have heven : ZModEightEvenOffset (f 0) := by
      have hfinite : ∀ z : ZMod 8,
          z + z = 0 → ZModEightEvenOffset z := by decide
      exact hfinite (f 0) hdouble
    exact (hodd 0) (by simpa using heven)
  · have hformula : ∀ y : ZMod 8, f y = f 0 - y := by
      intro y
      have hind : ∀ n : ℕ,
          f (n : ZMod 8) = f 0 - (n : ZMod 8) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
            rw [Nat.cast_succ, hrev, ih]
            ring
      simpa only [ZMod.natCast_zmod_val] using hind y.val
    have hf0odd : ¬ ZModEightEvenOffset (f 0) := by
      simpa using hodd 0
    have hex : ∃ x : ZMod 8, f 0 - x = x - 1 ∨ f 0 - x = x + 1 := by
      have hfinite : ∀ z : ZMod 8, ¬ ZModEightEvenOffset z →
          ∃ x : ZMod 8, z - x = x - 1 ∨ z - x = x + 1 := by decide
      exact hfinite (f 0) hf0odd
    obtain ⟨x, hx | hx⟩ := hex
    · exact (havoid x).1 (by rw [hformula]; exact hx)
    · exact (havoid x).2 (by rw [hformula]; exact hx)

/-- The forward half-turn matching on `ZMod 8`. -/
def zmodEightHalfTurnMatrix : Matrix (ZMod 8) (ZMod 8) ℤ :=
  fun x y => if y - x = 4 then 1 else 0

theorem zmodEightHalfTurnMatrix_entry_intertwine (x y : ZMod 8) :
    zmodEightHalfTurnMatrix (x - 1) y +
        zmodEightHalfTurnMatrix (x + 1) y =
      zmodEightHalfTurnMatrix x (y + 1) +
        zmodEightHalfTurnMatrix x (y - 1) := by
  revert x y
  decide

theorem zmodEightHalfTurnMatrix_row_sum (x : ZMod 8) :
    ∑ y, zmodEightHalfTurnMatrix x y = 1 := by
  revert x
  decide

/-- A row-two binary symmetric C8 self-intertwiner with exactly one
same-parity entry in every row cannot avoid the ambient cycle edges.  The
same-parity entry is forced to be the half-turn; subtracting it produces the
forbidden oriented odd matching above. -/
theorem zmodEight_selfIntertwiner_sameParity_degreeOne_impossible
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ x, H x x = 0)
    (hsymm : ∀ x y, H x y = H y x)
    (hinter : ∀ x y,
      H (x - 1) y + H (x + 1) y =
        H x (y + 1) + H x (y - 1))
    (hbinary : ∀ x y, H x y = 0 ∨ H x y = 1)
    (hrow : ∀ x, ∑ y, H x y = 2)
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧ H x y = 1).card = 1)
    (havoid : ∀ x, H x (x - 1) = 0 ∧ H x (x + 1) = 0) : False := by
  classical
  have heven := zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
    H hdiag hsymm hinter hdegree
  let M := zmodEightHalfTurnMatrix
  let P : Matrix (ZMod 8) (ZMod 8) ℤ := H - M
  have hinterP : ∀ x y,
      P (x - 1) y + P (x + 1) y =
        P x (y + 1) + P x (y - 1) := by
    intro x y
    have hH := hinter x y
    have hM := zmodEightHalfTurnMatrix_entry_intertwine x y
    dsimp only [P, M]
    simp only [Matrix.sub_apply]
    linear_combination hH - hM
  have hbinaryP : ∀ x y, P x y = 0 ∨ P x y = 1 := by
    intro x y
    by_cases h4 : y - x = 4
    · have he : ZModEightEvenOffset (y - x) := by
        rw [h4]
        exact Or.inr (Or.inr (Or.inl rfl))
      have hH : H x y = 1 := (heven x y he).2 h4
      left
      simp [P, M, zmodEightHalfTurnMatrix, h4, hH]
    · have hM : M x y = 0 := by
        simp [M, zmodEightHalfTurnMatrix, h4]
      rcases hbinary x y with hH | hH
      · left
        simp [P, hM, hH]
      · right
        simp [P, hM, hH]
  have hrowP : ∀ x, ∑ y, P x y = 1 := by
    intro x
    calc
      ∑ y, P x y = (∑ y, H x y) - ∑ y, M x y := by
        simp only [P, Matrix.sub_apply, Finset.sum_sub_distrib]
      _ = 2 - 1 := by rw [hrow, zmodEightHalfTurnMatrix_row_sum]
      _ = 1 := by norm_num
  obtain ⟨f, hf, horient⟩ :=
    binary_rowOne_cycleIntertwiner_orientation (r := 8) (by omega)
      P hinterP hbinaryP hrowP
  have hP_one_iff_oddH (x y : ZMod 8)
      (ho : ¬ ZModEightEvenOffset (y - x)) :
      P x y = 1 ↔ H x y = 1 := by
    have h4 : y - x ≠ 4 := by
      intro h
      apply ho
      rw [h]
      exact Or.inr (Or.inr (Or.inl rfl))
    simp [P, M, zmodEightHalfTurnMatrix, h4]
  have hfOdd : ∀ x, ¬ ZModEightEvenOffset (f x - x) := by
    intro x he
    have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
    have h4 := heven x (f x) he
    by_cases hoff : f x - x = 4
    · have hH := h4.mpr hoff
      simp [P, M, zmodEightHalfTurnMatrix, hoff, hH] at hP
    · have hH : H x (f x) = 0 := by
        rcases hbinary x (f x) with hz | ho
        · exact hz
        · exact (hoff (h4.mp ho)).elim
      simp [P, M, zmodEightHalfTurnMatrix, hoff, hH] at hP
  have hfAvoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1 := by
    intro x
    constructor
    · intro h
      have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
      have ho : ¬ ZModEightEvenOffset (f x - x) := hfOdd x
      have hH : H x (f x) = 1 := (hP_one_iff_oddH x (f x) ho).mp hP
      rw [h, (havoid x).1] at hH
      norm_num at hH
    · intro h
      have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
      have ho : ¬ ZModEightEvenOffset (f x - x) := hfOdd x
      have hH : H x (f x) = 1 := (hP_one_iff_oddH x (f x) ho).mp hP
      rw [h, (havoid x).2] at hH
      norm_num at hH
  have hfInvol : ∀ x, f (f x) = x := by
    intro x
    have hP : P x (f x) = 1 := (hf x (f x)).2 rfl
    have ho : ¬ ZModEightEvenOffset (f x - x) := hfOdd x
    have hH : H x (f x) = 1 := (hP_one_iff_oddH x (f x) ho).mp hP
    have horev : ¬ ZModEightEvenOffset (x - f x) := by
      intro he
      apply ho
      rcases he with h0 | h2 | h4 | h6
      · left
        linear_combination -h0
      · right; right; right
        have : f x - x = -2 := by linear_combination -h2
        exact this.trans (by decide)
      · right; right; left
        have : f x - x = -4 := by linear_combination -h4
        exact this.trans (by decide)
      · right; left
        have : f x - x = -6 := by linear_combination -h6
        exact this.trans (by decide)
    have hP' : P (f x) x = 1 :=
      (hP_one_iff_oddH (f x) x horev).2 (by simpa [hsymm] using hH)
    exact ((hf (f x) x).1 hP').symm
  exact zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    f hfInvol hfOdd hfAvoid horient

end Erdos85

#print axioms Erdos85.zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
#print axioms Erdos85.zmodEight_selfIntertwiner_sameParity_degreeOne_impossible

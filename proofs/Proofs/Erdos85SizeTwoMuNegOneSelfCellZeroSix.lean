import Proofs.Erdos85SizeTwoMuNegOneEightEightDiagonalSameShape

/-! # Eliminating the `mu=-1`, `(k,r)=(0,6)` self-switch cell -/

namespace Erdos85

noncomputable section

/-- A symmetric binary row-one C8 self-intertwiner cannot be supported only
on odd offsets while avoiding the two cycle offsets. -/
theorem zmodEight_selfIntertwiner_rowOne_odd_avoiding_cycle_impossible
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hsymm : ∀ x y, M x y = M y x)
    (hinter : ∀ x y,
      M (x - 1) y + M (x + 1) y =
        M x (y + 1) + M x (y - 1))
    (hbinary : ∀ x y, M x y = 0 ∨ M x y = 1)
    (hrow : ∀ x, ∑ y, M x y = 1)
    (hodd : ∀ x y, M x y = 1 → ¬ ZModEightEvenOffset (y - x))
    (havoid : ∀ x, M x (x - 1) = 0 ∧ M x (x + 1) = 0) : False := by
  classical
  obtain ⟨f, hf, horient⟩ :=
    binary_rowOne_cycleIntertwiner_orientation (r := 8) (by omega)
      M hinter hbinary hrow
  have hfOdd : ∀ x, ¬ ZModEightEvenOffset (f x - x) := by
    intro x
    exact hodd x (f x) ((hf x (f x)).2 rfl)
  have hfAvoid : ∀ x, f x ≠ x - 1 ∧ f x ≠ x + 1 := by
    intro x
    constructor
    · intro h
      have hM := (hf x (f x)).2 rfl
      rw [h, (havoid x).1] at hM
      norm_num at hM
    · intro h
      have hM := (hf x (f x)).2 rfl
      rw [h, (havoid x).2] at hM
      norm_num at hM
  have hfInvol : ∀ x, f (f x) = x := by
    intro x
    have hM : M x (f x) = 1 := (hf x (f x)).2 rfl
    have hM' : M (f x) x = 1 := by simpa [hsymm] using hM
    exact ((hf (f x) x).1 hM').symm
  exact zmodEight_no_oriented_symmetric_odd_matching_avoiding_cycle
    f hfInvol hfOdd hfAvoid horient

/-- The normalized self-cell socket: an empty same-sign shape (`k=0`),
total diagonal degree one (`r=6`), and all-triangle cycle avoidance are
incompatible. -/
theorem zmodEight_sameSignShape_zero_rowOne_avoiding_cycle_impossible
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hshape : ZModEightSameSignShapeUpToThree M f 0)
    (hsymm : ∀ x y, M x y = M y x)
    (hinter : ∀ x y,
      M (x - 1) y + M (x + 1) y =
        M x (y + 1) + M x (y - 1))
    (hbinary : ∀ x y, M x y = 0 ∨ M x y = 1)
    (hrow : ∀ x, ∑ y, M x y = 1)
    (havoid : ∀ x, M x (x - 1) = 0 ∧ M x (x + 1) = 0) : False := by
  have heven := zmodEight_alternating_sign_eq_iff_evenOffset f hsign hflip
  have hempty : ∀ i j, f j = f i → M i j ≠ 1 := by
    rcases hshape with hshape | hthree
    · rcases hshape with hzero | hone | htwo
      · exact hzero.2
      · omega
      · omega
    · omega
  have hodd : ∀ x y, M x y = 1 →
      ¬ ZModEightEvenOffset (y - x) := by
    intro x y hM he
    exact (hempty x y ((heven x y).2 he)) hM
  exact zmodEight_selfIntertwiner_rowOne_odd_avoiding_cycle_impossible
    M hsymm hinter hbinary hrow hodd havoid

end

end Erdos85

#print axioms Erdos85.zmodEight_selfIntertwiner_rowOne_odd_avoiding_cycle_impossible
#print axioms Erdos85.zmodEight_sameSignShape_zero_rowOne_avoiding_cycle_impossible

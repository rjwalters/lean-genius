import Proofs.Erdos85SizeTwoMuNegThreeEightEightDiagonalSameShape
import Proofs.Erdos85SizeTwoEigenlineEightEightLowParameterDiagonalModels

/-! # The four signed diagonal shapes in the `mu=-1` eight-plus-eight stratum -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The four possible same-sign supports of a loopless signed C8 block. -/
def ZModEightSameSignShapeUpToThree
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f : ZMod 8 → ℤ) (k : ℕ) : Prop :=
  ZModEightSameSignShape M f k ∨
  (k = 3 ∧ ∀ i j, f j = f i →
    (M i j = 1 ↔ j - i = 2 ∨ j - i = 4 ∨ j - i = 6))

/-- A symmetric loopless C8 self-intertwiner whose alternating-line
same-sign degree is at most three has exactly one of four shapes: empty,
the antipodal matching, the offset `±2` cycle, or all three nonzero even
offsets. -/
theorem zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_three
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (k : ℕ) (hk : k ≤ 3)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i)
    (hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1))
    (hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f i ∧ M i j = 1).card = k) :
    ZModEightSameSignShapeUpToThree M f k := by
  classical
  rcases Nat.lt_or_eq_of_le hk with hk2 | rfl
  · left
    exact zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_two M f k
      (by omega) hsign hflip hdiag hsymm hinter hdegree
  · right
    refine ⟨rfl, ?_⟩
    have heven := zmodEight_alternating_sign_eq_iff_evenOffset f hsign hflip
    have hdegree' : ∀ i,
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 3 := by
      intro i
      calc
        _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            f j = f i ∧ M i j = 1).card := by
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← heven i j]
        _ = 3 := hdegree i
    have hshape := zmodEight_sameParity_degreeThree_offset_two_four_six
      M hdiag hdegree'
    intro i j hsame
    exact hshape i j ((heven i j).mp hsame)

end


end Erdos85

#print axioms Erdos85.zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_three

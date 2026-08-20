import Proofs.Erdos85SizeTwoMuNegThreeEightEightDiagonalSameShape

/-!
# Offset-two nondefect pairs in the `k = 1` C8 diagonal shape

The `k = 1` same-sign defect support is the antipodal matching.  Hence the
two offset-two pairs at every coordinate are nondefect.  This does **not**
make them exterior-pair edges: the underlying C8 supplies the internal common
neighbor at the intervening coordinate.  For h512/h313 owner realizations the
relevant same-shore exterior pairs instead occur at offset `±3`.
-/

open Matrix

namespace Erdos85

noncomputable section

/-- In the `k = 1` classified diagonal shape, both offset-two entries are
nondefect. -/
theorem ZModEightSameSignShape.offsetTwo_ne_one
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hshape : ZModEightSameSignShape M f 1) (i : ZMod 8) :
    M i (i + 2) ≠ 1 ∧ M i (i - 2) ≠ 1 := by
  rcases hshape with hzero | hone | htwo
  · obtain ⟨hbad, _⟩ := hzero
    omega
  · obtain ⟨_, hone⟩ := hone
    have hplusSign : f (i + 2) = f i := by
      have h1 := hflip i
      have h2 := hflip (i + 1)
      rw [show i + 1 + 1 = i + 2 by ring] at h2
      omega
    have hminusSign : f (i - 2) = f i := by
      exact (zmodEight_alternating_sign_eq_iff_evenOffset
        f hsign hflip i (i - 2)).mpr (by
          fin_cases i <;> decide)
    constructor
    · intro hm
      have hoff := (hone i (i + 2) hplusSign).mp hm
      have hne : (i + 2) - i ≠ (4 : ZMod 8) := by
        fin_cases i <;> decide
      exact hne hoff
    · intro hm
      have hoff := (hone i (i - 2) hminusSign).mp hm
      have hne : (i - 2) - i ≠ (4 : ZMod 8) := by
        fin_cases i <;> decide
      exact hne hoff
  · obtain ⟨hbad, _⟩ := htwo
    omega

end

end Erdos85

#print axioms Erdos85.ZModEightSameSignShape.offsetTwo_ne_one

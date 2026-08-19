import Proofs.Erdos85SizeTwoMuNegThreeEightEightParameterBounds

/-! # Signed capacity bounds for the `mu=-1` C8+C8 quotient -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- When the global same-sign degree is three, the internal and cross signed
row counts force `3 ≤ r+k ≤ 7`.  The four values of `k` give the useful
upper bounds `r≤6,5,4` for `k=1,2,3`, respectively. -/
theorem alternating_C8_internal_cross_parameter_bounds_three
    (N M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (k r : ℕ) (hk : k ≤ 3)
    (hfsign : ∀ i, f i = -1 ∨ f i = 1)
    (hgsign : ∀ i, g i = -1 ∨ g i = 1)
    (hfflip : ∀ i, f (i + 1) = -f i)
    (hgflip : ∀ i, g (i + 1) = -g i)
    (hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r)
    (hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ N 0 j = 1).card = k)
    (hMrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      M 0 j = 1).card = r)
    (hMsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f 0 ∧ M 0 j = 1).card = 3 - k) :
    3 ≤ r + k ∧ r + k ≤ 7 ∧
      (k = 0 → 3 ≤ r) ∧
      (k = 1 → r ≤ 6) ∧
      (k = 2 → r ≤ 5) ∧
      (k = 3 → r ≤ 4) := by
  have hNle := binary_C8_row_card_le_same_add_four
    N f hfsign hfflip 0 (f 0) (hfsign 0)
  have hMle := binary_C8_row_card_le_same_add_four
    M g hgsign hgflip 0 (f 0) (hfsign 0)
  rw [hNrow, hNsame] at hNle
  rw [hMrow, hMsame] at hMle
  omega

end


end Erdos85

#print axioms Erdos85.alternating_C8_internal_cross_parameter_bounds_three

import Proofs.Erdos85SizeTwoEigenlineEightEightHighSectorSaturation

/-!
# The high eight-plus-eight parameter is six

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The high quotient parameter cannot be seven.  The finite input is that an
alternating sign on an eight-cycle has only four vertices of either sign;
if the diagonal defect degree vanished, the global five same-sign defect
neighbours would all have to fit in the opposite cycle.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An alternating `±1` labeling of `ZMod 8` has four entries of each sign. -/
theorem zmodEight_alternating_sign_filter_cards
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i) :
    ((Finset.univ : Finset (ZMod 8)).filter (fun i => f i = f 0)).card = 4 ∧
      ((Finset.univ : Finset (ZMod 8)).filter
        (fun i => f i = -f 0)).card = 4 := by
  have h1 : f 1 = -f 0 := by simpa using hflip 0
  have h2 : f 2 = f 0 := by
    calc
      f 2 = -f 1 := by
        simpa only [show (1 : ZMod 8) + 1 = 2 by decide] using hflip 1
      _ = f 0 := by rw [h1]; ring
  have h3 : f 3 = -f 0 := by
    calc
      f 3 = -f 2 := by
        simpa only [show (2 : ZMod 8) + 1 = 3 by decide] using hflip 2
      _ = -f 0 := by rw [h2]
  have h4 : f 4 = f 0 := by
    calc
      f 4 = -f 3 := by
        simpa only [show (3 : ZMod 8) + 1 = 4 by decide] using hflip 3
      _ = f 0 := by rw [h3]; ring
  have h5 : f 5 = -f 0 := by
    calc
      f 5 = -f 4 := by
        simpa only [show (4 : ZMod 8) + 1 = 5 by decide] using hflip 4
      _ = -f 0 := by rw [h4]
  have h6 : f 6 = f 0 := by
    calc
      f 6 = -f 5 := by
        simpa only [show (5 : ZMod 8) + 1 = 6 by decide] using hflip 5
      _ = f 0 := by rw [h5]; ring
  have h7 : f 7 = -f 0 := by
    calc
      f 7 = -f 6 := by
        simpa only [show (6 : ZMod 8) + 1 = 7 by decide] using hflip 6
      _ = -f 0 := by rw [h6]
  have hne : f 0 ≠ -f 0 := by
    rcases hsign 0 with hneg | hpos <;> omega
  have hne' : -f 0 ≠ f 0 := Ne.symm hne
  have hsame : (Finset.univ : Finset (ZMod 8)).filter
      (fun i => f i = f 0) = {0, 2, 4, 6} := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 := by
      revert i
      decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h1, h2, h3, h4, h5, h6, h7, hne'] <;> decide
  have hopp : (Finset.univ : Finset (ZMod 8)).filter
      (fun i => f i = -f 0) = {1, 3, 5, 7} := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 := by
      revert i
      decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h1, h2, h3, h4, h5, h6, h7, hne] <;> decide
  rw [hsame, hopp]
  decide

end

end Erdos85

#print axioms Erdos85.zmodEight_alternating_sign_filter_cards

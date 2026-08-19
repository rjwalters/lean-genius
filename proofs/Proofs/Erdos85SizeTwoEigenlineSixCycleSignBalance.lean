import Mathlib

/-!
# Sign balance on an alternating six-cycle

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

An alternating `±1` labeling of a six-cycle has three vertices of each sign.
This finite lemma is separated from the graph bookkeeping so it can feed the
coordinate-free cross-sign saturation argument.
-/

open Finset

namespace Erdos85

/-- An alternating `±1` function on `ZMod 6` has exactly three entries equal
to its base value and three equal to its negative. -/
theorem zmodSix_alternating_sign_filter_cards
    (f : ZMod 6 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i) :
    ((Finset.univ : Finset (ZMod 6)).filter (fun i => f i = f 0)).card = 3 ∧
      ((Finset.univ : Finset (ZMod 6)).filter
        (fun i => f i = -f 0)).card = 3 := by
  have h1 : f 1 = -f 0 := by simpa using hflip 0
  have h2 : f 2 = f 0 := by
    calc
      f 2 = -f 1 := by
        simpa only [show (1 : ZMod 6) + 1 = 2 by decide] using hflip 1
      _ = f 0 := by rw [h1]; ring
  have h3 : f 3 = -f 0 := by
    calc
      f 3 = -f 2 := by
        simpa only [show (2 : ZMod 6) + 1 = 3 by decide] using hflip 2
      _ = -f 0 := by rw [h2]
  have h4 : f 4 = f 0 := by
    calc
      f 4 = -f 3 := by
        simpa only [show (3 : ZMod 6) + 1 = 4 by decide] using hflip 3
      _ = f 0 := by rw [h3]; ring
  have h5 : f 5 = -f 0 := by
    calc
      f 5 = -f 4 := by
        simpa only [show (4 : ZMod 6) + 1 = 5 by decide] using hflip 4
      _ = -f 0 := by rw [h4]
  have hne : f 0 ≠ -f 0 := by
    rcases hsign 0 with hneg | hpos <;> omega
  have hne' : -f 0 ≠ f 0 := Ne.symm hne
  have hsame : (Finset.univ : Finset (ZMod 6)).filter
      (fun i => f i = f 0) = {0, 2, 4} := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      revert i
      decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h1, h2, h3, h4, h5, hne'] <;> decide
  have hopp : (Finset.univ : Finset (ZMod 6)).filter
      (fun i => f i = -f 0) = {1, 3, 5} := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      revert i
      decide
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [h1, h2, h3, h4, h5, hne] <;> decide
  rw [hsame, hopp]
  decide

end Erdos85

#print axioms Erdos85.zmodSix_alternating_sign_filter_cards

import Mathlib

-- Check Finset.offDiag card lemma names
#check @Finset.offDiag
#check @Finset.offDiag_card

-- Check alternative names
example (s : Finset ℕ) : s.offDiag.card = s.card * (s.card - 1) := by
  exact Finset.offDiag_card s

-- Check Rat.toNat
#check @Rat.toNat

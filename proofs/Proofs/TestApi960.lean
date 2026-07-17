import Mathlib

-- Check Finset.offDiag card lemma names
#check @Finset.offDiag
#check @Finset.offDiag_card

-- Check alternative names (v4.31: offDiag_card is `card * card - card`)
example (s : Finset ℕ) : s.offDiag.card = s.card * s.card - s.card := by
  exact Finset.offDiag_card s

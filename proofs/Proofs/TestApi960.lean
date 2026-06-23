import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

-- Check Finset.offDiag card lemma names
#check @Finset.offDiag
#check @Finset.card_offDiag

-- Check alternative names
example (s : Finset ℕ) : s.offDiag.card = s.card * (s.card - 1) := by
  exact Finset.card_offDiag s

-- Check Rat.toNat
#check @Rat.toNat

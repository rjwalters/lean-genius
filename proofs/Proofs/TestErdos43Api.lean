-- Test API availability for Erdos43 fixes
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Mathlib.Order.LocallyFiniteOrder

-- Test: What's the ℤ Icc card API?
#check @Int.Icc_toFinset_card
#check @Finset.card_Icc_of_le
#check @Int.card_Icc

-- Test: direct computation for Icc card
example (N : ℕ) (hN : N ≥ 1) : (Finset.Icc (1 : ℤ) (↑N - 1)).card ≤ N := by
  simp only [Int.card_Icc]
  omega

-- Test: Alternative with Finset.Icc_card
example (N : ℕ) (hN : N ≥ 1) : (Finset.Icc (1 : ℤ) (↑N - 1)).card ≤ N := by
  have : (Finset.Icc (1 : ℤ) (↑N - 1)).card = (↑N - 1 - 1 + 1).toNat := by
    rfl
  omega

-- Test pair_eq_pair_iff alternative
example (a b c d : ℤ) (hab : a ≠ b) (hcd : c ≠ d) :
    ({a, b} : Finset ℤ) = {c, d} → (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  intro h
  simp only [Finset.ext_iff, Finset.mem_insert, Finset.mem_singleton] at h
  have hac : a = c ∨ a = d := by simpa using (h a).mp (by left; rfl)
  have hbc : b = c ∨ b = d := by simpa using (h b).mp (by right; rfl)
  rcases hac with rfl | rfl
  · rcases hbc with rfl | rfl
    · exact absurd rfl hab
    · left; exact ⟨rfl, rfl⟩
  · rcases hbc with rfl | rfl
    · right; exact ⟨rfl, rfl⟩
    · exact absurd rfl hab

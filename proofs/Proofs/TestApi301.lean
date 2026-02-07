-- Test API availability for Erdős 301
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Order
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset

-- Test: Rat division properties
example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (1 : ℚ) / a ≠ (1 : ℚ) / b := by
  intro h
  have : (a : ℚ) = (b : ℚ) := by
    field_simp at h
    linarith
  exact hab (Nat.cast_injective this)

-- Test: sum over finset bound
example (N : ℕ) (B : Finset ℕ) (hB : ∀ b ∈ B, N / 2 < b ∧ b ≤ N) (hcard : 2 ≤ B.card) :
    (1 : ℚ) / N < B.sum (fun b => (1 : ℚ) / b) := by
  sorry

-- Test: Finset.sum_le_sum type
#check @Finset.sum_le_sum

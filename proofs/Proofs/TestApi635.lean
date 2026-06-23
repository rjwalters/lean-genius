import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic

-- Test: even number cannot divide odd number
example (n d : ℕ) (hn : n % 2 = 1) (hd : d % 2 = 0) (hd0 : d ≠ 0) : ¬(d ∣ n) := by
  intro ⟨k, hk⟩
  have : n % 2 = (d * k) % 2 := by rw [hk]
  rw [Nat.mul_mod, hd] at this
  simp at this
  linarith

-- Test: difference of two odds is even
example (a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) (hab : a < b) :
    (b - a) % 2 = 0 := by
  omega

-- Test: Finset.card_le_card
example (s t : Finset ℕ) (h : s ⊆ t) : s.card ≤ t.card :=
  Finset.card_le_card h

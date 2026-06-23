import Mathlib.Data.Nat.Totient
import Mathlib.Data.Finset.Basic

open Nat Finset

-- Check key APIs
#check Nat.totient_le  -- totient m ≤ m
#check Nat.totient_prime
#check Nat.totient_prime_pow
#check @Nat.totient_even

-- Small computations
#eval Nat.totient 3  -- expect 2

-- Test: Finset.card_le_card for V' ≤ V
#check @Finset.card_le_card

-- Test key proof idea: image ⊆ filter
example : (Finset.image Nat.totient (Finset.range 4)) ⊆
    (Finset.filter (fun n => ∃ m, Nat.totient m = n) (Finset.range 4)) := by
  intro n hn
  simp only [mem_image, mem_range] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  simp only [mem_filter, mem_range]
  exact ⟨Nat.lt_of_lt_of_le hm (Nat.totient_le m) |>.trans_le (by omega), ⟨m, rfl⟩⟩

-- Wait, totient_le gives totient m ≤ m, not totient m < m. Let me adjust.
-- Actually we need totient m ∈ range (x+1), i.e. totient m ≤ x
-- Since m ∈ range (x+1), we have m ≤ x, and totient m ≤ m ≤ x
-- So totient m ∈ range (x+1)

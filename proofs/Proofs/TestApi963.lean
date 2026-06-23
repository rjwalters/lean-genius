import Mathlib.Data.Nat.Log
import Mathlib.Tactic

-- Nat.log_anti_left : {b c n : ℕ} → 1 < c → c ≤ b → Nat.log b n ≤ Nat.log c n
-- So log_anti_left (1 < 2) (2 ≤ 3) gives Nat.log 3 n ≤ Nat.log 2 n

-- Test log_base_gap
example (n : ℕ) (hn : n ≥ 2) : Nat.log 3 n ≤ Nat.log 2 n :=
  Nat.log_anti_left (by omega) (by omega)

-- Test: powers of 2 sum uniqueness via Finset
-- We need to check what's available for this
#check Finset.sum_pow_eq_pow_sum
#check Nat.sum_range_id_eq_sum_range_succ

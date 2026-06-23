-- Minimal API test for Erdős 952
import Mathlib

open GaussianInt

-- Test 1: GaussianInt.norm type
-- GaussianInt is Zsqrtd (-1)
-- Zsqrtd.norm returns ℤ
#check @Zsqrtd.norm  -- Zsqrtd d → ℤ
#check @Zsqrtd.norm_nonneg

-- Test 2: Nat.Prime.sq_add_sq
#check @Nat.Prime.sq_add_sq
-- Expected: Nat.Prime p → p % 4 ≠ 3 → ∃ a b : ℤ, a ^ 2 + b ^ 2 = ↑p

-- Test 3: norm non-negativity for d = -1
example (z : GaussianInt) : 0 ≤ Zsqrtd.norm z :=
  Zsqrtd.norm_nonneg (hd := by norm_num) z

-- Test 4: norm < 0 is impossible
example : ¬ (Zsqrtd.norm (0 : GaussianInt) < (0 : ℤ)) := by
  simp [Zsqrtd.norm]

-- Test 5: Int.ofNat_le
example (j k : ℕ) (h : j ≤ k) : (j : ℤ) ≤ (k : ℤ) := by
  exact Int.ofNat_le.mpr h

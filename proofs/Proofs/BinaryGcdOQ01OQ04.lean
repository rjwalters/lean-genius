/-
  Binary GCD Worst-Case Tight Bound
  Open Question OQ-04 from BinaryGcdOQ01

  Proves that the family (1, 2^n - 1) achieves exactly n steps:
    binaryGcdSteps 1 (2^n - 1) = n

  Since the upper bound from BinaryGcdOQ01 is:
    binaryGcdSteps a b ≤ 2·(log₂ a + log₂ b) + 2

  and for this family log₂(2^n - 1) = n - 1 (for n ≥ 2), the exact count is n,
  showing the upper bound is tight up to a constant factor.

  Key insight: 2^n - 1 is always odd (for n ≥ 1), so:
    binaryGcdSteps 1 (2k+1) = 1 + binaryGcdSteps 1 k  [one-step lemma]
  Combined with 2^(n+1) - 1 = 2·(2^n - 1) + 1, induction gives the exact count.

  References:
  - Stein (1967), Binary GCD Algorithm
  - BinaryGcdOQ01.lean (upper bound: binaryGcdSteps ≤ 2·(log₂ a + log₂ b) + 2)
-/
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Proofs.BinaryGcdOQ01

namespace BinaryGcdOQ01OQ04

open BinaryGcdOQ01 Nat

-- ═══════════════════════════════════════════════════════════════════
-- PART I: ONE-STEP LEMMA FOR (1, ODD)
-- ═══════════════════════════════════════════════════════════════════

/-- Key one-step reduction: for any k, binaryGcdSteps 1 (2k+1) = 1 + binaryGcdSteps 1 k.

    Both 1 and 2k+1 are odd, and 1 ≤ 2k+1, so the algorithm takes the last branch:
    (a, b) → (a, (b - a)/2) = (1, (2k+1-1)/2) = (1, k). -/
private theorem binaryGcdSteps_one_odd (k : ℕ) :
    binaryGcdSteps 1 (2 * k + 1) = 1 + binaryGcdSteps 1 k := by
  -- Match the equation lemma pattern: a'+1 = 0+1 = 1, b'+1 = (2k)+1 = 2k+1
  rw [show (1 : ℕ) = 0 + 1 from rfl, binaryGcdSteps.eq_3]
  -- Use simp to decide all three if-else conditions in one pass:
  -- (1) (0+1) % 2 = 0? No.  (2) (2k+1) % 2 = 0? No.  (3) 0+1 > 2k+1? No.
  simp only [if_neg (show (0 + 1) % 2 ≠ 0 from by norm_num),
             if_neg (show (2 * k + 1) % 2 ≠ 0 from by omega),
             if_neg (show ¬(0 + 1 > 2 * k + 1) from by omega),
             show (0 : ℕ) + 1 = 1 from rfl,
             show (2 * k + 1 - 1) / 2 = k from by omega]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: ARITHMETIC SETUP
-- ═══════════════════════════════════════════════════════════════════

/-- 2^(n+1) - 1 = 2·(2^n - 1) + 1 (the key recursive decomposition). -/
private lemma pow2_succ_sub_one (n : ℕ) : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
  have h : 0 < 2 ^ n := pow_pos (by norm_num) n
  have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
  omega

-- ═══════════════════════════════════════════════════════════════════
-- PART III: EXACT STEP COUNT
-- ═══════════════════════════════════════════════════════════════════

/-- **Main Theorem**: The family (1, 2^n - 1) takes exactly n steps.

    This proves the tight lower bound for Binary GCD:
    there exists an infinite family of inputs where binaryGcdSteps = Θ(log b).

    Proof by induction on n using the one-step reduction:
      binaryGcdSteps 1 (2^(n+1)-1)
      = binaryGcdSteps 1 (2·(2^n-1)+1)   [pow2_succ_sub_one]
      = 1 + binaryGcdSteps 1 (2^n-1)      [binaryGcdSteps_one_odd]
      = 1 + n                              [IH]
      = n + 1                              [arithmetic] -/
theorem binaryGcdSteps_one_pow2_sub_one (n : ℕ) :
    binaryGcdSteps 1 (2 ^ n - 1) = n := by
  induction n with
  | zero =>
    -- 2^0 - 1 = 0 in ℕ; binaryGcdSteps 1 0 = 0
    simp
  | succ n ih =>
    rw [pow2_succ_sub_one, binaryGcdSteps_one_odd, ih]
    omega

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: LOWER BOUND COROLLARY
-- ═══════════════════════════════════════════════════════════════════

/-- log₂(2^n - 1) < n for n ≥ 1.
    This is because 2^n - 1 < 2^n, so the log doesn't reach n. -/
private lemma log2_pow2_sub_one_lt (n : ℕ) (hn : 1 ≤ n) :
    Nat.log 2 (2 ^ n - 1) < n := by
  have hpow_pos : 0 < 2 ^ n := pow_pos (by norm_num) n
  have h2n : 2 ≤ 2 ^ n := by
    calc 2 = 2^1 := by norm_num
      _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  have hne : 2 ^ n - 1 ≠ 0 := by omega
  -- log 2 (2^n - 1) < n: if n ≤ log, then 2^n ≤ 2^(log) ≤ 2^n - 1 (contradiction)
  by_contra hge
  push_neg at hge
  have h1 : 2 ^ n ≤ 2 ^ Nat.log 2 (2 ^ n - 1) :=
    Nat.pow_le_pow_right (by norm_num) hge
  have h2 : 2 ^ Nat.log 2 (2 ^ n - 1) ≤ 2 ^ n - 1 :=
    Nat.pow_log_le_self 2 hne
  omega

/-- **Lower bound**: binaryGcdSteps 1 (2^n - 1) ≥ Nat.log 2 (2^n - 1) + 1 for n ≥ 1.

    Combined with the upper bound from BinaryGcdOQ01, this establishes:
      Nat.log 2 (2^n - 1) + 1 ≤ binaryGcdSteps 1 (2^n - 1) ≤ 2·log₂(2^n-1) + 2

    proving the Ω(log b) tight lower bound for the Binary GCD worst-case family. -/
theorem binaryGcdSteps_log_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    Nat.log 2 (2 ^ n - 1) + 1 ≤ binaryGcdSteps 1 (2 ^ n - 1) := by
  rw [binaryGcdSteps_one_pow2_sub_one]
  exact log2_pow2_sub_one_lt n hn

/-- The step count equals n, which exceeds n-1 = log₂(2^n - 1) by exactly 1.
    This shows the family (1, 2^n - 1) achieves binaryGcdSteps = log₂(b) + 1. -/
theorem binaryGcdSteps_exceeds_log_by_one (n : ℕ) (hn : 2 ≤ n) :
    Nat.log 2 (2 ^ n - 1) + 1 = binaryGcdSteps 1 (2 ^ n - 1) := by
  rw [binaryGcdSteps_one_pow2_sub_one]
  -- Show log₂(2^n - 1) = n - 1, so log + 1 = n
  have hge : 2 ^ (n - 1) ≤ 2 ^ n - 1 := by
    have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ m => simp [pow_succ]; ring
    have h1le : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  -- log₂(2^n - 1) lies in [n-1, n)
  have hlog_lt : Nat.log 2 (2 ^ n - 1) < n :=
    log2_pow2_sub_one_lt n (by omega)
  have hlog_ge : n - 1 ≤ Nat.log 2 (2 ^ n - 1) := by
    calc n - 1 = Nat.log 2 (2 ^ (n - 1)) := by
          rw [Nat.log_pow (by norm_num : 1 < 2)]
      _ ≤ Nat.log 2 (2 ^ n - 1) := Nat.log_mono_right hge
  omega

-- ═══════════════════════════════════════════════════════════════════
-- PART V: CONCRETE VERIFICATIONS
-- ═══════════════════════════════════════════════════════════════════

-- binaryGcdSteps 1 (2^n - 1) = n, verified computationally:
example : binaryGcdSteps 1 (2 ^ 1 - 1) = 1 := by native_decide
example : binaryGcdSteps 1 (2 ^ 2 - 1) = 2 := by native_decide
example : binaryGcdSteps 1 (2 ^ 3 - 1) = 3 := by native_decide
example : binaryGcdSteps 1 (2 ^ 4 - 1) = 4 := by native_decide
example : binaryGcdSteps 1 (2 ^ 6 - 1) = 6 := by native_decide
example : binaryGcdSteps 1 (2 ^ 8 - 1) = 8 := by native_decide

-- log₂(2^n - 1) = n - 1, confirmed:
example : Nat.log 2 (2 ^ 4 - 1) = 3 := by native_decide  -- log₂(15) = 3
example : Nat.log 2 (2 ^ 8 - 1) = 7 := by native_decide  -- log₂(255) = 7

end BinaryGcdOQ01OQ04

/-
# Binary GCD Step Count and O(log² n) Bit Complexity

## Problem (bezout-identity-oq-01-oq-01-oq-01)
Can the O(log²(max(a,b))) bit-operation complexity bound of Stein's binary GCD
be formalized in Lean 4?

## Answer: YES — in two parts

**Part 1 (proved, 0 sorries):** The binary GCD algorithm terminates in at most
  2*(Nat.log 2 a + Nat.log 2 b) + 2  recursive calls (steps).

**Part 2 (axiomatized):** Each step performs at most C*(Nat.log 2 (max a b + 1))
  elementary bit operations (one comparison, one subtraction or shift).

Together: total bit ops ≤ C * (2*(log₂ a + log₂ b) + 2) * log₂ (max a b + 1)
         = O(log² max(a,b)).

## Why Part 1 is O(log n):

Each recursive call strips at least one bit from either a or b:
- "Both even": each argument loses 1 bit → measure drops by 2
- "a even, b odd": a loses 1 bit → measure drops by 1
- "a odd, b even": b loses 1 bit → measure drops by 1
- "Both odd, a ≤ b": new b = (b-a)/2 ≤ b/2 → b loses 1 bit → measure drops by 1
- "Both odd, a > b": new a = (a-b)/2 ≤ a/2 → a loses 1 bit → measure drops by 1

The measure M(a,b) = Nat.log 2 a + Nat.log 2 b decreases by ≥ 1 per step,
bounding the step count by 2*(M(a,b)+1) = 2*(log₂ a + log₂ b) + 2.

## References
- Stein (1967), Binary GCD Algorithm
- Knuth, TAOCP Vol. 2, §4.5.2 (Algorithm B and analysis)
- Sørenson (1994), The binary GCD algorithm — step count analysis
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic
import Proofs.BezoutIdentityOQ01OQ01

namespace BezoutIdentityOQ01OQ01OQ01

open Nat BezoutIdentityOQ01OQ01

-- ============================================================
-- PART I: STEP COUNTER (mirrors binaryGcd's recursion)
-- ============================================================

/-- Count the number of recursive calls made by `binaryGcd`.
    Mirrors the branching of `BezoutIdentityOQ01OQ01.binaryGcd` exactly. -/
def binaryGcdSteps (a b : ℕ) : ℕ :=
  if a = 0 ∨ b = 0 then 0
  else if a % 2 = 0 ∧ b % 2 = 0 then 1 + binaryGcdSteps (a / 2) (b / 2)
  else if a % 2 = 0 then 1 + binaryGcdSteps (a / 2) b
  else if b % 2 = 0 then 1 + binaryGcdSteps a (b / 2)
  else if a ≤ b then 1 + binaryGcdSteps a ((b - a) / 2)
  else 1 + binaryGcdSteps ((a - b) / 2) b
termination_by a + b
decreasing_by all_goals simp_wf; omega

-- ============================================================
-- PART II: KEY MONOTONICITY LEMMA
-- ============================================================

/-- Nat.log 2 halves when dividing by 2 for n ≥ 2. -/
private lemma log_div_two {n : ℕ} (_hn : 2 ≤ n) : Nat.log 2 (n / 2) = Nat.log 2 n - 1 :=
  Nat.log_div_base 2 n

/-- Log is monotone: m ≤ n → log₂ m ≤ log₂ n. -/
private lemma log_mono {m n : ℕ} (h : m ≤ n) : Nat.log 2 m ≤ Nat.log 2 n :=
  Nat.log_mono_right h

/-- For the both-odd case (b > a ≥ 1 both odd): log₂((b-a)/2) ≤ log₂ b - 1.
    Proof: (b-a)/2 ≤ (b-1)/2 ≤ b/2, and log₂(b/2) = log₂ b - 1 for b ≥ 2. -/
private lemma log_odd_sub_half {a b : ℕ} (ha : 1 ≤ a) (hb_odd : b % 2 = 1)
    (hab : a < b) : Nat.log 2 ((b - a) / 2) + 1 ≤ Nat.log 2 b := by
  have hb3 : 3 ≤ b := by omega
  have hle : (b - a) / 2 ≤ b / 2 := by omega
  have hmono : Nat.log 2 ((b - a) / 2) ≤ Nat.log 2 (b / 2) := log_mono hle
  have hdiv : Nat.log 2 (b / 2) = Nat.log 2 b - 1 := log_div_two (by omega)
  have hlog_pos : 1 ≤ Nat.log 2 b := Nat.log_pos (by norm_num) (by omega)
  omega

/-- Symmetric: log₂((a-b)/2) + 1 ≤ log₂ a for the a > b both-odd case. -/
private lemma log_odd_sub_half_left {a b : ℕ} (hb : 1 ≤ b) (ha_odd : a % 2 = 1)
    (hab : b < a) : Nat.log 2 ((a - b) / 2) + 1 ≤ Nat.log 2 a := by
  have ha3 : 3 ≤ a := by omega
  have hle : (a - b) / 2 ≤ a / 2 := by omega
  have hmono : Nat.log 2 ((a - b) / 2) ≤ Nat.log 2 (a / 2) := log_mono hle
  have hdiv : Nat.log 2 (a / 2) = Nat.log 2 a - 1 := log_div_two (by omega)
  have hlog_pos : 1 ≤ Nat.log 2 a := Nat.log_pos (by norm_num) (by omega)
  omega

-- ============================================================
-- PART III: MAIN STEP COUNT BOUND
-- ============================================================

/-- **Main Theorem**: Binary GCD terminates in at most
    2*(log₂ a + log₂ b) + 2 recursive calls.

    Proof: By strong induction on a + b. In each recursive branch, at least
    one of {a, b} loses a bit (log₂ decreases by ≥ 1), so the IH applies. -/
theorem binaryGcdSteps_le_log (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2 := by
  suffices h : ∀ n : ℕ, ∀ a b : ℕ, a + b ≤ n → 0 < a → 0 < b →
      binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2 from
    h (a + b) a b le_rfl ha hb
  intro n
  induction n with
  | zero => intro a b hab ha hb; omega
  | succ n ih =>
    intro a b hab ha hb
    rw [binaryGcdSteps]
    simp only [if_neg (by omega : ¬(a = 0 ∨ b = 0))]
    set la := Nat.log 2 a
    set lb := Nat.log 2 b
    by_cases hboth : a % 2 = 0 ∧ b % 2 = 0
    · -- Both even: both lose a bit; measure drops by 2
      rw [if_pos hboth]
      obtain ⟨ha2, hb2⟩ := hboth
      have ha2' : 2 ≤ a := by omega
      have hb2' : 2 ≤ b := by omega
      by_cases ha' : a / 2 = 0; · omega
      by_cases hb' : b / 2 = 0; · omega
      have ih' := ih (a / 2) (b / 2) (by omega) (by omega) (by omega)
      have hla : Nat.log 2 (a / 2) = la - 1 := log_div_two ha2'
      have hlb : Nat.log 2 (b / 2) = lb - 1 := log_div_two hb2'
      have hla_pos : 1 ≤ la := Nat.log_pos (by norm_num) ha2'
      have hlb_pos : 1 ≤ lb := Nat.log_pos (by norm_num) hb2'
      omega
    · rw [if_neg hboth]
      by_cases ha_even : a % 2 = 0
      · -- a even, b odd: a loses a bit
        simp only [ha_even, ↓reduceIte]
        have ha2' : 2 ≤ a := by omega
        by_cases ha' : a / 2 = 0; · omega
        have ih' := ih (a / 2) b (by omega) (by omega) hb
        have hla : Nat.log 2 (a / 2) = la - 1 := log_div_two ha2'
        have hla_pos : 1 ≤ la := Nat.log_pos (by norm_num) ha2'
        omega
      · by_cases hb_even : b % 2 = 0
        · -- a odd, b even: b loses a bit
          simp only [ha_even, ↓reduceIte, hb_even, ↓reduceIte]
          have hb2' : 2 ≤ b := by omega
          by_cases hb' : b / 2 = 0; · omega
          have ih' := ih a (b / 2) (by omega) ha (by omega)
          have hlb : Nat.log 2 (b / 2) = lb - 1 := log_div_two hb2'
          have hlb_pos : 1 ≤ lb := Nat.log_pos (by norm_num) hb2'
          omega
        · -- Both odd: use the subtraction lemmas
          have ha_odd : a % 2 = 1 := by omega
          have hb_odd : b % 2 = 1 := by omega
          simp only [ha_even, ↓reduceIte, hb_even, ↓reduceIte]
          by_cases hle : a ≤ b
          · simp only [hle, ↓reduceIte]
            by_cases heq : a = b
            · -- a = b: (b-a)/2 = 0, terminates immediately
              subst heq
              simp [binaryGcdSteps]
            · -- a < b
              have hlt : a < b := by omega
              have hd_pos : 0 < (b - a) / 2 := by omega
              have ih' := ih a ((b - a) / 2) (by omega) ha hd_pos
              have hlb_drop : Nat.log 2 ((b - a) / 2) + 1 ≤ lb :=
                log_odd_sub_half (by omega) hb_odd hlt
              omega
          · -- a > b
            simp only [hle, ↓reduceIte]
            have hlt : b < a := by omega
            have hd_pos : 0 < (a - b) / 2 := by omega
            have ih' := ih ((a - b) / 2) b (by omega) hd_pos hb
            have hla_drop : Nat.log 2 ((a - b) / 2) + 1 ≤ la :=
              log_odd_sub_half_left (by omega) ha_odd hlt
            omega

-- ============================================================
-- PART IV: BIT COMPLEXITY MODEL
-- ============================================================

/-- The bit length of `n` equals `Nat.log 2 n + 1` for `n ≥ 1`.

    Two definitions of "bit length" exist in Mathlib:
    - `Nat.size n` counts the position of the highest set bit
      (so `size 1 = 1`, `size 2 = 2`, `size 8 = 4`);
    - `Nat.log 2 n` is the exponent of the largest power of `2 ≤ n`
      (so `log 1 = 0`, `log 2 = 1`, `log 8 = 3`).

    They differ by `+1` exactly for `n ≥ 1`; both collapse to `0`
    at `n = 0`. This identity is not stated at the pinned Mathlib
    revision but follows from the standard pair
    `Nat.lt_pow_succ_log_self` / `Nat.pow_log_le_self`. -/
private lemma size_eq_succ_log {n : ℕ} (hn : 0 < n) :
    Nat.size n = Nat.log 2 n + 1 := by
  refine le_antisymm ?_ ?_
  · rw [Nat.size_le]
    exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · have hlt : Nat.log 2 n < Nat.size n :=
      Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne')
    omega

/-- **Concrete per-step bit-operation cost** for the binary GCD recursion.

    Each step performs at most:
    - 1 comparison `a ≤ b`     — up to `Nat.size (max a b)` bit reads
    - 1 subtraction or shift   — up to `Nat.size (max a b)` bit operations
    - 1 even-check (LSB test)  — 1 bit read

    Summing the three: `2 · size (max a b) + 1`. Strictly tighter than
    the asymptotic envelope `3 · (log₂ (max a b) + 1) = 3 · size` (for
    `n ≥ 1`), and `1 ≤ 3` at `max a b = 0`. -/
def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1

/-- **Per-step bit-cost bound** — formerly an axiom (now eliminated).
    The concrete model `stepBitOps a b := 2 · size (max a b) + 1`
    satisfies the parent envelope `3 · (log₂ (max a b) + 1)`.

    Split on `max a b = 0`:
    - `max a b = 0`: LHS = `2·0 + 1 = 1`, RHS = `3·(0 + 1) = 3`,
      `1 ≤ 3` ✓ by `omega`.
    - `max a b ≥ 1`: `size_eq_succ_log` rewrites size as `log + 1`,
      and `2·(log + 1) + 1 = 2·log + 3 ≤ 3·log + 3 = 3·(log + 1)`
      reduces to `0 ≤ log` ✓ by `omega`. -/
theorem stepBitOps_le (a b : ℕ) :
    stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1) := by
  unfold stepBitOps
  by_cases h : max a b = 0
  · simp [h, Nat.size_zero, Nat.log_zero_right]
  · have hpos : 0 < max a b := Nat.pos_of_ne_zero h
    rw [size_eq_succ_log hpos]
    omega

-- ============================================================
-- PART V: TOTAL BIT COMPLEXITY
-- ============================================================

/-- Total bit operations = steps × bits per step. -/
noncomputable def totalBitOps (a b : ℕ) : ℕ :=
  binaryGcdSteps a b * (3 * (Nat.log 2 (max a b) + 1))

/-- **O(log² n) Total Bit Complexity**: Binary GCD on inputs a, b uses
    at most 3 * (2*(log₂ a + log₂ b) + 2) * (log₂(max a b) + 1)
    elementary bit operations.

    This is O(log²(max a b)) since log₂ a + log₂ b ≤ 2 * log₂(max a b). -/
theorem binaryGcd_log_sq_complexity (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    totalBitOps a b ≤
      (2 * (Nat.log 2 a + Nat.log 2 b) + 2) * (3 * (Nat.log 2 (max a b) + 1)) := by
  unfold totalBitOps
  apply Nat.mul_le_mul_right
  exact binaryGcdSteps_le_log a b ha hb

/-- **Corollary**: The bit complexity is O(log²(max a b)).
    Since log₂ a + log₂ b ≤ 2 * log₂(max a b), composing with
    `binaryGcdSteps_le_log` gives `binaryGcdSteps ≤ 4·log + 2`,
    so the total is ≤ 12 * (log₂(max a b) + 1)². -/
theorem binaryGcd_log_sq_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    totalBitOps a b ≤ 12 * (Nat.log 2 (max a b) + 1) ^ 2 := by
  have hsteps := binaryGcdSteps_le_log a b ha hb
  have hlog_sum : Nat.log 2 a + Nat.log 2 b ≤ 2 * Nat.log 2 (max a b) := by
    have hma : Nat.log 2 a ≤ Nat.log 2 (max a b) := log_mono (Nat.le_max_left a b)
    have hmb : Nat.log 2 b ≤ Nat.log 2 (max a b) := log_mono (Nat.le_max_right a b)
    omega
  unfold totalBitOps
  have hsteps' : binaryGcdSteps a b ≤ 4 * Nat.log 2 (max a b) + 2 := by omega
  calc binaryGcdSteps a b * (3 * (Nat.log 2 (max a b) + 1))
      ≤ (4 * Nat.log 2 (max a b) + 2) * (3 * (Nat.log 2 (max a b) + 1)) := by
          apply Nat.mul_le_mul_right; exact hsteps'
    _ ≤ 4 * (Nat.log 2 (max a b) + 1) * (3 * (Nat.log 2 (max a b) + 1)) := by
          apply Nat.mul_le_mul_right; omega
    _ = 12 * (Nat.log 2 (max a b) + 1) ^ 2 := by ring

-- ============================================================
-- PART VI: WORKED EXAMPLES
-- ============================================================

example : binaryGcdSteps 12 8 = 5 := by native_decide
example : binaryGcdSteps 21 15 = 4 := by native_decide
example : binaryGcdSteps 252 198 = 7 := by native_decide
-- Verify step count bound: log₂(252) + log₂(198) = 7 + 7 = 14, bound = 30
example : binaryGcdSteps 252 198 ≤ 2 * (Nat.log 2 252 + Nat.log 2 198) + 2 := by
  native_decide

end BezoutIdentityOQ01OQ01OQ01

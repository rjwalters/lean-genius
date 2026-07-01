/-
Formal Divisibility Rules — Extension OQ-01-OQ-03

**Casting out nines, the alternating dual: general alternating digit-sum rule
for any base b ≡ -1 (mod d).**

The parent extension (DivisibilityByThreeOQ01) develops the *additive* digit-sum
theory: when the base b satisfies b ≡ 1 (mod d), a number is congruent to the
plain sum of its base-b digits (casting out nines is the case b = 10, d = 9).
Mathlib packages this as `Nat.modEq_digits_sum` / `Nat.dvd_iff_dvd_digits_sum`.

The *dual* phenomenon — bases with b ≡ -1 (mod d) — produces the **alternating**
digit-sum rule. Mathlib only records the single classical instance
`Nat.modEq_eleven_digits_sum` / `Nat.eleven_dvd_iff` (base 10, mod 11). This file
proves the general statement for arbitrary (b, d) with d ∣ b + 1, exactly
paralleling the additive theory, and derives the divisibility tests that the
parent's Part X only *mentions* without proof: since 1001 = 7·11·13, alternating
three-digit (base-1000) group sums simultaneously test divisibility by 7, 11, 13
and 1001.

Main results:
* `modEq_alternating_digits`  — congruence: n ≡ altSum(digits b n) (mod d) when d ∣ b+1
* `dvd_iff_dvd_alternating_digits` — divisibility test form
* `dvd_succ_base_iff_alternating` — the universal corollary: in any base b,
    (b+1) ∣ n ↔ (b+1) ∣ altSum(digits b n)  (generalizes "11 in base 10")
* Instances: 11 (base 10), 101 (base 100), and 7 / 11 / 13 / 1001 (base 1000)
* `alternating_digit_rules_summary` — master statement

Everything reduces to Mathlib's master congruence `Nat.zmodeq_ofDigits_digits`
with residue c = -1, so the file is fully machine-checked with no axioms.

Tags: number-theory, modular-arithmetic, divisibility, alternating-digit-sum, extension
-/

import Mathlib.Data.Nat.Digits.Div
import Mathlib.Tactic

open Nat

namespace DivisibilityByThreeOQ01OQ03

/-- The alternating sum of the base-`b` digits of `n`, taken in `ℤ`.
    `[a₀, a₁, a₂, …] ↦ a₀ - a₁ + a₂ - …`. -/
def altDigitSum (b n : ℕ) : ℤ :=
  ((Nat.digits b n).map fun k : ℕ => (k : ℤ)).alternatingSum

-- ============================================================
-- Part I: The general alternating digit-sum theorem
-- ============================================================

/-- **General casting-out (alternating form), congruence version.**

    If the base `b` satisfies `d ∣ b + 1` (i.e. `b ≡ -1 mod d`), then every
    natural number is congruent modulo `d` to the alternating sum of its
    base-`b` digits. This is the exact dual of the additive rule
    `Nat.modEq_digits_sum` (which needs `b ≡ 1 mod d`).

    Specializing `b = 10, d = 11` recovers `Nat.modEq_eleven_digits_sum`. -/
theorem modEq_alternating_digits (d b : ℕ) (h : (d : ℤ) ∣ (b : ℤ) + 1) (n : ℕ) :
    (n : ℤ) ≡ altDigitSum b n [ZMOD (d : ℤ)] := by
  have hmod : (b : ℤ) ≡ -1 [ZMOD (d : ℤ)] := by
    rw [Int.modEq_iff_dvd]
    have : (-1 : ℤ) - (b : ℤ) = -((b : ℤ) + 1) := by ring
    rw [this]
    exact (dvd_neg).mpr h
  have t := Nat.zmodeq_ofDigits_digits d b (-1 : ℤ) hmod n
  rwa [Nat.ofDigits_neg_one] at t

/-- **General casting-out (alternating form), divisibility test version.**

    If `d ∣ b + 1`, then `d ∣ n` iff `d` divides the alternating sum of the
    base-`b` digits of `n`. Dual of `Nat.dvd_iff_dvd_digits_sum`. -/
theorem dvd_iff_dvd_alternating_digits (d b : ℕ) (h : (d : ℤ) ∣ (b : ℤ) + 1) (n : ℕ) :
    d ∣ n ↔ (d : ℤ) ∣ altDigitSum b n := by
  have hd : (d : ℤ) ∣ (b : ℤ) - (-1 : ℤ) := by
    have : (b : ℤ) - (-1 : ℤ) = (b : ℤ) + 1 := by ring
    rw [this]; exact h
  have t := Nat.dvd_iff_dvd_ofDigits d b (-1 : ℤ) hd n
  rwa [Nat.ofDigits_neg_one] at t

/-- **Universal corollary.** For *every* base `b ≥ 2`, the number `b + 1` divides
    `n` exactly when it divides the alternating sum of the base-`b` digits of `n`.

    This is the "one free divisor" every positional system carries: base 10 gives
    the classical divisibility-by-11 rule, base 2 gives divisibility by 3, base 16
    gives divisibility by 17, etc. No coprimality or primality hypothesis is
    needed — it holds because `(b+1) ∣ (b+1)` tautologically. -/
theorem dvd_succ_base_iff_alternating (b n : ℕ) :
    (b + 1) ∣ n ↔ ((b : ℤ) + 1) ∣ altDigitSum b n := by
  have h : ((b + 1 : ℕ) : ℤ) ∣ (b : ℤ) + 1 := by push_cast; exact dvd_refl _
  have := dvd_iff_dvd_alternating_digits (b + 1) b h n
  rwa [show ((b + 1 : ℕ) : ℤ) = (b : ℤ) + 1 by push_cast; ring] at this

-- ============================================================
-- Part II: Classical and new instances
-- ============================================================

/-- **Divisibility by 11** (base 10) — recovers `Nat.eleven_dvd_iff`. -/
theorem eleven_dvd_iff_alt (n : ℕ) :
    11 ∣ n ↔ (11 : ℤ) ∣ altDigitSum 10 n :=
  dvd_iff_dvd_alternating_digits 11 10 (by norm_num) n

/-- **Divisibility by 101** via alternating two-digit (base-100) groups.
    Here `101 ∣ 100 + 1`. -/
theorem onehundredone_dvd_iff_alt (n : ℕ) :
    101 ∣ n ↔ (101 : ℤ) ∣ altDigitSum 100 n :=
  dvd_iff_dvd_alternating_digits 101 100 (by norm_num) n

-- The next four all ride on 1001 = 7·11·13, i.e. 1000 ≡ -1 (mod 7, 11, 13, 1001).
-- This is the classical "alternating three-digit groups" test.

/-- **Divisibility by 7** via alternating three-digit (base-1000) groups. -/
theorem seven_dvd_iff_alt_base1000 (n : ℕ) :
    7 ∣ n ↔ (7 : ℤ) ∣ altDigitSum 1000 n :=
  dvd_iff_dvd_alternating_digits 7 1000 (by norm_num) n

/-- **Divisibility by 11** via alternating three-digit (base-1000) groups. -/
theorem eleven_dvd_iff_alt_base1000 (n : ℕ) :
    11 ∣ n ↔ (11 : ℤ) ∣ altDigitSum 1000 n :=
  dvd_iff_dvd_alternating_digits 11 1000 (by norm_num) n

/-- **Divisibility by 13** via alternating three-digit (base-1000) groups. -/
theorem thirteen_dvd_iff_alt_base1000 (n : ℕ) :
    13 ∣ n ↔ (13 : ℤ) ∣ altDigitSum 1000 n :=
  dvd_iff_dvd_alternating_digits 13 1000 (by norm_num) n

/-- **Divisibility by 1001** via alternating three-digit (base-1000) groups. -/
theorem tenohone_dvd_iff_alt_base1000 (n : ℕ) :
    1001 ∣ n ↔ (1001 : ℤ) ∣ altDigitSum 1000 n :=
  dvd_iff_dvd_alternating_digits 1001 1000 (by norm_num) n

/-- **Divisibility by 3 in binary**: `2 ≡ -1 (mod 3)`, so `3 ∣ n` iff `3` divides
    the alternating sum of the *bits* of `n`. (Instance of the universal corollary
    with `b = 2`.) -/
theorem three_dvd_iff_alt_binary (n : ℕ) :
    3 ∣ n ↔ (3 : ℤ) ∣ altDigitSum 2 n :=
  dvd_iff_dvd_alternating_digits 3 2 (by norm_num) n

/-- **Divisibility by 17 in hexadecimal**: `16 ≡ -1 (mod 17)`. -/
theorem seventeen_dvd_iff_alt_hex (n : ℕ) :
    17 ∣ n ↔ (17 : ℤ) ∣ altDigitSum 16 n :=
  dvd_iff_dvd_alternating_digits 17 16 (by norm_num) n

-- ============================================================
-- Part III: Congruence (casting-out) instances
-- ============================================================

/-- Casting out elevens: `n ≡ altDigitSum₁₀(n) (mod 11)`. -/
theorem casting_out_elevens (n : ℕ) :
    (n : ℤ) ≡ altDigitSum 10 n [ZMOD 11] :=
  modEq_alternating_digits 11 10 (by norm_num) n

/-- Alternating three-digit groups mod 7 (base 1000): `n ≡ altDigitSum₁₀₀₀(n) (mod 7)`. -/
theorem casting_out_sevens_base1000 (n : ℕ) :
    (n : ℤ) ≡ altDigitSum 1000 n [ZMOD 7] :=
  modEq_alternating_digits 7 1000 (by norm_num) n

-- ============================================================
-- Part IV: Numerical verification
-- ============================================================

-- 1001 = 7·11·13 is the arithmetic behind the base-1000 alternating test.
example : 1001 = 7 * 11 * 13 := by norm_num
example : (1000 : ℤ) + 1 = 1001 := by norm_num

-- Concrete divisibility checks.
example : 11 ∣ 121 := by decide
example : 11 ∣ 1001 := by decide
example : 7 ∣ 1001 := by decide
example : 13 ∣ 1001 := by decide
example : 101 ∣ 10201 := by decide

-- The alternating base-1000 digit sum of 1_002_001 is 1 - 2 + 1 = 0, so it is
-- divisible by 7, 11, 13 and 1001 simultaneously.
example : altDigitSum 1000 1002001 = 0 := by native_decide
example : 1001 ∣ 1002001 := by decide

-- Alternating decimal digit sum of 1331 is 1 - 3 + 3 - 1 = 0 ⇒ divisible by 11.
example : altDigitSum 10 1331 = 0 := by native_decide
example : 11 ∣ 1331 := by decide

-- ============================================================
-- Part V: Master summary theorem
-- ============================================================

/-- Master statement collecting the alternating digit-sum divisibility tests
    proved in this extension, alongside the universal corollary. -/
theorem alternating_digit_rules_summary :
    -- Universal: every base carries a free divisor b+1
    (∀ (b n : ℕ), (b + 1) ∣ n ↔ ((b : ℤ) + 1) ∣ altDigitSum b n) ∧
    -- Classical base-10 rule for 11
    (∀ n, 11 ∣ n ↔ (11 : ℤ) ∣ altDigitSum 10 n) ∧
    -- Base-100 rule for 101
    (∀ n, 101 ∣ n ↔ (101 : ℤ) ∣ altDigitSum 100 n) ∧
    -- Base-1000 alternating group tests (1001 = 7·11·13)
    (∀ n, 7 ∣ n ↔ (7 : ℤ) ∣ altDigitSum 1000 n) ∧
    (∀ n, 11 ∣ n ↔ (11 : ℤ) ∣ altDigitSum 1000 n) ∧
    (∀ n, 13 ∣ n ↔ (13 : ℤ) ∣ altDigitSum 1000 n) ∧
    (∀ n, 1001 ∣ n ↔ (1001 : ℤ) ∣ altDigitSum 1000 n) := by
  refine ⟨dvd_succ_base_iff_alternating, eleven_dvd_iff_alt, onehundredone_dvd_iff_alt,
    seven_dvd_iff_alt_base1000, eleven_dvd_iff_alt_base1000, thirteen_dvd_iff_alt_base1000,
    tenohone_dvd_iff_alt_base1000⟩

end DivisibilityByThreeOQ01OQ03

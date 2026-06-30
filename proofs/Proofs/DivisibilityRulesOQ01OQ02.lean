/-
Universal Power-of-10 Bases for Digit-Sum Divisibility Rules (OQ-01-OQ-02 Extension)

Extension of `divisibility-rules-oq-01`. The parent file proves digit-sum
divisibility rules for a hand-picked list of moduli (3, 9, 37, 27, 999, 99, 101,
...), each paired with an ad hoc base in which `base ≡ 1 (mod d)`. This file
resolves the open question by proving the **universal** statement:

  For EVERY modulus `d` coprime to 10 there exists a power-of-10 base `B = 10^k`
  (with `k > 0`) for which the digit-sum rule holds:
        `d ∣ n  ↔  d ∣ (digits (10^k) n).sum`   for all `n`.

The witness is `k = φ(d)` (Fermat–Euler: `10^φ(d) ≡ 1 (mod d)`), and more sharply
the set of *valid* exponents is exactly the multiples of the multiplicative order
`ord_d(10) = orderOf (10 : ZMod d)`, whose value is the minimal positive valid
exponent (so `10^{ord_d(10)}` is the smallest power-of-10 base that works).

This single theorem subsumes every digit-sum instance in the parent and yields
new ones the parent could only obtain by ad hoc truncation: e.g. genuine
base-`10^6` digit-sum rules for 7 and 13 (the parent handled 7 only via octal /
truncation and 13 only via truncation).

The original problem statement phrases the goal as exhibiting a base `B` with the
digit-sum *or* alternating-digit-sum rule; since the digit-sum rule is available
for every coprime `d`, that disjunction is settled in full by the digit-sum
branch below. (The alternating analogue, which needs `-1` to be a power of `10`
mod `d`, is the parent's `modEq_alternating_digits_sum`; it is not universal.)

The file is self-contained and imports only Mathlib.

Tags: number-theory, modular-arithmetic, divisibility, Euler's theorem, order, extension
-/

import Mathlib

open Nat

namespace DivisibilityRulesOQ01OQ02

/-
## Part I: The general digit-sum rule from `10^k ≡ 1 (mod d)`
-/

/-- **Workhorse lemma.** Whenever `10^k ≡ 1 (mod d)` with `d ≥ 2`, the base
`B = 10^k` validates the digit-sum divisibility rule for `d`: a number is
divisible by `d` iff the sum of its base-`10^k` digits is. -/
theorem digitSum_rule_of_modEq_one (d k : ℕ) (hd : 2 ≤ d)
    (hk : 10 ^ k ≡ 1 [MOD d]) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits (10 ^ k) n).sum := by
  have hb : 10 ^ k % d = 1 := by
    have h2 : 10 ^ k % d = 1 % d := hk
    rwa [Nat.mod_eq_of_lt (show 1 < d by omega)] at h2
  exact (Nat.modEq_digits_sum d (10 ^ k) hb n).dvd_iff (dvd_refl d)

/-- **Main theorem (resolves the open question).** For every modulus `d ≥ 2`
coprime to 10 there is a positive exponent `k` such that the power-of-10 base
`B = 10^k` gives a valid digit-sum divisibility rule for `d`. The witness is
`k = φ(d)` via the Fermat–Euler theorem. -/
theorem exists_pow_ten_digitSum_rule (d : ℕ) (hd : 2 ≤ d)
    (hcop : Nat.Coprime 10 d) :
    ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, d ∣ n ↔ d ∣ (Nat.digits (10 ^ k) n).sum :=
  ⟨d.totient, Nat.totient_pos.mpr (by omega), fun n =>
    digitSum_rule_of_modEq_one d d.totient hd (Nat.ModEq.pow_totient hcop) n⟩

/-- Explicit form of the main theorem: the base `10^φ(d)` always works. -/
theorem digitSum_rule_pow_totient (d : ℕ) (hd : 2 ≤ d) (hcop : Nat.Coprime 10 d)
    (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits (10 ^ d.totient) n).sum :=
  digitSum_rule_of_modEq_one d d.totient hd (Nat.ModEq.pow_totient hcop) n

/-
## Part II: Sharp characterization via the multiplicative order

The exponents `k` for which `10^k ≡ 1 (mod d)` are exactly the multiples of
`ord_d(10) = orderOf (10 : ZMod d)`. Hence the *minimal* power-of-10 base giving
a digit-sum rule is `10^{ord_d(10)}`, and every valid base is a power of it.
-/

/-- A power of 10 is `≡ 1 (mod d)` exactly when the multiplicative order of `10`
in `ZMod d` divides the exponent. -/
theorem pow_modEq_one_iff_order_dvd (d k : ℕ) :
    10 ^ k ≡ 1 [MOD d] ↔ orderOf (10 : ZMod d) ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one]
  rw [show ((10 : ZMod d) ^ k) = ((10 ^ k : ℕ) : ZMod d) by push_cast; ring]
  rw [show (1 : ZMod d) = ((1 : ℕ) : ZMod d) by push_cast; ring]
  rw [ZMod.natCast_eq_natCast_iff]

/-- For `d ≥ 2` coprime to 10 the order of 10 in `ZMod d` is positive
(10 is a unit of the finite ring `ZMod d`). -/
theorem orderOf_ten_pos (d : ℕ) (hd : 2 ≤ d) (hcop : Nat.Coprime 10 d) :
    0 < orderOf (10 : ZMod d) := by
  have hdvd : orderOf (10 : ZMod d) ∣ d.totient :=
    (pow_modEq_one_iff_order_dvd d d.totient).mp (Nat.ModEq.pow_totient hcop)
  have hφ : 0 < d.totient := Nat.totient_pos.mpr (by omega)
  rcases Nat.eq_zero_or_pos (orderOf (10 : ZMod d)) with h | h
  · rw [h] at hdvd
    simp only [Nat.zero_dvd] at hdvd
    omega
  · exact h

/-- **Sharpness.** `ord_d(10)` is the least positive exponent giving a valid
power-of-10 digit-sum base: it is positive, itself valid, and bounds below every
positive valid exponent. -/
theorem orderOf_least_valid_exponent (d : ℕ) (hd : 2 ≤ d)
    (hcop : Nat.Coprime 10 d) :
    0 < orderOf (10 : ZMod d) ∧
    10 ^ orderOf (10 : ZMod d) ≡ 1 [MOD d] ∧
    ∀ k, 0 < k → 10 ^ k ≡ 1 [MOD d] → orderOf (10 : ZMod d) ≤ k := by
  refine ⟨orderOf_ten_pos d hd hcop, ?_, ?_⟩
  · exact (pow_modEq_one_iff_order_dvd d _).mpr dvd_rfl
  · intro k hk hmod
    exact Nat.le_of_dvd hk ((pow_modEq_one_iff_order_dvd d k).mp hmod)

/-- The minimal valid base validates the digit-sum rule: `10^{ord_d(10)}` works.
(For `d` coprime to 10 this base is `≠ 1` since then `ord_d(10) > 0`; see
`orderOf_least_valid_exponent`. The statement itself needs only `d ≥ 2`.) -/
theorem minimal_pow_ten_digitSum_rule (d : ℕ) (hd : 2 ≤ d) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits (10 ^ orderOf (10 : ZMod d)) n).sum :=
  digitSum_rule_of_modEq_one d _ hd
    ((pow_modEq_one_iff_order_dvd d _).mpr dvd_rfl) n

/-
## Part III: Concrete instances recovered from the general theorems

These rules follow purely as corollaries of `digitSum_rule_of_modEq_one`;
several (7, 13 in base `10^6`) are *new* — the parent only obtained 7 and 13 by
truncation / a different base.
-/

/-- Divisibility by 3 via base `10^1` (parent's `three_dvd_iff`, k = 1). -/
theorem three_dvd_digitSum (n : ℕ) :
    3 ∣ n ↔ 3 ∣ (Nat.digits (10 ^ 1) n).sum :=
  digitSum_rule_of_modEq_one 3 1 (by norm_num) (by decide) n

/-- Divisibility by 7 via base `10^6` (`ord_7(10) = 6`). New: parent only had 7
via truncation / octal, not a base-10 digit-sum rule. -/
theorem seven_dvd_digitSum (n : ℕ) :
    7 ∣ n ↔ 7 ∣ (Nat.digits (10 ^ 6) n).sum :=
  digitSum_rule_of_modEq_one 7 6 (by norm_num) (by decide) n

/-- Divisibility by 13 via base `10^6` (`ord_13(10) = 6`). New: parent only had
13 via truncation. -/
theorem thirteen_dvd_digitSum (n : ℕ) :
    13 ∣ n ↔ 13 ∣ (Nat.digits (10 ^ 6) n).sum :=
  digitSum_rule_of_modEq_one 13 6 (by norm_num) (by decide) n

/-- Divisibility by 27 via base `10^3` (`ord_27(10) = 3`; cf. parent's
`twentyseven_dvd_iff` which uses base 1000 = 10^3). -/
theorem twentyseven_dvd_digitSum (n : ℕ) :
    27 ∣ n ↔ 27 ∣ (Nat.digits (10 ^ 3) n).sum :=
  digitSum_rule_of_modEq_one 27 3 (by norm_num) (by decide) n

/-- Divisibility by 37 via base `10^3` (`ord_37(10) = 3`). -/
theorem thirtyseven_dvd_digitSum (n : ℕ) :
    37 ∣ n ↔ 37 ∣ (Nat.digits (10 ^ 3) n).sum :=
  digitSum_rule_of_modEq_one 37 3 (by norm_num) (by decide) n

/-
## Part IV: Numerical sanity checks

(`Nat.digits` and `orderOf` are not kernel-reducible by `decide`, so the checks
below exercise the underlying modular facts that drive the rules instead.)
-/

-- `ord_7(10) ∣ 6`, so `10^6` is a valid digit-sum base for 7.
example : orderOf (10 : ZMod 7) ∣ 6 := (pow_modEq_one_iff_order_dvd 7 6).mp (by decide)
-- `ord_13(10) ∣ 6`, so `10^6` is a valid digit-sum base for 13.
example : orderOf (10 : ZMod 13) ∣ 6 := (pow_modEq_one_iff_order_dvd 13 6).mp (by decide)
-- `10^3 ≢ 1 (mod 7)`: a base `10^3` is too small to validate the rule for 7.
example : ¬ (10 ^ 3 ≡ 1 [MOD 7]) := by decide
-- `10^6 ≡ 1 (mod 13)`: the modular fact behind the base-`10^6` rule for 13.
example : 10 ^ 6 ≡ 1 [MOD 13] := by decide

#check @exists_pow_ten_digitSum_rule
#check @digitSum_rule_pow_totient
#check @pow_modEq_one_iff_order_dvd
#check @orderOf_least_valid_exponent
#check @minimal_pow_ten_digitSum_rule

end DivisibilityRulesOQ01OQ02

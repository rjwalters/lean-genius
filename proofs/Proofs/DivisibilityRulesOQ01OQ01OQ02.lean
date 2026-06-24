/-
# Base-b Divisibility Rule for Moduli Coprime to the Base

OQ-02 follow-up to DivisibilityRulesOQ01OQ01 (divisibility-rules-oq-01-oq-01).

The parent proof established, **in base 10**, that every `d > 1` coprime to `10`
admits a digit-sum divisibility rule: there is some `k > 0` with

  d ∣ n ↔ d ∣ (sum of the base-`10^k` digits of n).

The argument was entirely base-agnostic — it only used that `10` is a unit
modulo `d`, so that Euler's theorem forces `10^φ(d) ≡ 1 (mod d)`.  This file
makes that observation explicit and proves the rule for an **arbitrary base**
`b ≥ 2` coprime to `d`:

  ∀ b ≥ 2, ∀ d > 1 with gcd(d, b) = 1, ∃ k > 0 such that
    d ∣ n ↔ d ∣ (sum of digits of n in base b^k).

The base-10 parent is recovered as the special case `b = 10`.

## Proof Strategy

For any unit `u` in `(ZMod d)ˣ`, Euler's theorem (`ZMod.pow_totient`) gives
`u^φ(d) = 1`.  Taking `u = ZMod.unitOfCoprime b hcop.symm`, whose coercion is
`(b : ZMod d)`, yields `(b : ZMod d)^φ(d) = 1`, i.e. `b^φ(d) ≡ 1 (mod d)`.
Then `Nat.modEq_digits_sum` (working in base `b^φ(d)`) delivers the digit-sum
rule.  None of these steps depends on the value `10`.

## Results

1. `pow_totient_mod_eq_one` — Euler's theorem in `ℕ` form:
   `b^φ(d) % d = 1` whenever `1 < d` and `gcd(d, b) = 1` (any base `b`).
2. `general_base_divisibility_rule_exists` — the headline generalization:
   a digit-sum rule in base `b^k` exists for every base `b ≥ 2` and every
   `d > 1` coprime to `b`.
3. `general_divisibility_rule_base_ten` — the base-10 parent recovered as a
   corollary (`b = 10`).

## Tags
number-theory, divisibility, modular-arithmetic, multiplicative-order,
Euler-theorem, generalization
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace DivisibilityRulesOQ01OQ01OQ02

open Nat BigOperators

/-! ## Euler's theorem gives `b^φ(d) ≡ 1 (mod d)` for any base coprime to `d` -/

/-- **Euler's theorem, `ℕ` form.** When `gcd(d, b) = 1` and `d > 1`,
`b^φ(d) % d = 1`.  This is the base-agnostic engine of every digit-sum
divisibility rule: it generalizes the parent's `10^φ(d) % d = 1`. -/
theorem pow_totient_mod_eq_one {d b : ℕ} (hd : 1 < d) (hcop : Nat.Coprime d b) :
    b ^ d.totient % d = 1 := by
  -- `ZMod.pow_totient` needs `NeZero d`.
  haveI hne : NeZero d := ⟨by omega⟩
  -- View `b` as a unit of `ZMod d`.
  let u := ZMod.unitOfCoprime b hcop.symm
  -- Euler's theorem in the unit group: `u^φ(d) = 1`.
  have hpow_unit : u ^ d.totient = 1 := ZMod.pow_totient u
  -- Push down to `ZMod d`: `(u : ZMod d)^φ(d) = 1`.
  have hpow : (u : ZMod d) ^ d.totient = 1 := by
    have := congr_arg Units.val hpow_unit
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    exact this
  -- The unit's coercion is exactly `(b : ZMod d)`.
  have hcoe : (u : ZMod d) = b := by
    simp [u, ZMod.unitOfCoprime]
  rw [hcoe] at hpow
  -- Lift back to a `ℕ` congruence `b^φ(d) ≡ 1 [MOD d]`.
  have hmod : ((b ^ d.totient : ℕ) : ZMod d) = ((1 : ℕ) : ZMod d) := by
    push_cast; exact hpow
  rw [ZMod.natCast_eq_natCast_iff] at hmod
  -- `1 % d = 1` since `d > 1`.
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hd] at hmod
  exact hmod

/-! ## Main Theorem: General Base-b Divisibility Rule Existence -/

/-- **General base-`b` divisibility rule.** For every base `b ≥ 2` and every
`d > 1` coprime to `b`, there exists `k > 0` such that `d ∣ n` iff `d` divides
the sum of the base-`b^k` digits of `n`.

The choice `k = φ(d)` always works: `b^φ(d) ≡ 1 (mod d)` by Euler's theorem
(`pow_totient_mod_eq_one`), and `Nat.modEq_digits_sum` turns this into the
digit-sum rule.  Taking `b = 10` recovers the classical decimal rule. -/
theorem general_base_divisibility_rule_exists {b d : ℕ} (_hb : 2 ≤ b) (hd : 1 < d)
    (hcop : Nat.Coprime d b) :
    ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, d ∣ n ↔ d ∣ (Nat.digits (b ^ k) n).sum := by
  refine ⟨d.totient, Nat.totient_pos.mpr (by omega), fun n => ?_⟩
  exact Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum d (b ^ d.totient) (pow_totient_mod_eq_one hd hcop) n)
    (dvd_refl d)

/-! ## The base-10 parent recovered as a corollary -/

/-- **Parent recovered (`b = 10`).** Specializing the general theorem to base
`10` reproduces `DivisibilityRulesOQ01OQ01.general_divisibility_rule_exists`:
every `d > 1` coprime to `10` has a decimal digit-sum rule. -/
theorem general_divisibility_rule_base_ten {d : ℕ} (hd : 1 < d)
    (hcop : Nat.Coprime d 10) :
    ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, d ∣ n ↔ d ∣ (Nat.digits (10 ^ k) n).sum :=
  general_base_divisibility_rule_exists (by norm_num) hd hcop

/-! ## Explicit witnesses across several bases -/

/-- Base 2, modulus 3: `2^2 = 4 ≡ 1 (mod 3)`, so `k = 2` works. -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 3 ∣ n ↔ 3 ∣ (Nat.digits (2 ^ k) n).sum :=
  ⟨2, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 3 (2 ^ 2) (by decide) n) (dvd_refl 3)⟩

/-- Base 7, modulus 4: `gcd(4,7)=1` and `7^2 = 49 ≡ 1 (mod 4)`, so `k = 2`
works (note `7 ≡ 3 (mod 4)`, so the single-digit `k = 1` rule fails). -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 4 ∣ n ↔ 4 ∣ (Nat.digits (7 ^ k) n).sum :=
  ⟨2, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 4 (7 ^ 2) (by decide) n) (dvd_refl 4)⟩

/-- Base 16, modulus 5: `16 ≡ 1 (mod 5)`, so `k = 1` works — the hexadecimal
analogue of casting out nines. -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 5 ∣ n ↔ 5 ∣ (Nat.digits (16 ^ k) n).sum :=
  ⟨1, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 5 (16 ^ 1) (by decide) n) (dvd_refl 5)⟩

#check @general_base_divisibility_rule_exists

end DivisibilityRulesOQ01OQ01OQ02

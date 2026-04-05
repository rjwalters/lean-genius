/-
# General Divisibility Rule for Any d Coprime to 10

OQ-01 follow-up to DivisibilityRulesOQ01 (divisibility-rules-oq-01).

The parent proof showed digit sum rules for specific d (3, 9, 11, 37, ...).
This proof establishes the **existence** of such a rule for every d coprime to 10:

  ∀ d > 1 with gcd(d, 10) = 1, ∃ k > 0 such that
    d ∣ n ↔ d ∣ (sum of digits of n in base 10^k)

## Proof Strategy

By Euler's theorem (ZMod.pow_totient), for any unit u in (ZMod d)ˣ,
u^φ(d) = 1. Taking u = ZMod.unitOfCoprime 10 (hcop.symm), whose
coercion is (10 : ZMod d), gives (10 : ZMod d)^φ(d) = 1, i.e.,
10^φ(d) ≡ 1 (mod d). Then Nat.modEq_digits_sum gives the digit sum rule.

## Tags
number-theory, divisibility, modular-arithmetic, Euler-theorem, generalization
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Units
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace DivisibilityRulesOQ01OQ01

open Nat BigOperators

/-! ## Euler's theorem gives 10^φ(d) ≡ 1 (mod d) -/

/-- When gcd(d, 10) = 1 and d > 1, 10^φ(d) % d = 1 (Euler's theorem). -/
theorem ten_pow_totient_mod_eq_one {d : ℕ} (hd : 1 < d) (hcop : Nat.Coprime d 10) :
    10 ^ d.totient % d = 1 := by
  -- Provide NeZero instance needed by ZMod.pow_totient
  haveI hne : NeZero d := ⟨by omega⟩
  -- Construct 10 as a unit in ZMod d
  let u := ZMod.unitOfCoprime 10 hcop.symm
  -- Euler's theorem: u^φ(d) = 1 in (ZMod d)ˣ
  have hpow_unit : u ^ d.totient = 1 := ZMod.pow_totient u
  -- Coerce to ZMod d: (u : ZMod d)^φ(d) = 1
  have hpow : (u : ZMod d) ^ d.totient = 1 := by
    have := congr_arg Units.val hpow_unit
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    exact this
  -- The coercion of ZMod.unitOfCoprime 10 equals (10 : ZMod d)
  have hcoe : (u : ZMod d) = 10 := by
    simp [u, ZMod.unitOfCoprime]
  -- So (10 : ZMod d)^φ(d) = 1
  rw [hcoe] at hpow
  -- Cast back to ℕ arithmetic: 10^φ(d) ≡ 1 [MOD d]
  have hmod : ((10 ^ d.totient : ℕ) : ZMod d) = ((1 : ℕ) : ZMod d) := by
    push_cast; exact hpow
  rw [ZMod.natCast_eq_natCast_iff] at hmod
  -- hmod : 10^φ(d) ≡ 1 [MOD d], unfolds to 10^φ(d) % d = 1 % d; simplify 1 % d = 1
  simp only [Nat.ModEq, Nat.mod_eq_of_lt hd] at hmod
  exact hmod

/-! ## Main Theorem: General Divisibility Rule Existence -/

/-- **General Divisibility Rule Theorem**: For any d > 1 coprime to 10,
there exists k > 0 such that d ∣ n ↔ d ∣ (sum of digits of n in base 10^k).

Choosing k = φ(d) always works: 10^φ(d) ≡ 1 (mod d) by Euler's theorem. -/
theorem general_divisibility_rule_exists {d : ℕ} (hd : 1 < d) (hcop : Nat.Coprime d 10) :
    ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, d ∣ n ↔ d ∣ (Nat.digits (10 ^ k) n).sum := by
  refine ⟨d.totient, Nat.totient_pos.mpr (by omega), fun n => ?_⟩
  exact Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum d (10 ^ d.totient) (ten_pow_totient_mod_eq_one hd hcop) n)
    (dvd_refl d)

/-! ## Explicit witnesses for common moduli -/

/-- For d = 3: k = 1 works (10 ≡ 1 mod 3). -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 3 ∣ n ↔ 3 ∣ (Nat.digits (10 ^ k) n).sum :=
  ⟨1, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 3 10 (by native_decide) n) (dvd_refl 3)⟩

/-- For d = 7: k = 6 works (10^6 ≡ 1 mod 7). -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 7 ∣ n ↔ 7 ∣ (Nat.digits (10 ^ k) n).sum :=
  ⟨6, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 7 1000000 (by native_decide) n) (dvd_refl 7)⟩

/-- For d = 11: k = 2 works (100 ≡ 1 mod 11). -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 11 ∣ n ↔ 11 ∣ (Nat.digits (10 ^ k) n).sum :=
  ⟨2, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 11 100 (by native_decide) n) (dvd_refl 11)⟩

/-- For d = 13: k = 6 works (10^6 ≡ 1 mod 13). -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 13 ∣ n ↔ 13 ∣ (Nat.digits (10 ^ k) n).sum :=
  ⟨6, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 13 1000000 (by native_decide) n) (dvd_refl 13)⟩

/-- For d = 37: k = 3 works (1000 ≡ 1 mod 37). -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 37 ∣ n ↔ 37 ∣ (Nat.digits (10 ^ k) n).sum :=
  ⟨3, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 37 1000 (by native_decide) n) (dvd_refl 37)⟩

/-- For d = 41: k = 5 works (10^5 ≡ 1 mod 41). -/
example : ∃ k : ℕ, 0 < k ∧ ∀ n : ℕ, 41 ∣ n ↔ 41 ∣ (Nat.digits (10 ^ k) n).sum :=
  ⟨5, by omega, fun n => Nat.ModEq.dvd_iff
    (Nat.modEq_digits_sum 41 100000 (by native_decide) n) (dvd_refl 41)⟩

#check @general_divisibility_rule_exists

end DivisibilityRulesOQ01OQ01

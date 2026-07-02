/-
# Carmichael's λ(n): the least universal exponent of (ℤ/nℤ)ˣ

Euler's theorem gives, for every unit `a` of `ZMod n`, the identity `a ^ φ(n) = 1`;
equivalently the multiplicative order of any unit divides `φ(n)` (proved in the
parent entry `euler-totient-oq-05` as `orderOf_dvd_totient`). But `φ(n)` is in
general *not* the smallest exponent that annihilates every unit simultaneously.
The *least* such exponent is **Carmichael's function** `λ(n)`, defined here as the
exponent of the group `(ZMod n)ˣ`.

This entry answers the open question left by the parent
(`euler-totient-oq-05`, openQuestions[1]):

  > Formalize the converse refinement: Carmichael's λ(n) is the exact (least)
  > universal exponent, sharpening `orderOf u ∣ φ(n)`.

We prove:

* `pow_carmichael`      — `λ(n)` is a universal exponent: `a ^ λ(n) = 1` for every unit `a`.
* `carmichael_dvd_iff`  — the universal exponents are *exactly* the multiples of `λ(n)`.
* `carmichael_isLeast`  — `λ(n)` is the least positive universal exponent (the headline).
* `order_dvd_carmichael`— every unit's order divides `λ(n)`.
* `carmichael_dvd_totient` — `λ(n) ∣ φ(n)`, so `λ` refines Euler's exponent.
* `orderOf_dvd_totient` — the parent divisibility factors through `λ`: `ord(a) ∣ λ(n) ∣ φ(n)`.
* `carmichael_eq_arithmeticFunction` — agreement with Mathlib's `ArithmeticFunction.Carmichael`.

Finally, the concrete gap `n = 8`: every unit satisfies `a² = 1`, so `λ(8) = 2`,
strictly below `φ(8) = 4`. Hence Euler's exponent `φ(n)` is genuinely non-minimal
(`euler_exponent_not_minimal`), and `λ` is the sharp replacement.

All results are machine-checked with no axioms; the `ZMod 8` computations use
`decide` (no `native_decide`), so there is no `Lean.ofReduceBool` dependency.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.GroupTheory.Exponent
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace EulerTotientOQ0502

open Monoid

/-- **Carmichael's function** `λ(n)`, defined as the exponent of the unit group
`(ZMod n)ˣ`: the smallest `N` with `a ^ N = 1` for every unit `a` (see
`carmichael_isLeast`). -/
noncomputable def carmichaelLambda (n : ℕ) : ℕ := Monoid.exponent (ZMod n)ˣ

/-- `λ(n)` is a *universal exponent*: every unit of `ZMod n` is annihilated by it.
This is Euler's `a ^ φ(n) = 1` with `φ(n)` replaced by the smaller `λ(n)`. -/
theorem pow_carmichael {n : ℕ} (a : (ZMod n)ˣ) : a ^ carmichaelLambda n = 1 :=
  Monoid.pow_exponent_eq_one a

/-- The universal exponents of `(ZMod n)ˣ` are *exactly* the multiples of `λ(n)`:
`λ(n) ∣ N` iff `a ^ N = 1` for every unit `a`. -/
theorem carmichael_dvd_iff {n N : ℕ} :
    carmichaelLambda n ∣ N ↔ ∀ a : (ZMod n)ˣ, a ^ N = 1 :=
  Monoid.exponent_dvd_iff_forall_pow_eq_one

/-- For `n ≠ 0` the unit group is finite, so `λ(n)` is positive. -/
theorem carmichael_pos (n : ℕ) [NeZero n] : 0 < carmichaelLambda n :=
  Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite

/-- **Carmichael's λ(n) is the least universal exponent.** Among all positive `N`
with `a ^ N = 1` for every unit `a`, `λ(n)` is the minimum: it is itself such an
exponent (`pow_carmichael`), and it divides — hence is `≤` — any other one. This is
the exact sharpening of the parent's `orderOf u ∣ φ(n)`. -/
theorem carmichael_isLeast (n : ℕ) [NeZero n] :
    IsLeast {N | 0 < N ∧ ∀ a : (ZMod n)ˣ, a ^ N = 1} (carmichaelLambda n) := by
  refine ⟨⟨carmichael_pos n, fun a => pow_carmichael a⟩, ?_⟩
  rintro N ⟨hN, hall⟩
  exact Nat.le_of_dvd hN (carmichael_dvd_iff.mpr hall)

/-- Every unit's multiplicative order divides `λ(n)`. Combined with
`carmichael_dvd_totient` this recovers the parent's `orderOf u ∣ φ(n)`. -/
theorem order_dvd_carmichael {n : ℕ} (a : (ZMod n)ˣ) :
    orderOf a ∣ carmichaelLambda n :=
  Monoid.order_dvd_exponent a

/-- **`λ(n) ∣ φ(n)`**: Carmichael's exponent divides Euler's, since `λ(n)` is the
exponent of a group of order `φ(n) = |(ZMod n)ˣ|`. This is the divisibility that
makes `λ` a refinement of `φ` rather than an unrelated quantity. -/
theorem carmichael_dvd_totient (n : ℕ) [NeZero n] :
    carmichaelLambda n ∣ n.totient := by
  have h := Group.exponent_dvd_card (G := (ZMod n)ˣ)
  rwa [ZMod.card_units_eq_totient] at h

/-- The parent divisibility `orderOf u ∣ φ(n)` factors through `λ(n)`:
`orderOf a ∣ λ(n) ∣ φ(n)`. -/
theorem orderOf_dvd_totient (n : ℕ) [NeZero n] (a : (ZMod n)ˣ) :
    orderOf a ∣ n.totient :=
  (order_dvd_carmichael a).trans (carmichael_dvd_totient n)

/-- Agreement with Mathlib's official arithmetic function `ArithmeticFunction.Carmichael`:
our `λ(n)` is exactly that value for `n ≠ 0`. -/
theorem carmichael_eq_arithmeticFunction (n : ℕ) [NeZero n] :
    carmichaelLambda n = ArithmeticFunction.Carmichael n :=
  (ArithmeticFunction.carmichael_eq_exponent' n).symm

/-! ## The gap at `n = 8`: `λ(8) = 2 < 4 = φ(8)`

The group `(ZMod 8)ˣ ≅ ℤ/2 × ℤ/2` is elementary abelian of exponent `2`, so every
unit already squares to `1`. Thus Carmichael's `λ(8) = 2` is strictly smaller than
Euler's exponent `φ(8) = 4`: Euler's theorem is not sharp, and `λ` is the sharp bound.
-/

/-- Every unit of `ZMod 8` squares to `1` — a finite check over the four units. -/
theorem sq_eq_one_zmod_eight : ∀ a : (ZMod 8)ˣ, a ^ 2 = 1 := by decide

/-- `φ(8) = 4`. -/
theorem totient_eight : Nat.totient 8 = 4 := by decide

/-- `λ(8) = 2`. Upper bound: `a² = 1` for all units gives `λ(8) ∣ 2`. Lower bound:
`λ(8) ≠ 1` because some unit (e.g. `3`) is not the identity, so it cannot have
exponent `1`. With `0 < λ(8) ≤ 2` and `λ(8) ≠ 1`, we get `λ(8) = 2`. -/
theorem carmichael_eight : carmichaelLambda 8 = 2 := by
  have hdvd : carmichaelLambda 8 ∣ 2 := carmichael_dvd_iff.mpr sq_eq_one_zmod_eight
  have hle : carmichaelLambda 8 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < carmichaelLambda 8 := carmichael_pos 8
  have hne1 : carmichaelLambda 8 ≠ 1 := by
    intro h
    obtain ⟨a, ha⟩ : ∃ a : (ZMod 8)ˣ, a ≠ 1 := by decide
    have hpow := pow_carmichael (n := 8) a
    rw [h, pow_one] at hpow
    exact ha hpow
  omega

/-- **`λ(8) = 2 < 4 = φ(8)`.** Carmichael's exponent is strictly smaller than Euler's. -/
theorem carmichael_lt_totient_eight : carmichaelLambda 8 < Nat.totient 8 := by
  rw [carmichael_eight, totient_eight]; norm_num

/-- **Euler's exponent `φ(n)` is not minimal.** At `n = 8` there is a positive
`N = 2` strictly below `φ(8) = 4` that already annihilates every unit — so the
exponent `φ(n)` from Euler's theorem is not the least universal exponent, and the
minimal one is Carmichael's `λ(8) = 2` (`carmichael_isLeast`, `carmichael_eight`). -/
theorem euler_exponent_not_minimal :
    ∃ N, 0 < N ∧ N < Nat.totient 8 ∧ ∀ a : (ZMod 8)ˣ, a ^ N = 1 := by
  refine ⟨2, by norm_num, ?_, sq_eq_one_zmod_eight⟩
  rw [totient_eight]; norm_num

end EulerTotientOQ0502

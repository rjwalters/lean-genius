/-
# Euler's Theorem via the Group Structure of (ℤ/nℤ)ˣ  (OQ02-OQ02)

The base entry `euler-totient` states Euler's theorem `a^φ(n) ≡ 1 (mod n)` and
discharges it in one line by citing Mathlib's `ZMod.pow_totient`, treating the
underlying group mechanism as a black box. Its worked examples lean on
`native_decide`, which pulls in the `Lean.ofReduceBool` axiom.

This file makes the **group-theoretic mechanism explicit** and stays strictly
`0`-axiom (no `native_decide`). The organising object is the finite abelian
group of units `(ℤ/nℤ)ˣ`, whose order is `φ(n)`. Every statement below is a
consequence of a single structural fact — **Lagrange's theorem** — applied to
that group:

    the multiplicative order of a unit divides the group order `φ(n)`.

## Main results

1. `orderOf_unit_dvd_totient` — the sharp refinement: the multiplicative order
   of any unit divides `φ(n)`. This is *stronger* than Euler's theorem: it says
   `φ(n)` is a universal exponent, and pinpoints exactly why `a^φ(n) = 1`.
2. `euler_units` — Euler's theorem for units, derived from (1) through
   `orderOf_dvd_iff_pow_eq_one`. The proof is the honest Lagrange argument, not
   a citation of the packaged theorem.
3. `euler_modEq` — the number-theoretic form `a^φ(n) ≡ 1 (mod n)` over `ℕ`.
4. `pow_mod_totient` / `pow_mod_totient_modEq` — exponents may be reduced modulo
   `φ(n)`: `a^k = a^(k % φ(n))`. This is the practical payoff of the order
   dividing `φ(n)` and is what makes modular exponentiation efficient.
5. `fermat_little_of_euler` — Fermat's little theorem recovered as the prime
   special case `φ(p) = p - 1`.
6. `coprime_of_pow_modEq_one` — the **converse direction**: if some positive
   power of `a` is `≡ 1 (mod n)` then `a` must be coprime to `n`. This replaces
   the base file's `native_decide` non-coprime counterexamples with the general
   `0`-axiom theorem explaining *why* coprimality is forced (a non-unit can
   never be sent to `1` by any power).

Only the foundational axioms `propext`, `Classical.choice`, `Quot.sound` are
used; confirmed via `#print axioms`. No `sorryAx`, no `Lean.ofReduceBool`.
-/

import Mathlib

namespace EulerTotientOQ02OQ02

open Nat

variable {n : ℕ}

-- ============================================================
-- SECTION I: The structural refinement (Lagrange in the unit group)
-- ============================================================

/-- **The refinement underlying Euler's theorem.** The multiplicative order of
any unit of `ℤ/nℤ` divides `φ(n)`. This is Lagrange's theorem for the finite
group `(ℤ/nℤ)ˣ`, whose cardinality is `φ(n)`. It is strictly stronger than
`a^φ(n) = 1`: it exhibits `φ(n)` as a *universal exponent* for the unit group. -/
theorem orderOf_unit_dvd_totient [NeZero n] (a : (ZMod n)ˣ) :
    orderOf a ∣ φ n := by
  rw [← ZMod.card_units_eq_totient n]
  exact orderOf_dvd_card

-- ============================================================
-- SECTION II: Euler's theorem for units, via explicit Lagrange
-- ============================================================

/-- **Euler's theorem for units**, obtained *from* `orderOf_unit_dvd_totient`
rather than by citing the packaged `ZMod.pow_totient`. The bridge is
`orderOf_dvd_iff_pow_eq_one`: an element killed by its order is killed by any
multiple of it, and `φ(n)` is such a multiple. -/
theorem euler_units [NeZero n] (a : (ZMod n)ˣ) :
    a ^ φ n = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (orderOf_unit_dvd_totient a)

-- ============================================================
-- SECTION III: The number-theoretic form (ℕ)
-- ============================================================

/-- **Euler's theorem over `ℕ`.** For `a` coprime to `n`, `a^φ(n) ≡ 1 (mod n)`.
This is the arithmetic shadow of `euler_units`: a coprime residue is a unit, and
units satisfy `x^φ(n) = 1`. -/
theorem euler_modEq {a : ℕ} (h : Nat.Coprime a n) :
    a ^ φ n ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

-- ============================================================
-- SECTION IV: Exponent reduction modulo φ(n)
-- ============================================================

/-- **Exponents reduce modulo `φ(n)` (unit form).** Because `a^φ(n) = 1`, only
the residue of the exponent modulo `φ(n)` matters: `a^k = a^(k % φ(n))`. This is
the algebraic engine behind fast modular exponentiation. -/
theorem pow_mod_totient [NeZero n] (a : (ZMod n)ˣ) (k : ℕ) :
    a ^ k = a ^ (k % φ n) := by
  conv_lhs => rw [← Nat.mod_add_div k (φ n)]
  rw [pow_add, pow_mul, euler_units, one_pow, mul_one]

/-- **Exponents reduce modulo `φ(n)` (arithmetic form).** For `a` coprime to
`n`, `a^k ≡ a^(k % φ(n)) (mod n)`. -/
theorem pow_mod_totient_modEq {a : ℕ} (h : Nat.Coprime a n) (k : ℕ) :
    a ^ k ≡ a ^ (k % φ n) [MOD n] := by
  conv_lhs => rw [← Nat.mod_add_div k (φ n)]
  calc a ^ (k % φ n + φ n * (k / φ n))
      = a ^ (k % φ n) * (a ^ φ n) ^ (k / φ n) := by rw [pow_add, pow_mul]
    _ ≡ a ^ (k % φ n) * 1 ^ (k / φ n) [MOD n] :=
        (Nat.ModEq.refl _).mul ((euler_modEq h).pow _)
    _ = a ^ (k % φ n) := by rw [one_pow, mul_one]

-- ============================================================
-- SECTION V: Fermat's little theorem as the prime special case
-- ============================================================

/-- **Fermat's little theorem**, recovered from Euler's theorem by specialising
to a prime modulus, where `φ(p) = p - 1`. -/
theorem fermat_little_of_euler {p a : ℕ} (hp : p.Prime) (h : Nat.Coprime a p) :
    a ^ (p - 1) ≡ 1 [MOD p] := by
  have := euler_modEq h
  rwa [Nat.totient_prime hp] at this

-- ============================================================
-- SECTION VI: Coprimality is necessary (the converse; 0-axiom)
-- ============================================================

/-- **Coprimality is forced.** If any *positive* power of `a` is `≡ 1 (mod n)`,
then `a` is coprime to `n`. Structurally: `a^k = 1` in `ℤ/nℤ` exhibits `a` as a
unit (with inverse `a^(k-1)`), and units of `ℤ/nℤ` are exactly the coprime
residues. This is the general theorem behind the base file's `native_decide`
non-coprime counterexamples — here proved with no decision procedure. -/
theorem coprime_of_pow_modEq_one {a k : ℕ} (hk : 0 < k)
    (h : a ^ k ≡ 1 [MOD n]) : Nat.Coprime a n := by
  rw [← ZMod.isUnit_iff_coprime]
  -- Transport the congruence into `ZMod n`.
  have hcast : (a : ZMod n) ^ k = 1 := by
    have : ((a ^ k : ℕ) : ZMod n) = ((1 : ℕ) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 h
    simpa using this
  -- `a^k = 1` with `k ≠ 0` exhibits `a` as a unit (inverse `a^(k-1)`).
  exact IsUnit.of_pow_eq_one hcast hk.ne'

/-- **Contrapositive, as used in practice.** A residue sharing a nontrivial
factor with `n` cannot satisfy Euler's congruence for the totient exponent when
`0 < φ(n)` — indeed for no positive exponent at all. Stated as: non-coprime
implies no positive power hits `1`. -/
theorem no_pow_modEq_one_of_not_coprime {a k : ℕ} (hk : 0 < k)
    (h : ¬ Nat.Coprime a n) : ¬ a ^ k ≡ 1 [MOD n] :=
  fun hcon => h (coprime_of_pow_modEq_one hk hcon)

end EulerTotientOQ02OQ02

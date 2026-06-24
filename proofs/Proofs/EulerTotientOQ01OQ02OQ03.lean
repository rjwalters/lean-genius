import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

/-
# Euler totient OQ-01 → OQ-02 → OQ-03: the Carmichael function as the maximal order, and primitive roots

The parent entry (`euler-totient-oq-01-oq-02`) packages Mathlib's prime-power values of the
Carmichael function `λ` (the exponent of the unit group `(ℤ/nℤ)ˣ`). Its closing open
questions ask to

> *assemble the full formula `λ(n) = lcm` of the prime-power values, and to formalize the
> application that the maximal multiplicative order modulo `n` equals `λ(n)`, characterizing
> the `n` for which primitive roots exist.*

This file answers both. The point of `λ(n)` is **two-fold**:

* it is an **upper bound** on the multiplicative order of every unit: `aᵏ ≡ 1` for `k = λ(n)`,
  so `orderOf a ∣ λ(n)` (`orderOf_dvd_carmichael`); and
* it is **attained** — there is a unit whose order is *exactly* `λ(n)`
  (`exists_orderOf_eq_carmichael`).

Together these say `λ(n)` is the **maximal multiplicative order** modulo `n`. A *primitive
root* mod `n` is a unit of maximal possible order `φ(n)`; combining the two halves shows one
exists **iff** `λ(n) = φ(n)** (`exists_primitiveRoot_iff_carmichael_eq_totient`), iff the unit
group is cyclic (`isCyclic_units_iff_carmichael_eq_totient`). Since `λ(n) ∣ φ(n)` always and
`λ` can be a proper divisor (e.g. `λ(15) = 4 < 8 = φ(15)`), primitive roots fail to exist for
many `n` — the classical fact that `(ℤ/nℤ)ˣ` is cyclic only for `n ∈ {1,2,4,pᵏ,2pᵏ}`.

## Main results

* `carmichael_factorization'` : `λ(n) = lcm` over prime powers `p^{vₚ(n)}` of `λ(p^{vₚ(n)})`
  (the closed form, OQ-1).
* `orderOf_dvd_carmichael`, `orderOf_le_carmichael` : `λ(n)` bounds every unit's order.
* `exists_orderOf_eq_carmichael` : `λ(n)` is attained — the maximal order.
* `carmichael_le_totient` : `λ(n) ≤ φ(n)`.
* `isCyclic_units_iff_carmichael_eq_totient` : `(ℤ/nℤ)ˣ` cyclic `↔ λ(n) = φ(n)`.
* `exists_primitiveRoot_iff_carmichael_eq_totient` : a primitive root mod `n` exists `↔ λ(n) = φ(n)`.
* `carmichael_fifteen`, `not_exists_primitiveRoot_fifteen` : `λ(15) = 4 < 8 = φ(15)`, no primitive root mod 15.
* `exists_primitiveRoot_seven` : `λ(7) = 6 = φ(7)`, a primitive root mod 7 exists.
-/

namespace EulerTotientOQ01OQ02OQ03

open ArithmeticFunction Nat

/-- **The Carmichael function is positive** for `n ≠ 0`: it is the exponent of a finite group. -/
theorem carmichael_pos (n : ℕ) [NeZero n] : 0 < Carmichael n := by
  rw [carmichael_eq_exponent']
  exact Monoid.ExponentExists.of_finite.exponent_pos

/-- **Closed form (OQ-1).** `λ(n)` is the least common multiple, over the primes `p` dividing
    `n`, of the prime-power values `λ(p^{vₚ(n)})`. Combined with the parent's prime-power
    identities (`λ(2ᵏ) = 2ᵏ⁻²`, `λ(pᵏ) = φ(pᵏ)` for odd `p`) this determines `λ` for every `n`.
    (A restatement of Mathlib's `carmichael_factorization`.) -/
theorem carmichael_factorization' (n : ℕ) [NeZero n] :
    Carmichael n = n.primeFactors.lcm fun p ↦ Carmichael (p ^ n.factorization p) :=
  ArithmeticFunction.carmichael_factorization n

/-- **Upper bound (divisibility).** The order of every unit `a` modulo `n` divides `λ(n)`:
    `a^{λ(n)} = 1`, so `λ(n)` is a universal exponent. -/
theorem orderOf_dvd_carmichael {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) :
    orderOf a ∣ Carmichael n := by
  rw [carmichael_eq_exponent']
  exact Monoid.order_dvd_exponent a

/-- **Upper bound (size).** Hence the order of every unit is at most `λ(n)`. -/
theorem orderOf_le_carmichael {n : ℕ} [NeZero n] (a : (ZMod n)ˣ) :
    orderOf a ≤ Carmichael n :=
  Nat.le_of_dvd (carmichael_pos n) (orderOf_dvd_carmichael a)

/-- **The maximal order is attained.** There is a unit modulo `n` whose multiplicative order is
    exactly `λ(n)`. Together with `orderOf_le_carmichael` this characterises `λ(n)` as the
    **maximal multiplicative order** modulo `n` — the application requested by the OQ. -/
theorem exists_orderOf_eq_carmichael (n : ℕ) [NeZero n] :
    ∃ a : (ZMod n)ˣ, orderOf a = Carmichael n := by
  rw [carmichael_eq_exponent']
  exact Monoid.exists_orderOf_eq_exponent Monoid.ExponentExists.of_finite

/-- **`λ(n) ≤ φ(n)`.** Euler's theorem factors through the smaller exponent `λ`. -/
theorem carmichael_le_totient (n : ℕ) [NeZero n] : Carmichael n ≤ n.totient :=
  Nat.le_of_dvd (Nat.totient_pos.mpr (NeZero.pos n)) (ArithmeticFunction.carmichael_dvd_totient n)

/-- **Cyclicity criterion.** The unit group `(ℤ/nℤ)ˣ` is cyclic **iff** `λ(n) = φ(n)`: the
    maximal order equals the group order exactly when some element generates the whole group. -/
theorem isCyclic_units_iff_carmichael_eq_totient (n : ℕ) [NeZero n] :
    IsCyclic (ZMod n)ˣ ↔ Carmichael n = n.totient := by
  rw [carmichael_eq_exponent', IsCyclic.iff_exponent_eq_card, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

/-- **Primitive-root characterisation (the OQ's headline).** A *primitive root* modulo `n` is a
    unit of maximal possible order `φ(n)` (a generator of `(ℤ/nℤ)ˣ`). One exists **iff**
    `λ(n) = φ(n)`, i.e. iff the Carmichael function meets the totient. -/
theorem exists_primitiveRoot_iff_carmichael_eq_totient (n : ℕ) [NeZero n] :
    (∃ a : (ZMod n)ˣ, orderOf a = n.totient) ↔ Carmichael n = n.totient := by
  rw [← isCyclic_units_iff_carmichael_eq_totient, isCyclic_iff_exists_orderOf_eq_natCard,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-- `λ(15) = 4`. Since `15 = 3·5` with `3,5` coprime, `λ(15) = lcm(λ(3), λ(5)) = lcm(2, 4) = 4`. -/
theorem carmichael_fifteen : Carmichael 15 = 4 := by
  have h3 : Carmichael 3 = 2 := by
    have := carmichael_pow_of_prime_ne_two (p := 3) 1 (by norm_num) (by norm_num)
    simpa using this
  have h5 : Carmichael 5 = 4 := by
    have := carmichael_pow_of_prime_ne_two (p := 5) 1 (by norm_num) (by norm_num)
    simpa using this
  have : (15 : ℕ) = 3 * 5 := by norm_num
  rw [this, ArithmeticFunction.carmichael_mul (by decide), h3, h5]
  decide

/-- **No primitive root modulo 15.** `λ(15) = 4 < 8 = φ(15)`, so by the characterisation no
    unit attains order `φ(15)` — the failure of `λ = φ` is exactly the obstruction. -/
theorem not_exists_primitiveRoot_fifteen :
    ¬ ∃ a : (ZMod 15)ˣ, orderOf a = (15 : ℕ).totient := by
  rw [exists_primitiveRoot_iff_carmichael_eq_totient, carmichael_fifteen]
  norm_num [show (15 : ℕ).totient = 8 by decide]

/-- **A primitive root modulo 7 exists.** `7` is prime, so `(ℤ/7ℤ)ˣ` is cyclic and
    `λ(7) = φ(7) = 6`; some unit has order `6`. -/
theorem exists_primitiveRoot_seven :
    ∃ a : (ZMod 7)ˣ, orderOf a = (7 : ℕ).totient := by
  rw [exists_primitiveRoot_iff_carmichael_eq_totient]
  have := carmichael_pow_of_prime_ne_two (p := 7) 1 (by norm_num) (by norm_num)
  simpa using this

end EulerTotientOQ01OQ02OQ03

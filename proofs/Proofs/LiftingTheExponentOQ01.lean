import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-
# Lifting the Exponent (LTE) in `padicValNat` form

## What This Proves

The **Lifting the Exponent Lemma** (LTE) is the workhorse behind a huge swath of
olympiad and analytic-number-theory `p`-adic valuation computations.  For an odd
prime `p` and integers `x, y` with `p ∣ x - y` but `p ∤ x`, it states

    v_p(xⁿ - yⁿ) = v_p(x - y) + v_p(n)       for every `n ≥ 1`,

and dually, for **odd** exponents `n`,

    v_p(xⁿ + yⁿ) = v_p(x + y) + v_p(n).

Here `v_p` is the `p`-adic valuation: the exponent of the highest power of `p`
dividing its argument.

## Why this is not already in Mathlib

Mathlib proves LTE only in the `emultiplicity` form
(`Nat.emultiplicity_pow_sub_pow`), where both sides live in the extended naturals
`ℕ∞` and "valuation of `0`" is `⊤`.  That is the right home for the abstract
statement, but it is *not* the form a working number theorist uses: the standard
textbook statement is an honest equation of natural numbers built from
`padicValNat`.

Bridging the two requires discharging genuine *finiteness* side conditions —
every argument (`xⁿ - yⁿ`, `x - y`, and `n`) must be nonzero, otherwise its
`emultiplicity` is `⊤` and the natural-number `padicValNat` equation is simply
false.  This file does that bridging once and packages the textbook statements,
together with the most common specialisation `v_p(aⁿ - 1) = v_p(a - 1) + v_p(n)`.

## Approach

The single bridge is `padicValNat_eq_emultiplicity`, which says
`(padicValNat p m : ℕ∞) = emultiplicity p m` *whenever `m ≠ 0`*.  We:

1. establish the three nonzero side conditions from `y < x` (resp. `0 < x`) and
   `0 < n`;
2. cast the target into `ℕ∞`, rewrite each `padicValNat` to an `emultiplicity`;
3. close with Mathlib's `emultiplicity` LTE;
4. pull the equality back across the (injective) cast `ℕ ↪ ℕ∞`.

Everything is fully `0`-axiom: no `sorry`, no `axiom`, no `native_decide`.
-/

namespace LiftingTheExponentOQ01

open scoped Classical

/-- **Lifting the Exponent (subtraction form).**
For an odd prime `p` with `p ∣ x - y` and `p ∤ x`, and naturals `y < x`, `0 < n`,
the `p`-adic valuation of `xⁿ - yⁿ` splits as
`v_p(xⁿ - yⁿ) = v_p(x - y) + v_p(n)`. -/
theorem padicValNat_pow_sub_pow {p x y n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hxy : p ∣ x - y) (hx : ¬ p ∣ x) (hyx : y < x) (hn : 0 < n) :
    padicValNat p (x ^ n - y ^ n) = padicValNat p (x - y) + padicValNat p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hxy0 : x - y ≠ 0 := Nat.sub_ne_zero_of_lt hyx
  have hpow : y ^ n < x ^ n := Nat.pow_lt_pow_left hyx hn.ne'
  have hpow0 : x ^ n - y ^ n ≠ 0 := Nat.sub_ne_zero_of_lt hpow
  have key : (↑(padicValNat p (x ^ n - y ^ n)) : ℕ∞)
      = ↑(padicValNat p (x - y) + padicValNat p n) := by
    rw [padicValNat_eq_emultiplicity hpow0, Nat.cast_add,
        padicValNat_eq_emultiplicity hxy0, padicValNat_eq_emultiplicity hn.ne']
    exact Nat.emultiplicity_pow_sub_pow hp hodd hxy hx n
  exact_mod_cast key

/-- **Lifting the Exponent (addition form, odd exponent).**
For an odd prime `p` with `p ∣ x + y` and `p ∤ x`, and `0 < x`, `Odd n`,
the `p`-adic valuation of `xⁿ + yⁿ` splits as
`v_p(xⁿ + yⁿ) = v_p(x + y) + v_p(n)`. -/
theorem padicValNat_pow_add_pow {p x y n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hn : Odd n) (hxy : p ∣ x + y) (hx : ¬ p ∣ x) (hx0 : 0 < x) :
    padicValNat p (x ^ n + y ^ n) = padicValNat p (x + y) + padicValNat p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := hn.pos.ne'
  have hxn : 0 < x ^ n := pow_pos hx0 n
  have hxy0 : x + y ≠ 0 := by omega
  have hpow0 : x ^ n + y ^ n ≠ 0 := by omega
  have key : (↑(padicValNat p (x ^ n + y ^ n)) : ℕ∞)
      = ↑(padicValNat p (x + y) + padicValNat p n) := by
    rw [padicValNat_eq_emultiplicity hpow0, Nat.cast_add,
        padicValNat_eq_emultiplicity hxy0, padicValNat_eq_emultiplicity hn0]
    exact Nat.emultiplicity_pow_add_pow hp hodd hxy hx hn
  exact_mod_cast key

/-- **The workhorse specialisation.**
For an odd prime `p` dividing `a - 1` with `1 < a`, and `0 < n`,
`v_p(aⁿ - 1) = v_p(a - 1) + v_p(n)`.  This is the form used to read off the order
of `p` in numbers like `2ⁿ - 1` or repunits.  Note `p ∤ a` is *automatic*: if
`p ∣ a` and `p ∣ a - 1` then `p ∣ 1`, impossible for a prime. -/
theorem padicValNat_pow_sub_one {p a n : ℕ} (hp : p.Prime) (hodd : Odd p)
    (ha : p ∣ a - 1) (ha1 : 1 < a) (hn : 0 < n) :
    padicValNat p (a ^ n - 1) = padicValNat p (a - 1) + padicValNat p n := by
  have hx : ¬ p ∣ a := by
    intro h
    have h1 : p ∣ a - (a - 1) := Nat.dvd_sub h ha
    rw [show a - (a - 1) = 1 from by omega] at h1
    exact absurd (Nat.le_of_dvd one_pos h1) (Nat.not_le.mpr hp.one_lt)
  have := padicValNat_pow_sub_pow hp hodd ha hx ha1 hn
  simpa using this

/-- Concrete check that the corollary computes correctly: with `p = 3`, `a = 4`,
`n = 6` we have `4⁶ - 1 = 4095 = 3² · 5 · 7 · 13`, so `v_3(4⁶ - 1) = 2`, matching
`v_3(4 - 1) + v_3(6) = 1 + 1`.  Proved *through the theorem*, not by raw
computation, so it stays fully axiom-free. -/
example : padicValNat 3 (4 ^ 6 - 1) = padicValNat 3 (4 - 1) + padicValNat 3 6 :=
  padicValNat_pow_sub_one (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end LiftingTheExponentOQ01

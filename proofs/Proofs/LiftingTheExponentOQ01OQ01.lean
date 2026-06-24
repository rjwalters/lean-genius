import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-
# Lifting the Exponent at `p = 2` — the even-exponent exception (difference form)

## What This Proves

The parent entry (`lifting-the-exponent-oq-01`) packages the odd-prime Lifting the
Exponent lemma as an honest `padicValNat` equation,

    v_p(xⁿ - yⁿ) = v_p(x - y) + v_p(n)        (p odd, p ∣ x - y, p ∤ x),

and explicitly excludes `p = 2`.  The prime `2` is genuinely different: for
**even** exponents `n` an extra `v_2(x + y)` term appears and the right-hand side
is offset by `-1`.  This file proves the corrected two-adic law as a clean
`padicValInt` equation,

    v_2(xⁿ - yⁿ) + 1 = v_2(x - y) + v_2(x + y) + v_2(n)        (x, y odd, n even).

Equivalently, with truncated natural-number subtraction,

    v_2(xⁿ - yⁿ) = v_2(x - y) + v_2(x + y) + v_2(n) - 1.

This is the even-`n` branch of the full two-adic dichotomy
(`v_2(xⁿ - yⁿ) = v_2(x - y)` for odd `n`; the formula above for even `n`).

## Why this is not already in Mathlib

Mathlib proves the `p = 2` law only in the `emultiplicity`/`ℕ∞` form
(`Int.two_pow_sub_pow`), where "valuation of `0`" is `⊤`.  Transporting it to an
honest integer `padicValInt` equation requires discharging four genuine
*finiteness* side conditions — `xⁿ - yⁿ`, `x - y`, `x + y` and `n` must all be
nonzero.  The interesting one is `xⁿ - yⁿ ≠ 0`: for **even** `n` this needs
`x ≠ ± y` (not merely `x ≠ y`), since `x` and `-x` share the same even power.

## Approach

1. A single bridge `padicValInt_two_eq_emultiplicity`:
   `(padicValInt 2 z : ℕ∞) = emultiplicity (2 : ℤ) z` for `z ≠ 0`, obtained from
   the natural-number bridge `padicValNat_eq_emultiplicity` composed with
   `Int.emultiplicity_natAbs`.
2. The nonzero side condition `xⁿ ≠ yⁿ` from `x ≠ ± y` and `0 < n`, via
   `Int.natAbs` and `Nat.pow_left_injective`.
3. Cast the target into `ℕ∞`, rewrite every `padicValInt` to an `emultiplicity`,
   and close with Mathlib's `Int.two_pow_sub_pow`; pull the equality back across
   the injective cast `ℕ ↪ ℕ∞`.

Everything is fully `0`-axiom: no `sorry`, no `axiom`, no `native_decide`.
-/

namespace LiftingTheExponentOQ01OQ01

open scoped Classical

/-- **Finiteness bridge for `p = 2`.**  For a nonzero integer `z`, the integer
`2`-adic valuation `padicValInt 2 z` (an honest natural number) coincides, after
casting to `ℕ∞`, with the extended multiplicity `emultiplicity (2 : ℤ) z`. -/
theorem padicValInt_two_eq_emultiplicity {z : ℤ} (hz : z ≠ 0) :
    (padicValInt 2 z : ℕ∞) = emultiplicity (2 : ℤ) z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValInt, padicValNat_eq_emultiplicity (Int.natAbs_ne_zero.mpr hz),
      Int.emultiplicity_natAbs]
  norm_cast

/-- For an **even** positive exponent `n` and integers with `x ≠ y` and
`x ≠ -y`, the powers differ: `xⁿ ≠ yⁿ`.  (Evenness makes `x` and `-x` collide,
so `x ≠ y` alone is not enough — we genuinely need `x ≠ ± y`.) -/
theorem int_pow_ne_pow_of_ne {x y : ℤ} {n : ℕ} (hn0 : 0 < n)
    (hne : x ≠ y) (hne' : x ≠ -y) : x ^ n ≠ y ^ n := by
  intro h
  have habs : x.natAbs ^ n = y.natAbs ^ n := by
    have := congrArg Int.natAbs h
    rwa [Int.natAbs_pow, Int.natAbs_pow] at this
  have heq : x.natAbs = y.natAbs := Nat.pow_left_injective hn0.ne' habs
  rcases Int.natAbs_eq_natAbs_iff.mp heq with h1 | h1
  · exact hne h1
  · exact hne' h1

/-- **Lifting the Exponent at `p = 2`, difference form (additive).**
For odd integers `x, y`, an even exponent `n > 0`, and `x ≠ y`, `x + y ≠ 0`,

    v_2(xⁿ - yⁿ) + 1 = v_2(x - y) + v_2(x + y) + v_2(n).

This is the two-adic exception to the odd-prime rule of the parent entry: the
extra term `v_2(x + y)` and the `+1` offset are both present precisely because
`p = 2` and `n` is even. -/
theorem padicValInt_two_pow_sub_pow {x y : ℤ} {n : ℕ}
    (hx : Odd x) (hy : Odd y) (hn : Even n) (hn0 : 0 < n)
    (hne : x ≠ y) (hadd : x + y ≠ 0) :
    padicValInt 2 (x ^ n - y ^ n) + 1 =
      padicValInt 2 (x - y) + padicValInt 2 (x + y) + padicValNat 2 n := by
  -- Hypotheses for Mathlib's `Int.two_pow_sub_pow`.
  have hx2 : ¬ (2 : ℤ) ∣ x := by
    rw [← even_iff_two_dvd, Int.not_even_iff_odd]; exact hx
  have hxy2 : (2 : ℤ) ∣ x - y := even_iff_two_dvd.mp (hx.sub_odd hy)
  -- Nonzero side conditions for the finiteness bridge.
  have hne' : x ≠ -y := fun h => hadd (by rw [h]; ring)
  have hsub0 : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hpow0 : x ^ n - y ^ n ≠ 0 :=
    sub_ne_zero.mpr (int_pow_ne_pow_of_ne hn0 hne hne')
  have hn0' : (n : ℤ) ≠ 0 := by exact_mod_cast hn0.ne'
  -- The `n`-term: rephrase `padicValNat 2 n` as `padicValInt 2 (n : ℤ)`.
  have hcast : padicValInt 2 (n : ℤ) = padicValNat 2 n := by
    rw [padicValInt, Int.natAbs_natCast]
  -- Cast into `ℕ∞`, rewrite to `emultiplicity`, apply the `p = 2` LTE law.
  have key : (↑(padicValInt 2 (x ^ n - y ^ n) + 1) : ℕ∞)
      = ↑(padicValInt 2 (x - y) + padicValInt 2 (x + y) + padicValNat 2 n) := by
    rw [← hcast]
    push_cast
    rw [padicValInt_two_eq_emultiplicity hpow0,
        padicValInt_two_eq_emultiplicity hsub0,
        padicValInt_two_eq_emultiplicity hadd,
        padicValInt_two_eq_emultiplicity hn0',
        Int.two_pow_sub_pow hxy2 hx2 hn]
    abel
  exact_mod_cast key

/-- **Lifting the Exponent at `p = 2`, difference form (truncated subtraction).**
The same law packaged with `ℕ`-subtraction:

    v_2(xⁿ - yⁿ) = v_2(x - y) + v_2(x + y) + v_2(n) - 1. -/
theorem padicValInt_two_pow_sub_pow' {x y : ℤ} {n : ℕ}
    (hx : Odd x) (hy : Odd y) (hn : Even n) (hn0 : 0 < n)
    (hne : x ≠ y) (hadd : x + y ≠ 0) :
    padicValInt 2 (x ^ n - y ^ n) =
      padicValInt 2 (x - y) + padicValInt 2 (x + y) + padicValNat 2 n - 1 := by
  have h := padicValInt_two_pow_sub_pow hx hy hn hn0 hne hadd
  omega

/-- **Specialisation to `xⁿ - 1`.**  For an odd integer `a` with `a ≠ 1` and
`a ≠ -1`, and an even exponent `n > 0`,

    v_2(aⁿ - 1) + 1 = v_2(a - 1) + v_2(a + 1) + v_2(n).

This is the form most often quoted for orders and Mersenne-type valuations. -/
theorem padicValInt_two_pow_sub_one {a : ℤ} {n : ℕ}
    (ha : Odd a) (hn : Even n) (hn0 : 0 < n) (h1 : a ≠ 1) (h1' : a ≠ -1) :
    padicValInt 2 (a ^ n - 1) + 1 =
      padicValInt 2 (a - 1) + padicValInt 2 (a + 1) + padicValNat 2 n := by
  have hadd : a + 1 ≠ 0 := fun h => h1' (by linarith)
  have := padicValInt_two_pow_sub_pow ha odd_one hn hn0 h1 hadd
  simpa using this

end LiftingTheExponentOQ01OQ01

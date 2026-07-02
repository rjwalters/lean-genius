import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic
import Proofs.StarsAndBarsWeakCompositionsOQ01

/-
# Newton's Generalized Binomial Coefficient and the Negative Binomial Theorem

## What This Proves

The parent entry (`StarsAndBarsWeakCompositionsOQ01.lean`) identifies the ordinary
generating function of the weak-composition counts with Mathlib's `invOneSubPow S k`,
the algebraic power series `1/(1 − X)ᵏ`, and reads off its coefficients as the
stars-and-bars count

  `coeff n (invOneSubPow S k) = C(n + k − 1, n)`   (`coeff_invOneSubPow_eq_choose`).

This entry supplies the **negative binomial theorem** reading of the very same
coefficients, answering the parent's second open question. Newton's generalized
binomial coefficient `C(r, n)` — Mathlib's `Ring.choose r n`, defined over any
binomial ring by dividing a descending Pochhammer product by `n!` — extends
`Nat.choose` to negative (indeed arbitrary ring) upper index. The classical
*upper-negation* / negative-binomial identity is

  `(−1)ⁿ · C(−k, n) = C(n + k − 1, n)`,

which says the coefficients `C(n + k − 1, n)` of `1/(1 − X)ᵏ` are, up to the sign
`(−1)ⁿ`, the generalized binomial coefficients `C(−k, n)`. Equivalently
`1/(1 − X)ᵏ = ∑ₙ C(−k, n) (−X)ⁿ`, the negative-binomial expansion of `(1 − X)⁻ᵏ`.

## The argument

Mathlib already provides the analytic backbone:

* `Ring.choose_neg : choose (−r) n = Int.negOnePow n • choose (r + n − 1) n`
  — upper negation for the generalized binomial coefficient, with the sign carried
  by the unit `Int.negOnePow n = (−1)ⁿ ∈ ℤˣ`.
* `Ring.choose_natCast : choose (↑m) n = ↑(Nat.choose m n)` — on natural upper index
  the generalized coefficient is the ordinary one.
* `PowerSeries.rescale_neg_one_invOneSubPow :
  rescale (−1) (invOneSubPow A d) = binomialSeries A (−d)` — substituting `X ↦ −X`
  turns `1/(1 − X)ᵈ` into the binomial series `(1 + X)⁻ᵈ` whose coefficients are
  `Ring.choose (−d) n`.

The content added here is the *bridge*: rewriting the unit `Int.negOnePow n` as the
plain ring element `(−1)ⁿ`, specializing to `r = k : ℤ` (with `k ≥ 1`, so that
`k + n − 1` is a genuine natural number), and threading the resulting elementary
identity through the parent's coefficient formula and the stars-and-bars count. The
upshot is that the generalized binomial coefficient `C(−k, n)` *counts weak
compositions up to sign*.

## What Mathlib has — and what this adds

Mathlib has `Ring.choose` and its upper-negation `Ring.choose_neg` (sign as a unit),
the binomial power series `binomialSeries`, and the rescale relation
`rescale_neg_one_invOneSubPow`. It does **not** record the clean elementary identity
`(−1)ⁿ C(−k, n) = C(n + k − 1, n)` with the sign as `(−1)ⁿ`, nor its connection to
the enumerative content of the parent entry. The new results are:
`ringChoose_neg_eq` (upper negation in `(−1)ⁿ` form over any binomial ring),
`ringChoose_neg_natCast` and `negOnePow_mul_ringChoose_neg` (the negative-binomial
identity over ℤ), `coeff_invOneSubPow_eq_negOnePow_mul_ringChoose` (the negative
binomial reading of `invOneSubPow`'s coefficients), `coeff_rescale_invOneSubPow`
(coefficient of `(1 + X)⁻ᵏ` is exactly `C(−k, n)`), and
`negOnePow_mul_ringChoose_eq_card_weakComposition` (the generalized binomial
coefficient counts weak compositions up to sign).
-/

open PowerSeries

namespace StarsAndBarsNegBinom

/-- **Upper negation for the generalized binomial coefficient.** Over any commutative
binomial ring, `Ring.choose (−r) n = (−1)ⁿ · Ring.choose (r + n − 1) n`.

This is Mathlib's `Ring.choose_neg` with the unit `Int.negOnePow n ∈ ℤˣ` rewritten as
the plain ring element `(−1)ⁿ`. -/
theorem ringChoose_neg_eq {R : Type*} [CommRing R] [BinomialRing R] (r : R) (n : ℕ) :
    Ring.choose (-r) n = (-1) ^ n * Ring.choose (r + n - 1) n := by
  rw [Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul]
  push_cast
  ring

/-- The nonnegative upper index `k + n − 1` is a genuine natural number when `k ≥ 1`:
`(k : ℤ) + n − 1 = ↑(n + k − 1)`. -/
private theorem cast_add_sub_one (k n : ℕ) (hk : 0 < k) :
    (k : ℤ) + n - 1 = ((n + k - 1 : ℕ) : ℤ) := by
  have h : 1 ≤ n + k := by omega
  rw [Nat.cast_sub h]
  push_cast
  ring

/-- **Negative binomial identity, `Ring.choose` form.** Over ℤ, for `k ≥ 1`,
`Ring.choose (−k, n) = (−1)ⁿ · C(n + k − 1, n)`, where the right-hand `C` is the
ordinary `Nat.choose`. -/
theorem ringChoose_neg_natCast (k n : ℕ) (hk : 0 < k) :
    Ring.choose (-(k : ℤ)) n = (-1) ^ n * ((n + k - 1).choose n : ℤ) := by
  rw [ringChoose_neg_eq, cast_add_sub_one k n hk, Ring.choose_natCast]

/-- **Newton's generalized binomial coefficient identity** (the parent's open
question): `(−1)ⁿ · C(−k, n) = C(n + k − 1, n)` over ℤ, for `k ≥ 1`. The sign folds
in because `(−1)ⁿ · (−1)ⁿ = 1`. -/
theorem negOnePow_mul_ringChoose_neg (k n : ℕ) (hk : 0 < k) :
    (-1) ^ n * Ring.choose (-(k : ℤ)) n = ((n + k - 1).choose n : ℤ) := by
  have hsign : ((-1 : ℤ)) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]; norm_num
  rw [ringChoose_neg_natCast k n hk, ← mul_assoc, hsign, one_mul]

/-- **Negative binomial reading of the coefficients of `1/(1 − X)ᵏ`.** Over ℤ, the
`n`-th coefficient of Mathlib's `invOneSubPow ℤ k` is `(−1)ⁿ · C(−k, n)`, the
generalized binomial coefficient of `(1 − X)⁻ᵏ`. Combined with the parent's
`coeff_invOneSubPow_eq_choose` this is the identity `1/(1 − X)ᵏ = ∑ₙ C(−k, n) (−X)ⁿ`
read coefficientwise. -/
theorem coeff_invOneSubPow_eq_negOnePow_mul_ringChoose (k n : ℕ) (hk : 0 < k) :
    coeff n (invOneSubPow ℤ k).val = (-1) ^ n * Ring.choose (-(k : ℤ)) n := by
  rw [StarsAndBarsGenFun.coeff_invOneSubPow_eq_choose ℤ k n hk,
    negOnePow_mul_ringChoose_neg k n hk]

/-- **The negative binomial theorem, coefficient form.** Rescaling `X ↦ −X` sends
`1/(1 − X)ᵏ` to the binomial series `(1 + X)⁻ᵏ`, and its `n`-th coefficient is exactly
the generalized binomial coefficient `C(−k, n)`. -/
theorem coeff_rescale_invOneSubPow (k n : ℕ) :
    coeff n (rescale (-1 : ℤ) (invOneSubPow ℤ k)) = Ring.choose (-(k : ℤ)) n := by
  rw [rescale_neg_one_invOneSubPow, binomialSeries_coeff, smul_eq_mul, mul_one]

/-- **The generalized binomial coefficient counts weak compositions up to sign.**
`(−1)ⁿ · C(−k, n)` equals the number of weak compositions of `n` into `k` parts —
the enumerative content of the parent entry, now read off the negative-binomial
coefficient. -/
theorem negOnePow_mul_ringChoose_eq_card_weakComposition (k n : ℕ) (hk : 0 < k) :
    (-1) ^ n * Ring.choose (-(k : ℤ)) n
      = (Fintype.card {f : Fin k → ℕ // ∑ i, f i = n} : ℤ) := by
  rw [negOnePow_mul_ringChoose_neg k n hk, StarsAndBars.card_weakComposition]

/-- Sanity check: `C(−2, 3) = −4` while `C(4, 3) = 4`, and `(−1)³ · (−4) = 4`. -/
example : Ring.choose (-((2 : ℕ) : ℤ)) 3 = -4 := by
  rw [ringChoose_neg_natCast 2 3 (by norm_num)]
  norm_num

/-- Sanity check on the generalized coefficient at `k = 3, n = 2`:
`C(−3, 2) = (−1)² C(4, 2) = 6`. -/
example : Ring.choose (-((3 : ℕ) : ℤ)) 2 = 6 := by
  rw [ringChoose_neg_natCast 3 2 (by norm_num)]
  norm_num [Nat.choose]

end StarsAndBarsNegBinom

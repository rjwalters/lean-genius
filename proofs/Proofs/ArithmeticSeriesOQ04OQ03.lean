import Mathlib

/-
# Arithmetic Series OQ-04 / OQ-03: Riemann ζ at negative integers from Faulhaber

## The Open Question (parent OQ-04, third open question)

Faulhaber's formula writes the power sum `∑_{k=1}^n k^p` as a polynomial in `n` whose
coefficients are Bernoulli numbers. Its Bernoulli-polynomial form (Mathlib
`Polynomial.sum_range_pow_eq_bernoulli_sub`) reads
  `(p+1) · ∑_{k<n} k^p = B_{p+1}(n) − B_{p+1}`,
where `B_{p+1} = B_{p+1}(0)` is the Bernoulli number subtracted off.

> **Can we derive `ζ(−n) = −B_{n+1}/(n+1)` (the value of the Riemann zeta function at the
> non-positive integers) from the power-sum formula, via analytic continuation?**

## Answer

**Yes.** The analytic continuation itself is carried out in Mathlib (the Hurwitz/Riemann zeta
development), culminating in `riemannZeta_neg_nat_eq_bernoulli'`:
  `ζ(−n) = −B'_{n+1}/(n+1)`     (with the `B'_1 = +1/2` convention),
equivalently `riemannZeta_neg_nat_eq_bernoulli`:
  `ζ(−n) = (−1)^n · B_{n+1}/(n+1)`.

This file takes the result and makes the **Faulhaber ↔ ζ bridge explicit**:

* the constant `B_{p+1}` that Faulhaber's identity subtracts off is, for `p ≥ 1`, exactly
  `−(p+1)·ζ(−p)` (`faulhaber_constant_eq_zeta`);
* the two Bernoulli conventions in the two Mathlib value formulas agree
  (`bernoulli_convention_eq`);
* the **trivial zeros** `ζ(−2n) = 0` (`n ≥ 1`) come directly from the vanishing of the odd
  Bernoulli numbers `B'_{2n+1} = 0` (`zeta_neg_even`);
* the famous special values `ζ(0) = −1/2`, `ζ(−1) = −1/12`, `ζ(−2) = 0`, `ζ(−3) = 1/120`
  drop out of the same formula by reading off `B'_1, B'_2, B'_3, B'_4`.

The identity `ζ(−1) = −1/12` is the rigorous shadow of the (divergent) "1 + 2 + 3 + ⋯ = −1/12":
it is the regularized constant left over when the leading Faulhaber polynomial `½n(n+1)` is
analytically continued.

## Honest scope

The hard analytic core — the functional equation and the continuation of `ζ` to `ℂ` — is
Mathlib's. The new content here is the algebraic bridge identifying the subtracted Faulhaber
constant with `(p+1)·ζ(−p)`, the convention reconciliation, and the closed list of consequences.

Tags: number-theory, bernoulli, riemann-zeta, power-sums, faulhaber, analytic-continuation
-/

noncomputable section

namespace ArithmeticSeriesOQ04OQ03

open scoped Polynomial

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE VALUE FORMULA — ζ(−n) IN TERMS OF BERNOULLI NUMBERS

The answer to the open question, in both Mathlib conventions.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **ζ at negative integers (B′ convention)**: `ζ(−n) = −B'_{n+1}/(n+1)`.

    This is the classical formula `ζ(−n) = −B_{n+1}/(n+1)` of the open question, with the
    `B'_1 = +1/2` convention. Direct restatement of Mathlib's
    `riemannZeta_neg_nat_eq_bernoulli'`, the endpoint of the analytic continuation. -/
theorem zeta_neg_nat (n : ℕ) :
    riemannZeta (-(n : ℂ)) = -(bernoulli' (n + 1) : ℂ) / ((n : ℂ) + 1) :=
  riemannZeta_neg_nat_eq_bernoulli' n

/-- **ζ at negative integers (B convention)**: `ζ(−n) = (−1)^n · B_{n+1}/(n+1)`.

    The sign `(−1)^n` absorbs the `B_1 = −1/2` vs `B'_1 = +1/2` difference. Restatement of
    Mathlib's `riemannZeta_neg_nat_eq_bernoulli`. -/
theorem zeta_neg_nat_bernoulli (n : ℕ) :
    riemannZeta (-(n : ℂ)) = (-1) ^ n * (bernoulli (n + 1) : ℂ) / ((n : ℂ) + 1) :=
  riemannZeta_neg_nat_eq_bernoulli n

/-- The two value formulas agree: `−B'_{n+1} = (−1)^n · B_{n+1}`. This is the numerator
    reconciliation of `zeta_neg_nat` and `zeta_neg_nat_bernoulli`, from
    `bernoulli' m = (−1)^m · B_m`. -/
theorem bernoulli_convention_eq (n : ℕ) :
    -(bernoulli' (n + 1) : ℂ) = (-1) ^ n * (bernoulli (n + 1) : ℂ) := by
  rw [show bernoulli' (n + 1) = (-1) ^ (n + 1) * bernoulli (n + 1) from
        bernoulli'_eq_bernoulli (n + 1)]
  push_cast
  ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE FAULHABER ↔ ζ BRIDGE

Faulhaber's polynomial identity subtracts the constant `B_{p+1}`. For p ≥ 1 that
constant is exactly `−(p+1)·ζ(−p)`.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- Faulhaber's Bernoulli-polynomial identity (Mathlib `sum_range_pow_eq_bernoulli_sub`):
    `(p+1)·∑_{k<n} k^p = B_{p+1}(n) − B_{p+1}`. The subtracted constant `B_{p+1}` is the
    object the bridge below identifies with `−(p+1)·ζ(−p)`. -/
theorem faulhaber_sum_eq (n p : ℕ) :
    ((p + 1 : ℚ) * ∑ k ∈ Finset.range n, (k : ℚ) ^ p) =
      (Polynomial.bernoulli p.succ).eval (n : ℚ) - bernoulli p.succ :=
  Polynomial.sum_range_pow_eq_bernoulli_sub n p

/-- The subtracted constant equals the constant term of the Bernoulli polynomial:
    `B_{p+1} = B_{p+1}(0)`. (Mathlib `Polynomial.bernoulli_eval_zero`.) -/
theorem faulhaber_constant_is_eval_zero (p : ℕ) :
    (Polynomial.bernoulli p.succ).eval 0 = bernoulli p.succ :=
  Polynomial.bernoulli_eval_zero p.succ

/-- **Clearing the denominator in the value formula**: for `p ≥ 1`,
    `(p+1)·ζ(−p) = −B_{p+1}`. (For `p ≥ 1` the two Bernoulli conventions coincide, since
    `B'_{p+1} = B_{p+1}` for `p+1 ≠ 1`.) -/
theorem zeta_neg_nat_mul (p : ℕ) (hp : 1 ≤ p) :
    ((p : ℂ) + 1) * riemannZeta (-(p : ℂ)) = -(bernoulli (p + 1) : ℂ) := by
  have hne : ((p : ℂ) + 1) ≠ 0 := by
    have : ((p : ℂ) + 1) = ((p + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [this]; exact_mod_cast Nat.succ_ne_zero p
  rw [riemannZeta_neg_nat_eq_bernoulli', bernoulli_eq_bernoulli'_of_ne_one (by omega : p + 1 ≠ 1)]
  field_simp

/-- **The Faulhaber ↔ ζ bridge.** For `p ≥ 1`, the constant `B_{p+1}` that Faulhaber's
    identity `(p+1)·∑_{k<n} k^p = B_{p+1}(n) − B_{p+1}` subtracts off is exactly
    `−(p+1)·ζ(−p)`. Thus the analytically-continued zeta value is, up to the factor `(p+1)`
    and a sign, the "missing constant term" of the power-sum polynomial. -/
theorem faulhaber_constant_eq_zeta (p : ℕ) (hp : 1 ≤ p) :
    (bernoulli (p + 1) : ℂ) = -(((p : ℂ) + 1) * riemannZeta (-(p : ℂ))) := by
  rw [zeta_neg_nat_mul p hp, neg_neg]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE TRIVIAL ZEROS — ζ(−2n) = 0

Direct from the vanishing of the odd Bernoulli numbers B'_{2n+1} = 0 (n ≥ 1).
═══════════════════════════════════════════════════════════════════════════════
-/

/-- **Trivial zeros of ζ**: `ζ(−2n) = 0` for `n ≥ 1`.

    From `zeta_neg_nat`, `ζ(−2n) = −B'_{2n+1}/(2n+1)`, and `B'_{2n+1} = 0` because `2n+1`
    is odd and `> 1`. These are exactly the trivial zeros at the negative even integers. -/
theorem zeta_neg_even (n : ℕ) (hn : 1 ≤ n) :
    riemannZeta (-((2 * n : ℕ) : ℂ)) = 0 := by
  rw [riemannZeta_neg_nat_eq_bernoulli',
    bernoulli'_eq_zero_of_odd ⟨n, by ring⟩ (by omega : 1 < 2 * n + 1)]
  simp

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: SPECIAL VALUES

ζ(0) = −1/2, ζ(−1) = −1/12, ζ(−2) = 0, ζ(−3) = 1/120 — read off from B'_1..B'_4.
═══════════════════════════════════════════════════════════════════════════════
-/

/-- `ζ(0) = −1/2`, derived from the value formula: `ζ(0) = −B'_1/1 = −1/2`. -/
theorem zeta_zero : riemannZeta 0 = -1 / 2 := by
  have h := riemannZeta_neg_nat_eq_bernoulli' 0
  rw [bernoulli'_one] at h
  rw [show (0 : ℂ) = -((0 : ℕ) : ℂ) by norm_num, h]
  push_cast
  norm_num

/-- `ζ(−1) = −1/12`, from `ζ(−1) = −B'_2/2 = −(1/6)/2`.

    This is the rigorous form of the regularized sum `1 + 2 + 3 + ⋯ "=" −1/12`. -/
theorem zeta_neg_one : riemannZeta (-(1 : ℂ)) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli' 1
  rw [bernoulli'_two] at h
  rw [show (-(1 : ℂ)) = -((1 : ℕ) : ℂ) by norm_num, h]
  push_cast
  norm_num

/-- `ζ(−2) = 0` — the first trivial zero. -/
theorem zeta_neg_two : riemannZeta (-(2 : ℂ)) = 0 := by
  rw [show (-(2 : ℂ)) = -((2 * 1 : ℕ) : ℂ) by norm_num]
  exact zeta_neg_even 1 le_rfl

/-- `ζ(−3) = 1/120`, from `ζ(−3) = −B'_4/4 = −(−1/30)/4`. -/
theorem zeta_neg_three : riemannZeta (-(3 : ℂ)) = 1 / 120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli' 3
  rw [bernoulli'_four] at h
  rw [show (-(3 : ℂ)) = -((3 : ℕ) : ℂ) by norm_num, h]
  push_cast
  norm_num

end ArithmeticSeriesOQ04OQ03

end -- noncomputable section

/-
## Summary

Answering parent OQ-04's third open question — deriving `ζ(−n) = −B_{n+1}/(n+1)` from the
power-sum / Faulhaber formula via analytic continuation:

**Value formula** (Mathlib endpoint of the analytic continuation):
- `zeta_neg_nat`:            `ζ(−n) = −B'_{n+1}/(n+1)`        (B′ convention, `B'_1 = +1/2`)
- `zeta_neg_nat_bernoulli`:  `ζ(−n) = (−1)^n·B_{n+1}/(n+1)`   (B convention)
- `bernoulli_convention_eq`: the two numerators agree.

**Faulhaber ↔ ζ bridge** (the new content):
- `faulhaber_sum_eq`:           `(p+1)·∑_{k<n} k^p = B_{p+1}(n) − B_{p+1}`.
- `zeta_neg_nat_mul`:           `(p+1)·ζ(−p) = −B_{p+1}` for `p ≥ 1`.
- `faulhaber_constant_eq_zeta`: the subtracted constant `B_{p+1}` equals `−(p+1)·ζ(−p)`.

**Trivial zeros**: `zeta_neg_even`: `ζ(−2n) = 0` for `n ≥ 1`, from `B'_{2n+1} = 0`.

**Special values**: `ζ(0) = −1/2`, `ζ(−1) = −1/12`, `ζ(−2) = 0`, `ζ(−3) = 1/120`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`. The analytic continuation
is Mathlib's; the bridge and consequences are the contribution.
-/

/-
# Euler's Criterion OQ-01-OQ-02-OQ-03: Jacobi-symbol supplementary laws for odd composite moduli

The parent leaf `euler-criterion-squares-oq-01-oq-02`
(`EulerCriterionSquaresOQ01OQ02.lean`) proved the two **supplementary laws of quadratic
reciprocity** for the *Legendre* symbol `(a | p)`, which is only defined for a prime modulus:

  `(−1 | p) = (−1)^((p−1)/2)`   and   `(2 | p) = (−1)^((p²−1)/8)`.

This leaf lifts those same mod-4 / mod-8 exponent formulas to the **Jacobi symbol**
`J(a | n)`, which is defined for arbitrary odd `n > 0` by extending the Legendre symbol
multiplicatively over the prime factorization of `n`. We show the clean closed forms
survive the passage from prime to composite modulus:

  `J(−1 | n) = (−1)^((n−1)/2)`   and   `J(2 | n) = (−1)^((n²−1)/8)`   for all odd `n`.

## What this proves

* `jacobiSym_neg_one` — `J(−1 | n) = (−1)^((n−1)/2)` for odd `n`.
* `jacobiSym_two`     — `J(2 | n) = (−1)^((n²−1)/8)` for odd `n`.
* `jacobiSym_mul_top` — top-argument multiplicativity `J(a·b | n) = J(a | n)·J(b | n)`.
* `jacobiSym_neg_one_eq_one_iff` — `J(−1 | n) = 1 ↔ n ≡ 1 (mod 4)`.
* `jacobiSym_two_eq_one_iff`     — `J(2 | n) = 1 ↔ n ≡ ±1 (mod 8)`.

## Method

For `J(−1 | n)` Mathlib's `jacobiSym.at_neg_one` gives `J(−1 | n) = χ₄ n`, and
`ZMod.χ₄_eq_neg_one_pow` already supplies `χ₄ n = (−1)^(n/2)`; since `n/2 = (n−1)/2`
for odd `n`, the exponent form follows immediately.

For `J(2 | n)` Mathlib's `jacobiSym.at_two` gives `J(2 | n) = χ₈ n`, but Mathlib has **no**
power-of-`(−1)` form for `χ₈`. The genuine content of this file is the elementary identity
`χ₈ n = (−1)^((n²−1)/8)` for odd `n`: a case analysis on `n mod 8 ∈ {1,3,5,7}`, where in
each class we compute `(n²−1)/8` explicitly (writing `n = 8k + r`) and read off its parity.

All results are machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/
import Mathlib

open ZMod
open scoped NumberTheorySymbols

namespace EulerCriterionSquaresOQ01OQ02OQ03

/-! ## First supplementary law: `J(−1 | n)` -/

/-- **First supplementary law for the Jacobi symbol.** For odd `n`,
`J(−1 | n) = (−1)^((n−1)/2)`.

Mathlib's `jacobiSym.at_neg_one` evaluates `J(−1 | n) = χ₄ n`, and `ZMod.χ₄_eq_neg_one_pow`
gives `χ₄ n = (−1)^(n/2)`; for odd `n` the Nat divisions `n/2` and `(n−1)/2` agree. -/
theorem jacobiSym_neg_one {n : ℕ} (hn : Odd n) :
    J(-1 | n) = (-1 : ℤ) ^ ((n - 1) / 2) := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.at_neg_one hn, χ₄_eq_neg_one_pow hn2]
  congr 1
  omega

/-! ## Second supplementary law: `J(2 | n)` -/

/-- The arithmetic heart of the second supplementary law: for odd `n`,
`χ₈ n = (−1)^((n²−1)/8)`.

Proof by case analysis on `n mod 8`. Writing `n = 8k + r` with `r ∈ {1,3,5,7}`, the
quotient `(n²−1)/8` is `2·(…)` when `r ∈ {1,7}` (so the sign is `+1`, matching `χ₈ n = 1`)
and `2·(…)+1` when `r ∈ {3,5}` (so the sign is `−1`, matching `χ₈ n = −1`). -/
theorem χ₈_eq_neg_one_pow {n : ℕ} (hn : n % 2 = 1) :
    χ₈ (n : ZMod 8) = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ n % 2 = 0)]
  obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + n % 8 := ⟨n / 8, by omega⟩
  have hr : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hr with hr | hr | hr | hr <;> rw [hr] at hk <;> subst hk
  · -- n = 8k + 1 : exponent even, χ₈ = 1
    rw [if_pos (by omega)]
    have hX : ((8 * k + 1) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + k) := by
      have h : (8 * k + 1) ^ 2 = 8 * (2 * (4 * k ^ 2 + k)) + 1 := by ring
      omega
    rw [hX, pow_mul, neg_one_sq, one_pow]
  · -- n = 8k + 3 : exponent odd, χ₈ = -1
    rw [if_neg (by omega)]
    have hX : ((8 * k + 3) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 3 * k) + 1 := by
      have h : (8 * k + 3) ^ 2 = 8 * (2 * (4 * k ^ 2 + 3 * k) + 1) + 1 := by ring
      omega
    rw [hX, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  · -- n = 8k + 5 : exponent odd, χ₈ = -1
    rw [if_neg (by omega)]
    have hX : ((8 * k + 5) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 5 * k + 1) + 1 := by
      have h : (8 * k + 5) ^ 2 = 8 * (2 * (4 * k ^ 2 + 5 * k + 1) + 1) + 1 := by ring
      omega
    rw [hX, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  · -- n = 8k + 7 : exponent even, χ₈ = 1
    rw [if_pos (by omega)]
    have hX : ((8 * k + 7) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 7 * k + 3) := by
      have h : (8 * k + 7) ^ 2 = 8 * (2 * (4 * k ^ 2 + 7 * k + 3)) + 1 := by ring
      omega
    rw [hX, pow_mul, neg_one_sq, one_pow]

/-- **Second supplementary law for the Jacobi symbol.** For odd `n`,
`J(2 | n) = (−1)^((n²−1)/8)`.

Mathlib's `jacobiSym.at_two` evaluates `J(2 | n) = χ₈ n`; the exponent form is the
elementary identity `χ₈_eq_neg_one_pow` proved above. -/
theorem jacobiSym_two {n : ℕ} (hn : Odd n) :
    J(2 | n) = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  rw [jacobiSym.at_two hn, χ₈_eq_neg_one_pow (Nat.odd_iff.mp hn)]

/-! ## Multiplicativity in the top argument -/

/-- **Top-argument multiplicativity** of the Jacobi symbol:
`J(a·b | n) = J(a | n)·J(b | n)`. This is the structural property that distinguishes the
Jacobi symbol from the Legendre symbol (it holds for every modulus, prime or not). -/
theorem jacobiSym_mul_top (a b : ℤ) (n : ℕ) :
    J(a * b | n) = J(a | n) * J(b | n) :=
  jacobiSym.mul_left a b n

/-! ## Residue-class forms -/

/-- `J(−1 | n) = 1` iff `n ≡ 1 (mod 4)`, for odd `n`. -/
theorem jacobiSym_neg_one_eq_one_iff {n : ℕ} (hn : Odd n) :
    J(-1 | n) = 1 ↔ n % 4 = 1 := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.at_neg_one hn, χ₄_nat_eq_if_mod_four, if_neg (by omega : ¬ n % 2 = 0)]
  constructor
  · intro h; by_contra hc; rw [if_neg (by omega)] at h; norm_num at h
  · intro h; rw [if_pos h]

/-- `J(2 | n) = 1` iff `n ≡ ±1 (mod 8)`, for odd `n`. -/
theorem jacobiSym_two_eq_one_iff {n : ℕ} (hn : Odd n) :
    J(2 | n) = 1 ↔ n % 8 = 1 ∨ n % 8 = 7 := by
  have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn
  rw [jacobiSym.at_two hn, χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ n % 2 = 0)]
  constructor
  · intro h; by_contra hc; rw [if_neg (by omega)] at h; norm_num at h
  · intro h; rw [if_pos h]

end EulerCriterionSquaresOQ01OQ02OQ03

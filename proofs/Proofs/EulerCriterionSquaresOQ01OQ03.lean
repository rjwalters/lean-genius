/-
# Euler's Criterion OQ-01-OQ-03: The Second Supplement — `2` is a QR mod `p` iff `p ≡ ±1 (mod 8)`

The parent leaf `euler-criterion-squares-oq-01` (`EulerCriterionSquaresOQ01.lean`) proves
**Euler's criterion**: for an odd prime `p` and `a ≠ 0` in `ZMod p`,

  `IsSquare a  ⟺  a^((p−1)/2) = 1`,   and dually   `¬ IsSquare a  ⟺  a^((p−1)/2) = −1`.

That criterion is universal but does not tell you, for a *fixed* `a`, which primes `p` make
`a` a square. This leaf carries out that computation for the smallest interesting case `a = 2`,
the classical **second supplementary law of quadratic reciprocity**:

  `IsSquare (2 : ZMod p)  ⟺  p ≡ 1 (mod 8) ∨ p ≡ 7 (mod 8)`,

with the complementary non-residue characterisation `p ≡ 3 (mod 8) ∨ p ≡ 5 (mod 8)`, and the
explicit **Euler-criterion bridge** linking the parent's exponential test to the mod-8 sign:

  `(2 : ZMod p)^((p−1)/2) = (−1 : ZMod p)^((p²−1)/8)`.

## What this proves

* `isSquare_two_iff`            — `IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7`.
* `not_isSquare_two_iff`        — `¬ IsSquare (2 : ZMod p) ↔ p % 8 = 3 ∨ p % 8 = 5`.
* `legendreSym_two_eq_chi8`     — `legendreSym p 2 = χ₈ p`.
* `legendreSym_two_eq_neg_one_pow` — `legendreSym p 2 = (−1)^((p²−1)/8)`.
* `two_pow_half_eq_neg_one_pow` — the bridge `(2)^((p−1)/2) = (−1)^((p²−1)/8)` in `ZMod p`.
* `isSquare_two_iff_legendreSym` — residuacity ⟺ symbol value, `IsSquare 2 ↔ legendreSym p 2 = 1`.
* Concrete corollaries: `2` is a residue mod `7, 17, 23` and a non-residue mod `5, 11, 13`.

## Method

The headline equivalence `isSquare_two_iff` is Mathlib's `ZMod.exists_sq_eq_two_iff`, restated
for the parent's odd-prime convention `[Fact (2 < p)]`. The non-residue complement is the
exhaustive case split `p % 8 ∈ {1,3,5,7}` (`p` odd) against the residue classes.

The mathematically substantive piece — distinct from the sibling Jacobi leaf, which states the
sign formula but has *no* residuacity interpretation — is the bridge back to the parent's
Euler-criterion exponential `2^((p−1)/2)`. Combining Mathlib's `legendreSym.eq_pow`
(`(legendreSym p 2 : ZMod p) = 2^(p/2)`), `legendreSym.at_two` (`legendreSym p 2 = χ₈ p`), and
the elementary closed form `χ₈ p = (−1)^((p²−1)/8)` (a mod-8 case analysis, reproved here since
Mathlib supplies only the χ₄ analogue) yields the second supplement in its Gauss-sum exponent
form and exhibits `±1 = (−1)^((p²−1)/8)` as exactly the value of Euler's exponential test at `2`.

All results are machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide` (concrete checks
use `decide`).
-/
import Mathlib

open ZMod

namespace EulerCriterionSquaresOQ01OQ03

variable (p : ℕ) [Fact p.Prime] [Fact (2 < p)]

omit [Fact p.Prime] in
/-- An odd prime is not `2`. -/
theorem ne_two : p ≠ 2 := by have : 2 < p := Fact.out; omega

/-- An odd prime is odd. -/
theorem p_mod_two : p % 2 = 1 :=
  (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by have := (Fact.out : 2 < p); omega)

/-- For an odd prime, `p / 2 = (p − 1) / 2` — the exponent in Euler's criterion. -/
theorem half_eq : p / 2 = (p - 1) / 2 := by have := p_mod_two p; omega

/-- An odd prime lies in one of the four reduced residue classes mod `8`. -/
theorem mod_eight_cases : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by
  have := p_mod_two p; omega

/-! ## The residue / non-residue characterisation -/

/-- **Second supplementary law.** `2` is a quadratic residue mod an odd prime `p` iff
`p ≡ 1` or `7 (mod 8)`. This is Mathlib's `ZMod.exists_sq_eq_two_iff`, restated for the parent's
odd-prime convention. -/
theorem isSquare_two_iff : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  ZMod.exists_sq_eq_two_iff (ne_two p)

/-- **Non-residue complement.** `2` is a quadratic *non*-residue mod an odd prime `p` iff
`p ≡ 3` or `5 (mod 8)`. The complement of `isSquare_two_iff` across the four odd classes. -/
theorem not_isSquare_two_iff : ¬ IsSquare (2 : ZMod p) ↔ p % 8 = 3 ∨ p % 8 = 5 := by
  rw [isSquare_two_iff]
  have := mod_eight_cases p
  omega

/-! ## The Legendre symbol at `2` and the `(−1)^((p²−1)/8)` exponent -/

/-- The arithmetic heart of the second supplement: for odd `n`, `χ₈ n = (−1)^((n²−1)/8)`.

Mathlib provides the χ₄ analogue (`ZMod.χ₄_eq_neg_one_pow`) but no power-of-`(−1)` form for χ₈.
Proof by case analysis on `n mod 8`: writing `n = 8k + r` with `r ∈ {1,3,5,7}`, the quotient
`(n²−1)/8` is `2·(…)` when `r ∈ {1,7}` (sign `+1`) and `2·(…)+1` when `r ∈ {3,5}` (sign `−1`). -/
theorem chi8_eq_neg_one_pow {n : ℕ} (hn : n % 2 = 1) :
    χ₈ (n : ZMod 8) = (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  rw [χ₈_nat_eq_if_mod_eight, if_neg (by omega : ¬ n % 2 = 0)]
  obtain ⟨k, hk⟩ : ∃ k, n = 8 * k + n % 8 := ⟨n / 8, by omega⟩
  have hr : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
  rcases hr with hr | hr | hr | hr <;> rw [hr] at hk <;> subst hk
  · rw [if_pos (by omega)]
    have hX : ((8 * k + 1) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + k) := by
      have h : (8 * k + 1) ^ 2 = 8 * (2 * (4 * k ^ 2 + k)) + 1 := by ring
      omega
    rw [hX, pow_mul, neg_one_sq, one_pow]
  · rw [if_neg (by omega)]
    have hX : ((8 * k + 3) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 3 * k) + 1 := by
      have h : (8 * k + 3) ^ 2 = 8 * (2 * (4 * k ^ 2 + 3 * k) + 1) + 1 := by ring
      omega
    rw [hX, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  · rw [if_neg (by omega)]
    have hX : ((8 * k + 5) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 5 * k + 1) + 1 := by
      have h : (8 * k + 5) ^ 2 = 8 * (2 * (4 * k ^ 2 + 5 * k + 1) + 1) + 1 := by ring
      omega
    rw [hX, pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
  · rw [if_pos (by omega)]
    have hX : ((8 * k + 7) ^ 2 - 1) / 8 = 2 * (4 * k ^ 2 + 7 * k + 3) := by
      have h : (8 * k + 7) ^ 2 = 8 * (2 * (4 * k ^ 2 + 7 * k + 3)) + 1 := by ring
      omega
    rw [hX, pow_mul, neg_one_sq, one_pow]

/-- **Legendre symbol at `2`.** `legendreSym p 2 = χ₈ p` (Mathlib's `legendreSym.at_two`). -/
theorem legendreSym_two_eq_chi8 : legendreSym p 2 = χ₈ p :=
  legendreSym.at_two (ne_two p)

/-- **Second supplement, exponent form.** `legendreSym p 2 = (−1)^((p²−1)/8)`. -/
theorem legendreSym_two_eq_neg_one_pow :
    legendreSym p 2 = (-1 : ℤ) ^ ((p ^ 2 - 1) / 8) := by
  rw [legendreSym_two_eq_chi8 p, chi8_eq_neg_one_pow (p_mod_two p)]

/-! ## The Euler-criterion bridge -/

/-- The parent's Euler-criterion exponential equals the Legendre symbol as an element of
`ZMod p`: `(2 : ZMod p)^((p−1)/2) = (legendreSym p 2 : ZMod p)`. Mathlib's `legendreSym.eq_pow`
gives the `p/2` form; `half_eq` rewrites the exponent to `(p−1)/2`. -/
theorem two_pow_half_eq_legendreSym :
    (2 : ZMod p) ^ ((p - 1) / 2) = ((legendreSym p 2 : ℤ) : ZMod p) := by
  rw [← half_eq p, legendreSym.eq_pow p 2]
  norm_cast

/-- **The Euler-criterion bridge.** Euler's exponential test at `2` is the mod-8 Gauss-sum sign:

  `(2 : ZMod p)^((p−1)/2) = (−1 : ZMod p)^((p²−1)/8)`.

This is the piece that connects the parent's universal criterion `a^((p−1)/2)` to the concrete
`p mod 8` statement — the residue/non-residue dichotomy for `2` is read off from the right-hand
sign being `+1` (for `p ≡ ±1`) or `−1` (for `p ≡ ±3`). -/
theorem two_pow_half_eq_neg_one_pow :
    (2 : ZMod p) ^ ((p - 1) / 2) = (-1 : ZMod p) ^ ((p ^ 2 - 1) / 8) := by
  rw [two_pow_half_eq_legendreSym p, legendreSym_two_eq_neg_one_pow p]
  push_cast
  ring

/-! ## Residuacity ⟺ symbol value (the prime-only feature) -/

/-- `(2 : ZMod p) ≠ 0` for an odd prime `p`. -/
theorem two_ne_zero : (2 : ZMod p) ≠ 0 := by
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    have : 2 < p := Fact.out
    omega
  simpa using h2

/-- **Residuacity is symbol value `+1`.** For the *prime* modulus, `2` is a quadratic residue iff
`legendreSym p 2 = 1`. (This equivalence is what fails for composite Jacobi moduli, where the
sibling leaf can state the sign formula but not the residue interpretation.) -/
theorem isSquare_two_iff_legendreSym : IsSquare (2 : ZMod p) ↔ legendreSym p 2 = 1 := by
  rw [legendreSym.eq_one_iff p (by exact_mod_cast two_ne_zero p)]
  norm_num

/-! ## Concrete checks (decide, no native_decide) -/

/-- `2` is a quadratic residue mod `7` (`p ≡ 7 (mod 8)`), witnessed by `3² = 2`. -/
theorem isSquare_two_mod_seven : IsSquare (2 : ZMod 7) := ⟨3, by decide⟩

/-- `2` is a quadratic residue mod `17` (`p ≡ 1 (mod 8)`), witnessed by `6² = 36 = 2`. -/
theorem isSquare_two_mod_seventeen : IsSquare (2 : ZMod 17) := ⟨6, by decide⟩

/-- `2` is a quadratic residue mod `23` (`p ≡ 7 (mod 8)`), witnessed by `5² = 25 = 2`. -/
theorem isSquare_two_mod_twentythree : IsSquare (2 : ZMod 23) := ⟨5, by decide⟩

/-- `2` is a quadratic non-residue mod `5` (`p ≡ 5 (mod 8)`). -/
theorem not_isSquare_two_mod_five : ¬ IsSquare (2 : ZMod 5) := by decide

/-- `2` is a quadratic non-residue mod `11` (`p ≡ 3 (mod 8)`). -/
theorem not_isSquare_two_mod_eleven : ¬ IsSquare (2 : ZMod 11) := by decide

/-- `2` is a quadratic non-residue mod `13` (`p ≡ 5 (mod 8)`). -/
theorem not_isSquare_two_mod_thirteen : ¬ IsSquare (2 : ZMod 13) := by decide

end EulerCriterionSquaresOQ01OQ03

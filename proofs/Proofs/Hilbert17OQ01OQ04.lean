/-
# Hilbert's 17th Problem, OQ-01 / OQ-04: the *minimal-denominator* Motzkin certificate

Parent entry: `hilbert-17-oq-01` (`Hilbert17OQ01.lean`), on the **Pfister bound** for the
number of rational-function squares needed to write a positive-semidefinite polynomial as
a sum of squares.  In `n` variables Pfister's theorem gives the universal bound `2ⁿ`; for
`n = 2` this is `4`.

The sibling entry `hilbert-17-oq-03-oq-01` (`Hilbert17MotzkinRationalSOS.lean`) already
exhibits a fully machine-checked rational sum-of-squares certificate for the **Motzkin
polynomial**

  M(x, y) = x⁴y² + x²y⁴ − 3x²y² + 1,

the canonical PSD-but-not-polynomial-SOS form, but it uses the *non-minimal* multiplier
`4 + 4x² + 4y² = 4·(x² + y² + 1)`.  What was missing — and is the literal content of OQ-04 —
is the **classical denominator certificate**, with multiplier exactly

  D(x, y) = x² + y² + 1   (= 1² + x² + y²,  itself a sum of three squares).

`x² + y² + 1` is the canonical, degree-minimal SOS denominator for Motzkin (Reznick); the
factor of `4` in the sibling file is only there to clear the half-integers below.

## The certificate

The heart is the single polynomial identity (cleared of its common factor `4`, so that it
closes by `ring` with integer coefficients):

  4 · D · M
      = (2xy − x³y − xy³)²            (three copies)
      + (x³y − xy³)²
      + (2x − 2xy²)²
      + (2y − 2x²y)²
      + (2 − 2x²y²)².

Dividing by `4` in the field of rational functions `ℝ(x, y)` gives the **minimal-denominator
certificate** itself,

  (x² + y² + 1) · M
      = 3·( xy − ½(x³y + xy³) )²
      + ( ½(x³y − xy³) )²
      + ( x − xy² )²
      + ( y − x²y )²
      + ( 1 − x²y² )²,

a sum of `7` squares of rational functions whose multiplier is the minimal denominator
`x² + y² + 1`.  Because `D = 1² + x² + y²` is itself a sum of squares, multiplying through
once more and using that a product of two sums of squares is a sum of squares (plain
distributivity, `(Σpᵢ²)(Σdⱼ²) = Σ(pᵢdⱼ)²`) yields

  M = Σ (rational function)²    with denominator exactly `x² + y² + 1`

(`motzkin_isSOS_ratFunc_minimalDenom`).  This is Hilbert's 17th problem solved
*constructively, with the minimal classical denominator*, for the Motzkin polynomial.

## On the Pfister bound

Pfister's `2² = 4` bound guarantees Motzkin is a sum of **four** rational-function squares.
The explicit minimal-denominator certificate here uses `7` squares over `ℚ` (equivalently
`5` over `ℝ`, since the three repeated squares combine to one `(√3·…)²`).  Motzkin sits on
the boundary of the SOS cone, so its Gram matrix at the minimal denominator is singular and
of rank `5`; closing the gap to the Pfister-optimal `4` squares is the natural open
follow-up.

## Results
* `four_mul_denom_mul_motzkin`         — the integer SOS Positivstellensatz certificate
                                         `4·(x²+y²+1)·M = Σ (seven squares)`.
* `denom_mul_motzkin_eq_rf`            — the **minimal-denominator** certificate
                                         `(x²+y²+1)·M = Σ (seven rational-function squares)`.
* `denom_isSumOfSquares`               — `x² + y² + 1 = 1² + x² + y²` is a sum of squares.
* `motzkin_isSOS_ratFunc_minimalDenom` — `M` is a sum of squares of rational functions with
                                         denominator exactly `x² + y² + 1`.
-/

import Mathlib

namespace Hilbert17OQ01OQ04

open MvPolynomial

noncomputable section

/-- The two variables of `ℝ[x, y]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 2) ℝ)
local notation "y" => (X 1 : MvPolynomial (Fin 2) ℝ)

/-- The **Motzkin polynomial** `M(x, y) = x⁴y² + x²y⁴ − 3x²y² + 1`, defined exactly as in
the parent entries. -/
def motzkin : MvPolynomial (Fin 2) ℝ :=
  x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1

/-- The **minimal classical denominator** `D(x, y) = x² + y² + 1 = 1² + x² + y²`. -/
def denom : MvPolynomial (Fin 2) ℝ := x ^ 2 + y ^ 2 + 1

/-! ### Sum-of-squares predicates -/

/-- A multivariate polynomial is a sum of squares of polynomials. -/
def IsSumOfSquaresMv (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin 2) ℝ), p = ∑ i, q i ^ 2

/-- The field of rational functions `ℝ(x, y)` in two variables. -/
abbrev RF : Type := FractionRing (MvPolynomial (Fin 2) ℝ)

/-- The embedding `ℝ[x, y] ↪ ℝ(x, y)`. -/
abbrev toRF : MvPolynomial (Fin 2) ℝ →+* RF := algebraMap _ _

/-- An element of the rational function field is a (finite) sum of squares of rational
functions. -/
def IsSumOfSquaresRF (z : RF) : Prop :=
  ∃ (m : ℕ) (g : Fin m → RF), z = ∑ i, g i ^ 2

/-! ### The integer (cleared) certificate -/

/-- The five generators of the cleared certificate (the first appears with multiplicity
three).  These are the square roots of `4·(x²+y²+1)·M`. -/
def P0 : MvPolynomial (Fin 2) ℝ := 2 * x * y - x ^ 3 * y - x * y ^ 3
def P1 : MvPolynomial (Fin 2) ℝ := x ^ 3 * y - x * y ^ 3
def P2 : MvPolynomial (Fin 2) ℝ := 2 * x - 2 * (x * y ^ 2)
def P3 : MvPolynomial (Fin 2) ℝ := 2 * y - 2 * (x ^ 2 * y)
def P4 : MvPolynomial (Fin 2) ℝ := 2 - 2 * (x ^ 2 * y ^ 2)

/-- The seven square roots of `4·(x²+y²+1)·M`. -/
def qv : Fin 7 → MvPolynomial (Fin 2) ℝ := ![P0, P0, P0, P1, P2, P3, P4]

/-- The three square roots of the minimal denominator `x²+y²+1 = 1² + x² + y²`. -/
def dv : Fin 3 → MvPolynomial (Fin 2) ℝ := ![1, x, y]

/-- **The cleared SOS Positivstellensatz certificate** (integer coefficients, closed by
`ring`): `4·(x²+y²+1)·M = 3·P0² + P1² + P2² + P3² + P4²`. -/
theorem four_mul_denom_mul_motzkin :
    (4 : MvPolynomial (Fin 2) ℝ) * (denom * motzkin)
      = P0 ^ 2 + P0 ^ 2 + P0 ^ 2 + P1 ^ 2 + P2 ^ 2 + P3 ^ 2 + P4 ^ 2 := by
  simp only [denom, motzkin, P0, P1, P2, P3, P4]
  ring

/-- `4·(x²+y²+1)·M` is a sum of squares of polynomials (seven squares). -/
theorem four_mul_denom_mul_motzkin_isSumOfSquares :
    IsSumOfSquaresMv ((4 : MvPolynomial (Fin 2) ℝ) * (denom * motzkin)) := by
  refine ⟨7, qv, ?_⟩
  rw [Fin.sum_univ_seven]
  simp only [qv, Matrix.cons_val]
  exact four_mul_denom_mul_motzkin

/-- The minimal denominator `x² + y² + 1 = 1² + x² + y²` is a sum of squares. -/
theorem denom_isSumOfSquares : IsSumOfSquaresMv denom := by
  refine ⟨3, dv, ?_⟩
  rw [Fin.sum_univ_three]
  simp only [dv, Matrix.cons_val, denom]
  ring

/-! ### The minimal-denominator certificate, in `ℝ(x, y)` -/

/-- The seven square roots of the **minimal-denominator** certificate `(x²+y²+1)·M`, as
rational functions: `P0/2` (three times), `P1/2`, and `P2/2, P3/2, P4/2`. -/
def rv : Fin 7 → RF :=
  ![toRF P0 / 2, toRF P0 / 2, toRF P0 / 2, toRF P1 / 2,
    toRF P2 / 2, toRF P3 / 2, toRF P4 / 2]

/-- **The minimal-denominator Motzkin certificate.**  In the field of rational functions,

  `(x² + y² + 1) · M = (P0/2)² + (P0/2)² + (P0/2)² + (P1/2)² + (P2/2)² + (P3/2)² + (P4/2)²`,

a sum of seven squares with multiplier exactly the minimal denominator `x² + y² + 1`. -/
theorem denom_mul_motzkin_eq_rf :
    toRF denom * toRF motzkin = ∑ i, rv i ^ 2 := by
  have key := congrArg toRF four_mul_denom_mul_motzkin
  simp only [map_mul, map_add, map_pow, map_ofNat] at key
  rw [Fin.sum_univ_seven]
  simp only [rv, Matrix.cons_val, div_pow]
  rw [show ((2 : RF)) ^ 2 = 4 by norm_num]
  linear_combination key / 4

/-! ### The rational-function corollary (minimal-denominator Artin for Motzkin) -/

/-- The minimal denominator is nonzero in `ℝ[x, y]` (its constant term is `1`). -/
theorem denom_ne_zero : denom ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ => (0 : ℝ))) h
  simp only [denom, map_add, map_pow, eval_X, map_one, map_zero] at this
  norm_num at this

/-- The image of the minimal denominator in `ℝ(x, y)` is nonzero. -/
theorem toRF_denom_ne_zero : toRF denom ≠ 0 := by
  have hinj : Function.Injective (toRF : MvPolynomial (Fin 2) ℝ → RF) :=
    IsFractionRing.injective (MvPolynomial (Fin 2) ℝ) RF
  simpa [map_eq_zero_iff _ hinj] using denom_ne_zero

/-- The 21-term product identity, as polynomials:
`Σ_{i<7, j<3} (qᵢ·dⱼ)² = (4·(x²+y²+1)·M)·(x²+y²+1)`.  Both sides are concrete polynomials,
so `ring` closes it. -/
theorem product_identity :
    (∑ p : Fin 7 × Fin 3, (qv p.1 * dv p.2) ^ 2)
      = ((4 : MvPolynomial (Fin 2) ℝ) * (denom * motzkin)) * denom := by
  rw [Fintype.sum_prod_type]
  simp only [qv, dv, Fin.sum_univ_seven, Fin.sum_univ_three, Matrix.cons_val]
  simp only [denom, motzkin, P0, P1, P2, P3, P4]
  ring

/-- **Hilbert's 17th problem, constructively, with the minimal classical denominator, for
Motzkin.**  The Motzkin polynomial is a sum of squares of rational functions
`M = Σ (qᵢ·dⱼ / (2·(x²+y²+1)))²`, whose common denominator is the minimal classical
denominator `x² + y² + 1` (the leading `2` only rescales the numerators). -/
theorem motzkin_isSOS_ratFunc_minimalDenom : IsSumOfSquaresRF (toRF motzkin) := by
  set a : RF := toRF denom with ha
  have ha0 : a ≠ 0 := toRF_denom_ne_zero
  -- `M = Σ (qᵢ·dⱼ / (2a))²`, indexed by `Fin 7 × Fin 3`.
  have key : toRF motzkin
      = ∑ p : Fin 7 × Fin 3, (toRF (qv p.1 * dv p.2) / (2 * a)) ^ 2 := by
    have e1 : (∑ p : Fin 7 × Fin 3, (toRF (qv p.1 * dv p.2) / (2 * a)) ^ 2)
        = toRF (∑ p : Fin 7 × Fin 3, (qv p.1 * dv p.2) ^ 2) / (2 * a) ^ 2 := by
      rw [map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [div_pow, map_pow]
    rw [e1, product_identity]
    simp only [map_mul, map_add, map_pow, map_ofNat, ← ha]
    field_simp
    ring
  -- Reindex `Fin 7 × Fin 3 ≃ Fin 21`.
  let e : Fin 7 × Fin 3 ≃ Fin 21 := finProdFinEquiv
  refine ⟨21, fun k => (toRF (qv (e.symm k).1 * dv (e.symm k).2) / (2 * a)), ?_⟩
  rw [key]
  exact (Equiv.sum_comp e.symm
    (fun p : Fin 7 × Fin 3 => (toRF (qv p.1 * dv p.2) / (2 * a)) ^ 2)).symm

end

end Hilbert17OQ01OQ04

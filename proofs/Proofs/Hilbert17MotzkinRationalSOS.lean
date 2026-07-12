/-
# Hilbert's 17th Problem, made constructive for the Motzkin polynomial

Parent entry: `hilbert-17` (`Hilbert17SumOfSquares.lean`), whose headline statement —
Artin's theorem, that every nonnegative real polynomial is a sum of squares of
*rational functions* — is necessarily axiomatized (`artin_hilbert17`), since the
general proof needs real-closed-field model theory.

The companion fact in that file, that the Motzkin polynomial

  M(x, y) = x⁴y² + x²y⁴ - 3x²y² + 1

is **not** a sum of squares of *polynomials*, is likewise carried as an axiom
(`motzkin_not_sos_polynomial_aux`).  What was missing is the *positive* side made
explicit: a fully machine-checked witness that Motzkin nevertheless **is** a sum of
squares of rational functions, i.e. a concrete instance of Artin's theorem for the
canonical example.  This file supplies exactly that, with `0` axioms.

## The certificate

The heart is a single polynomial identity (an SOS *Positivstellensatz certificate*):

  (4 + 4x² + 4y²) · M(x, y)
      = (2xy - x³y - xy³)²            (three copies)
      + (x³y - xy³)²
      + (2x - 2xy²)²
      + (2y - 2x²y)²
      + (2 - 2x²y²)²

Every coefficient is an integer, so the identity is closed by `ring`.  Because the
multiplier `4 + 4x² + 4y² = 2² + (2x)² + (2y)²` is itself a sum of squares, dividing
through in the field of rational functions and using that a product of two sums of
squares is a sum of squares yields

  M = Σ (rational function)²            (`motzkin_isSOS_ratFunc`).

This is Hilbert's 17th problem solved *constructively* for Motzkin: the abstract
existence axiom is replaced, for this polynomial, by an exhibited certificate.

The SOS multiplier was found by solving the associated semidefinite Gram-matrix
feasibility problem; Motzkin sits on the boundary of the SOS cone, and the rational
Gram matrix factors into the five squares above.

## Results
* `multiplier_mul_motzkin_eq`   — the integer SOS Positivstellensatz certificate.
* `motzkin_mul_isSumOfSquares`  — `(4 + 4x² + 4y²)·M` is a polynomial sum of squares.
* `multiplier_isSumOfSquares`   — the multiplier `4 + 4x² + 4y²` is a sum of squares.
* `motzkin_isSOS_ratFunc`       — `M` is a sum of squares of rational functions.
-/

import Mathlib

namespace Hilbert17MotzkinRationalSOS

open MvPolynomial

noncomputable section

/-- The two variables of `ℝ[x, y]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 2) ℝ)
local notation "y" => (X 1 : MvPolynomial (Fin 2) ℝ)

/-- The **Motzkin polynomial** `M(x, y) = x⁴y² + x²y⁴ - 3x²y² + 1`, defined exactly as
in the parent entry `Hilbert17SumOfSquares.lean`. -/
def motzkin : MvPolynomial (Fin 2) ℝ :=
  x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 - 3 * x ^ 2 * y ^ 2 + 1

/-- The SOS **multiplier** `4 + 4x² + 4y² = 2² + (2x)² + (2y)²`. -/
def multiplier : MvPolynomial (Fin 2) ℝ := 4 + 4 * x ^ 2 + 4 * y ^ 2

/-! ### Sum-of-squares predicates -/

/-- A multivariate polynomial is a sum of squares of polynomials. -/
def IsSumOfSquaresMv (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin 2) ℝ), p = ∑ i, q i ^ 2

/-- The field of rational functions `ℝ(x, y)` in two variables. -/
abbrev RF : Type := FractionRing (MvPolynomial (Fin 2) ℝ)

/-- The embedding `ℝ[x, y] ↪ ℝ(x, y)`. -/
abbrev toRF : MvPolynomial (Fin 2) ℝ →+* RF := algebraMap _ _

/-- An element of the rational function field is a (finite) sum of squares of
rational functions. -/
def IsSumOfSquaresRF (z : RF) : Prop :=
  ∃ (m : ℕ) (g : Fin m → RF), z = ∑ i, g i ^ 2

/-! ### The polynomial SOS certificate -/

/-- The five generators of the certificate (the first appears with multiplicity three). -/
def G0 : MvPolynomial (Fin 2) ℝ := 2 * x * y - x ^ 3 * y - x * y ^ 3
def G1 : MvPolynomial (Fin 2) ℝ := x ^ 3 * y - x * y ^ 3
def G2 : MvPolynomial (Fin 2) ℝ := 2 * x - 2 * (x * y ^ 2)
def G3 : MvPolynomial (Fin 2) ℝ := 2 * y - 2 * (x ^ 2 * y)
def G4 : MvPolynomial (Fin 2) ℝ := 2 - 2 * (x ^ 2 * y ^ 2)

/-- The seven square roots of `(4 + 4x² + 4y²)·M`. -/
def qv : Fin 7 → MvPolynomial (Fin 2) ℝ := ![G0, G0, G0, G1, G2, G3, G4]

/-- The three square roots of the multiplier `4 + 4x² + 4y² = 2² + (2x)² + (2y)²`. -/
def dv : Fin 3 → MvPolynomial (Fin 2) ℝ := ![2, 2 * x, 2 * y]

/-- **The SOS Positivstellensatz certificate for Motzkin** (integer coefficients,
closed by `ring`):
`(4 + 4x² + 4y²)·M = 3·G0² + G1² + G2² + G3² + G4²`. -/
theorem multiplier_mul_motzkin_eq :
    multiplier * motzkin = G0 ^ 2 + G0 ^ 2 + G0 ^ 2 + G1 ^ 2 + G2 ^ 2 + G3 ^ 2 + G4 ^ 2 := by
  simp only [multiplier, motzkin, G0, G1, G2, G3, G4]
  ring

/-- `(4 + 4x² + 4y²)·M` is a sum of squares of polynomials (seven squares). -/
theorem motzkin_mul_isSumOfSquares : IsSumOfSquaresMv (multiplier * motzkin) := by
  refine ⟨7, qv, ?_⟩
  rw [Fin.sum_univ_seven]
  simp only [qv, Matrix.cons_val]
  exact multiplier_mul_motzkin_eq

/-- The multiplier `4 + 4x² + 4y² = 2² + (2x)² + (2y)²` is a sum of squares. -/
theorem multiplier_isSumOfSquares : IsSumOfSquaresMv multiplier := by
  refine ⟨3, dv, ?_⟩
  rw [Fin.sum_univ_three]
  simp only [dv, Matrix.cons_val]
  simp only [multiplier]
  ring

/-! ### The certificate proves nonnegativity (the Positivstellensatz payoff)

A sum-of-squares Positivstellensatz certificate `s·M = Σ squares` with a strictly
positive multiplier `s` is not merely a curiosity: it is a *proof* that `M` is
nonnegative.  Here the multiplier `4 + 4x² + 4y² ≥ 4 > 0` never vanishes, so
evaluating the certificate at any real point `v` gives
`s(v)·M(v) = Σ (Gᵢ(v))² ≥ 0` with `s(v) > 0`, whence `M(v) ≥ 0`.  This recovers
Motzkin nonnegativity (`Hilbert17SumOfSquares.motzkin_nonneg`, proved there by a
direct AM–GM `nlinarith`) as a *corollary of the exhibited certificate* — the
logical reason the certificate is worth having. -/

/-- The multiplier `4 + 4x² + 4y²` is strictly positive at every real point
(its value is at least its constant term `4`). -/
theorem multiplier_eval_pos (v : Fin 2 → ℝ) : 0 < eval v multiplier := by
  simp only [multiplier, map_add, map_mul, map_pow, map_ofNat, eval_X]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]

/-- **Certificate-based nonnegativity of Motzkin.**  For every real point `v`,
`M(v) ≥ 0`, derived from the SOS certificate `multiplier·M = Σ Gᵢ²` and the strict
positivity of the multiplier.  (Independent route to `motzkin_nonneg`.) -/
theorem motzkin_eval_nonneg (v : Fin 2 → ℝ) : 0 ≤ eval v motzkin := by
  have hpos := multiplier_eval_pos v
  have key : eval v multiplier * eval v motzkin
      = (eval v G0) ^ 2 + (eval v G0) ^ 2 + (eval v G0) ^ 2 + (eval v G1) ^ 2
        + (eval v G2) ^ 2 + (eval v G3) ^ 2 + (eval v G4) ^ 2 := by
    have h := congrArg (eval v) multiplier_mul_motzkin_eq
    simpa only [map_mul, map_add, map_pow] using h
  have hrhs : 0 ≤ eval v multiplier * eval v motzkin := by rw [key]; positivity
  rcases le_or_gt 0 (eval v motzkin) with h | h
  · exact h
  · exact absurd hrhs (not_le.mpr (mul_neg_of_pos_of_neg hpos h))

/-! ### The rational-function corollary (Artin for Motzkin, constructively) -/

/-- The multiplier is nonzero in `ℝ[x, y]` (its constant term is `4`). -/
theorem multiplier_ne_zero : multiplier ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ => (0 : ℝ))) h
  simp only [multiplier, map_add, map_mul, map_pow, map_ofNat, eval_X, map_zero] at this
  norm_num at this

/-- The image of the multiplier in `ℝ(x, y)` is nonzero. -/
theorem toRF_multiplier_ne_zero : toRF multiplier ≠ 0 := by
  have hinj : Function.Injective (toRF : MvPolynomial (Fin 2) ℝ → RF) :=
    IsFractionRing.injective (MvPolynomial (Fin 2) ℝ) RF
  simpa [map_eq_zero_iff _ hinj] using multiplier_ne_zero

/-- The 21-term product identity, as polynomials:
`Σ_{i<7, j<3} (qᵢ·dⱼ)² = ((4+4x²+4y²)·M)·(4+4x²+4y²)`.  Both sides are concrete
polynomials, so `ring` closes it. -/
theorem product_identity :
    (∑ p : Fin 7 × Fin 3, (qv p.1 * dv p.2) ^ 2) = (multiplier * motzkin) * multiplier := by
  rw [Fintype.sum_prod_type]
  simp only [qv, dv, Fin.sum_univ_seven, Fin.sum_univ_three, Matrix.cons_val]
  simp only [multiplier, motzkin, G0, G1, G2, G3, G4]
  ring

/-- **Hilbert's 17th problem, constructively, for Motzkin.**  The Motzkin polynomial
is a sum of squares of rational functions: `M = Σ (qᵢ·dⱼ / (4+4x²+4y²))²`.

This is the explicit, fully machine-checked witness for the canonical example
underlying the (necessarily axiomatized) general theorem `artin_hilbert17`. -/
theorem motzkin_isSOS_ratFunc : IsSumOfSquaresRF (toRF motzkin) := by
  set a : RF := toRF multiplier with ha
  have ha0 : a ≠ 0 := toRF_multiplier_ne_zero
  -- First, the statement indexed by `Fin 7 × Fin 3`.
  have key : toRF motzkin = ∑ p : Fin 7 × Fin 3, (toRF (qv p.1 * dv p.2) / a) ^ 2 := by
    have e1 : (∑ p : Fin 7 × Fin 3, (toRF (qv p.1 * dv p.2) / a) ^ 2)
        = toRF (∑ p : Fin 7 × Fin 3, (qv p.1 * dv p.2) ^ 2) / a ^ 2 := by
      rw [map_sum, Finset.sum_div]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [div_pow, map_pow]
    rw [e1, product_identity, map_mul, map_mul, ← ha]
    field_simp
  -- Reindex `Fin 7 × Fin 3 ≃ Fin 21`.
  let e : Fin 7 × Fin 3 ≃ Fin 21 := finProdFinEquiv
  refine ⟨21, fun k => (toRF (qv (e.symm k).1 * dv (e.symm k).2) / a), ?_⟩
  rw [key]
  exact (Equiv.sum_comp e.symm
    (fun p : Fin 7 × Fin 3 => (toRF (qv p.1 * dv p.2) / a) ^ 2)).symm

end

end Hilbert17MotzkinRationalSOS

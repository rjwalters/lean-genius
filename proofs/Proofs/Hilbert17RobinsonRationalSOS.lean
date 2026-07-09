/-
# Hilbert's 17th Problem, made constructive for the Robinson polynomial

Parent entry: `hilbert-17` (`Hilbert17SumOfSquares.lean`), whose headline statement —
Artin's theorem, that every nonnegative real polynomial is a sum of squares of
*rational functions* — is necessarily axiomatized (`artin_hilbert17`), since the
general proof needs real-closed-field model theory.

The companion fact in that file, that the Robinson polynomial

  R(x, y, z) = x⁶ + y⁶ + z⁶ - x⁴y² - y⁴z² - z⁴x² - x²y⁴ - y²z⁴ - z²x⁴ + 3x²y²z²

is **not** a sum of squares of *polynomials*, is fully machine-checked
(`Hilbert17RobinsonNotSOS.robinson_not_sos`).  What was missing is the *positive*
side made explicit: a fully machine-checked witness that Robinson nevertheless
**is** a sum of squares of rational functions, i.e. a concrete instance of
Artin's theorem for this second canonical extremal example (the ternary sextic
counterpart of the Motzkin form).  This file supplies exactly that, with `0`
axioms, mirroring `Hilbert17MotzkinRationalSOS.lean`.

## The certificate

The heart is a single polynomial identity (an SOS *Positivstellensatz certificate*):

  (4x² + 4y² + 4z²) · R(x, y, z)
      = (2x⁴ - x²y² - x²z² - y⁴ + 2y²z² - z⁴)²
      + (y⁴ - z⁴ - x²y² + x²z²)²        (three copies)
      + (2x³y - 2xy³)²
      + (2y³z - 2yz³)²
      + (2xz³ - 2x³z)²

Every coefficient is an integer, so the identity is closed by `ring`.  The
multiplier `4x² + 4y² + 4z² = (2x)² + (2y)² + (2z)²` is itself a sum of squares;
dividing through in the field of rational functions and using that a product of
two sums of squares is a sum of squares yields

  R = Σ (rational function)²            (`robinson_isSOS_ratFunc`).

This is Hilbert's 17th problem solved *constructively* for Robinson: the abstract
existence axiom is replaced, for this polynomial, by an exhibited certificate.

The SOS multiplier and Gram matrix were found by solving the associated
semidefinite feasibility problem; Robinson sits on the boundary of the SOS cone,
and after the substitution `u = x², v = y², w = z²` the certificate splits into a
rank-2 "even" block `(2q₁ - q₂)² + 3q₂²` and three rank-1 "odd" blocks
`(2·xy(x²-y²))²` and its cyclic images.

## Results
* `multiplier_mul_robinson_eq`  — the integer SOS Positivstellensatz certificate.
* `robinson_mul_isSumOfSquares` — `(4x²+4y²+4z²)·R` is a polynomial sum of squares.
* `multiplier_isSumOfSquares`   — the multiplier `4x²+4y²+4z²` is a sum of squares.
* `robinson_isSOS_ratFunc`      — `R` is a sum of squares of rational functions.
-/

import Mathlib

namespace Hilbert17RobinsonRationalSOS

open MvPolynomial

noncomputable section

/-- The three variables of `ℝ[x, y, z]`. -/
local notation "x" => (X 0 : MvPolynomial (Fin 3) ℝ)
local notation "y" => (X 1 : MvPolynomial (Fin 3) ℝ)
local notation "z" => (X 2 : MvPolynomial (Fin 3) ℝ)

/-- The **Robinson polynomial**
`R(x, y, z) = x⁶ + y⁶ + z⁶ - x⁴y² - y⁴z² - z⁴x² - x²y⁴ - y²z⁴ - z²x⁴ + 3x²y²z²`,
defined exactly as in the parent entry `Hilbert17SumOfSquares.lean`. -/
def robinson : MvPolynomial (Fin 3) ℝ :=
  x ^ 6 + y ^ 6 + z ^ 6
    - x ^ 4 * y ^ 2 - y ^ 4 * z ^ 2 - z ^ 4 * x ^ 2
    - x ^ 2 * y ^ 4 - y ^ 2 * z ^ 4 - z ^ 2 * x ^ 4
    + 3 * x ^ 2 * y ^ 2 * z ^ 2

/-- The SOS **multiplier** `4x² + 4y² + 4z² = (2x)² + (2y)² + (2z)²`. -/
def multiplier : MvPolynomial (Fin 3) ℝ := 4 * x ^ 2 + 4 * y ^ 2 + 4 * z ^ 2

/-! ### Sum-of-squares predicates -/

/-- A multivariate polynomial is a sum of squares of polynomials. -/
def IsSumOfSquaresMv (p : MvPolynomial (Fin 3) ℝ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin 3) ℝ), p = ∑ i, q i ^ 2

/-- The field of rational functions `ℝ(x, y, z)` in three variables. -/
abbrev RF : Type := FractionRing (MvPolynomial (Fin 3) ℝ)

/-- The embedding `ℝ[x, y, z] ↪ ℝ(x, y, z)`. -/
abbrev toRF : MvPolynomial (Fin 3) ℝ →+* RF := algebraMap _ _

/-- An element of the rational function field is a (finite) sum of squares of
rational functions. -/
def IsSumOfSquaresRF (r : RF) : Prop :=
  ∃ (m : ℕ) (g : Fin m → RF), r = ∑ i, g i ^ 2

/-! ### The polynomial SOS certificate -/

/-- The generators of the certificate.  `Q2` appears with multiplicity three;
`Q1` is the "even" block's other square, and `Ga, Gb, Gc` are the three cyclic
"odd" blocks `2·xy(x²-y²)`, `2·yz(y²-z²)`, `2·zx(z²-x²)`. -/
def Q1 : MvPolynomial (Fin 3) ℝ :=
  2 * x ^ 4 - x ^ 2 * y ^ 2 - x ^ 2 * z ^ 2 - y ^ 4 + 2 * y ^ 2 * z ^ 2 - z ^ 4
def Q2 : MvPolynomial (Fin 3) ℝ := y ^ 4 - z ^ 4 - x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2
def Ga : MvPolynomial (Fin 3) ℝ := 2 * x ^ 3 * y - 2 * x * y ^ 3
def Gb : MvPolynomial (Fin 3) ℝ := 2 * y ^ 3 * z - 2 * y * z ^ 3
def Gc : MvPolynomial (Fin 3) ℝ := 2 * x * z ^ 3 - 2 * x ^ 3 * z

/-- The seven square roots of `(4x²+4y²+4z²)·R`. -/
def qv : Fin 7 → MvPolynomial (Fin 3) ℝ := ![Q1, Q2, Q2, Q2, Ga, Gb, Gc]

/-- The three square roots of the multiplier `4x²+4y²+4z² = (2x)²+(2y)²+(2z)²`. -/
def dv : Fin 3 → MvPolynomial (Fin 3) ℝ := ![2 * x, 2 * y, 2 * z]

/-- **The SOS Positivstellensatz certificate for Robinson** (integer coefficients,
closed by `ring`):
`(4x²+4y²+4z²)·R = Q1² + 3·Q2² + Ga² + Gb² + Gc²`. -/
theorem multiplier_mul_robinson_eq :
    multiplier * robinson
      = Q1 ^ 2 + Q2 ^ 2 + Q2 ^ 2 + Q2 ^ 2 + Ga ^ 2 + Gb ^ 2 + Gc ^ 2 := by
  simp only [multiplier, robinson, Q1, Q2, Ga, Gb, Gc]
  ring

/-- `(4x²+4y²+4z²)·R` is a sum of squares of polynomials (seven squares). -/
theorem robinson_mul_isSumOfSquares : IsSumOfSquaresMv (multiplier * robinson) := by
  refine ⟨7, qv, ?_⟩
  rw [Fin.sum_univ_seven]
  simp only [qv, Matrix.cons_val]
  exact multiplier_mul_robinson_eq

/-- The multiplier `4x²+4y²+4z² = (2x)²+(2y)²+(2z)²` is a sum of squares. -/
theorem multiplier_isSumOfSquares : IsSumOfSquaresMv multiplier := by
  refine ⟨3, dv, ?_⟩
  rw [Fin.sum_univ_three]
  simp only [dv, Matrix.cons_val]
  simp only [multiplier]
  ring

/-! ### The rational-function corollary (Artin for Robinson, constructively) -/

/-- The multiplier is nonzero in `ℝ[x, y, z]` (its coefficient of `x²` is `4`). -/
theorem multiplier_ne_zero : multiplier ≠ 0 := by
  intro h
  have := congrArg (eval (fun i => if i = 0 then (1 : ℝ) else 0)) h
  simp only [multiplier, map_add, map_mul, map_pow, map_ofNat, eval_X, map_zero] at this
  norm_num at this

/-- The image of the multiplier in `ℝ(x, y, z)` is nonzero. -/
theorem toRF_multiplier_ne_zero : toRF multiplier ≠ 0 := by
  have hinj : Function.Injective (toRF : MvPolynomial (Fin 3) ℝ → RF) :=
    IsFractionRing.injective (MvPolynomial (Fin 3) ℝ) RF
  simpa [map_eq_zero_iff _ hinj] using multiplier_ne_zero

/-- The 21-term product identity, as polynomials:
`Σ_{i<7, j<3} (qᵢ·dⱼ)² = ((4x²+4y²+4z²)·R)·(4x²+4y²+4z²)`.  Both sides are concrete
polynomials, so `ring` closes it. -/
theorem product_identity :
    (∑ p : Fin 7 × Fin 3, (qv p.1 * dv p.2) ^ 2) = (multiplier * robinson) * multiplier := by
  rw [Fintype.sum_prod_type]
  simp only [qv, dv, Fin.sum_univ_seven, Fin.sum_univ_three, Matrix.cons_val]
  simp only [multiplier, robinson, Q1, Q2, Ga, Gb, Gc]
  ring

/-- **Hilbert's 17th problem, constructively, for Robinson.**  The Robinson
polynomial is a sum of squares of rational functions: `R = Σ (qᵢ·dⱼ / (4x²+4y²+4z²))²`.

This is the explicit, fully machine-checked witness for the second canonical
extremal example underlying the (necessarily axiomatized) general theorem
`artin_hilbert17`. -/
theorem robinson_isSOS_ratFunc : IsSumOfSquaresRF (toRF robinson) := by
  set a : RF := toRF multiplier with ha
  have ha0 : a ≠ 0 := toRF_multiplier_ne_zero
  -- First, the statement indexed by `Fin 7 × Fin 3`.
  have key : toRF robinson = ∑ p : Fin 7 × Fin 3, (toRF (qv p.1 * dv p.2) / a) ^ 2 := by
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

end Hilbert17RobinsonRationalSOS

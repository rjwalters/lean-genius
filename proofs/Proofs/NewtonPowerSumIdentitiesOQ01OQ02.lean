import Mathlib

/-
# The reverse Newton identities and their Toeplitz-determinant closed form

Parent: `newton-power-sum-identities-oq-01` (Newton's identities in low degree).

Newton's identities relate the elementary symmetric polynomials `eₖ = esymm σ R k`
and the power sums `pₖ = psum σ R k = ∑ᵢ Xᵢᵏ`.  The *forward* identities express
each power sum through the elementary symmetric polynomials; the parent entry
records `p₁, p₂, p₃` this way.  This entry proves the **reverse (dual) identities**,
expressing each elementary symmetric polynomial through the power sums.

Because inverting the recurrence introduces the factor `k!`, the division-free
statements carry that factor on the left:

* `e₁ = p₁`                              (`esymm_one_eq_psum`)
* `2·e₂ = p₁² − p₂`                      (`two_esymm_two`)
* `6·e₃ = p₁³ − 3 p₁ p₂ + 2 p₃`          (`six_esymm_three`)

These are identities in `MvPolynomial σ R` for **any** finite index type `σ` and
**any** commutative ring `R` — no division by `k!` is required, so the result is
strictly more general than a ℚ-algebra statement.

The classical closed form packages `k!·eₖ` as the determinant of a `k × k`
lower-Hessenberg *Toeplitz* matrix whose entries are the power sums, with the
super-diagonal carrying the integers `1, 2, …`:

* `1!·e₁ = det [p₁]`                                            (`esymm_one_det`)
* `2!·e₂ = det [[p₁, 1], [p₂, p₁]]`                             (`two_esymm_two_det`)
* `3!·e₃ = det [[p₁, 1, 0], [p₂, p₁, 2], [p₃, p₂, p₁]]`         (`six_esymm_three_det`)

The determinant form is exactly the shape requested by the parent's open question
and is absent from Mathlib.  We obtain it by expanding the small determinants with
`Matrix.det_fin_two_of` / `Matrix.det_fin_three` and matching against the scalar
reverse identities.

## Relation to existing gallery work

The scalar identities `e₁ = p₁` and `2·e₂ = p₁² − p₂` also appear in the
`amgm-inequality-oq-02-oq-01-oq-01-oq-02` entry (the abstract "same ℚ-subalgebra"
statement).  New here are the degree-3 reverse identity and, above all, the
explicit Toeplitz-determinant closed forms, valid over an arbitrary commutative ring.

## Axioms: 0 | Sorries: 0
-/

open Finset Matrix

namespace NewtonReverseOQ0102

open MvPolynomial

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-! ## Forward identities (stepping stones)

These reproduce the parent's low-degree forward Newton identities, obtained by
unrolling Mathlib's recurrence `psum_eq_mul_esymm_sub_sum`.  They are the inputs
from which the reverse identities are algebraically inverted. -/

/-- **Forward, degree 1:** `p₁ = e₁`. -/
theorem psum_one_eq : psum σ R 1 = esymm σ R 1 := by
  rw [psum_one, esymm_one]

/-- **Forward, degree 2:** `p₂ = e₁² − 2 e₂`. -/
theorem psum_two_eq :
    psum σ R 2 = esymm σ R 1 ^ 2 - 2 * esymm σ R 2 := by
  rw [psum_eq_mul_esymm_sub_sum σ R 2 (by norm_num)]
  have hset : {a ∈ Finset.antidiagonal 2 | a.1 ∈ Set.Ioo 0 2} = {(1, 1)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_singleton,
      Prod.mk.injEq]
    omega
  rw [hset, Finset.sum_singleton, psum_one_eq]
  push_cast
  ring

/-- **Forward, degree 3:** `p₃ = e₁³ − 3 e₁ e₂ + 3 e₃`. -/
theorem psum_three_eq :
    psum σ R 3 =
      esymm σ R 1 ^ 3 - 3 * esymm σ R 1 * esymm σ R 2 + 3 * esymm σ R 3 := by
  rw [psum_eq_mul_esymm_sub_sum σ R 3 (by norm_num)]
  have hset : {a ∈ Finset.antidiagonal 3 | a.1 ∈ Set.Ioo 0 3} = {(1, 2), (2, 1)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [hset, Finset.sum_pair (by decide), psum_two_eq, psum_one_eq]
  push_cast
  ring

/-! ## Reverse (dual) Newton identities

Each `k!·eₖ` is a polynomial in the power sums, obtained by inverting the forward
identities above.  Every step is a ring rearrangement, so no division by `k!`
occurs and the identities hold over an arbitrary commutative ring. -/

/-- **Reverse, degree 1:** `e₁ = p₁`. -/
theorem esymm_one_eq_psum : esymm σ R 1 = psum σ R 1 :=
  (psum_one_eq σ R).symm

/-- **Reverse, degree 2:** `2·e₂ = p₁² − p₂`. -/
theorem two_esymm_two :
    2 * esymm σ R 2 = psum σ R 1 ^ 2 - psum σ R 2 := by
  rw [psum_one_eq σ R]
  linear_combination psum_two_eq σ R

/-- **Reverse, degree 3:** `6·e₃ = p₁³ − 3 p₁ p₂ + 2 p₃`. -/
theorem six_esymm_three :
    6 * esymm σ R 3 =
      psum σ R 1 ^ 3 - 3 * psum σ R 1 * psum σ R 2 + 2 * psum σ R 3 := by
  have h1 := psum_one_eq σ R
  have h2 := psum_two_eq σ R
  have h3 := psum_three_eq σ R
  -- Substitute the two lower power sums, then invert the degree-3 forward identity.
  rw [h2, h1]
  linear_combination (-2 : MvPolynomial σ R) * h3

/-! ## Toeplitz-determinant closed form

`k!·eₖ = det Tₖ`, where `Tₖ` is the lower-Hessenberg Toeplitz matrix with the power
sums `p₁, p₂, …` down the first column and along the diagonals, and the integers
`1, 2, …, k−1` on the super-diagonal. -/

/-- **Determinant form, degree 1:** `1!·e₁ = det [p₁]`. -/
theorem esymm_one_det :
    esymm σ R 1 = (!![psum σ R 1] : Matrix (Fin 1) (Fin 1) (MvPolynomial σ R)).det := by
  rw [Matrix.det_fin_one_of, esymm_one_eq_psum]

/-- **Determinant form, degree 2:** `2!·e₂ = det [[p₁, 1], [p₂, p₁]]`. -/
theorem two_esymm_two_det :
    2 * esymm σ R 2 =
      (!![psum σ R 1, 1; psum σ R 2, psum σ R 1] :
        Matrix (Fin 2) (Fin 2) (MvPolynomial σ R)).det := by
  rw [Matrix.det_fin_two_of]
  linear_combination two_esymm_two σ R

/-- **Determinant form, degree 3:**
`3!·e₃ = det [[p₁, 1, 0], [p₂, p₁, 2], [p₃, p₂, p₁]]`. -/
theorem six_esymm_three_det :
    6 * esymm σ R 3 =
      (!![psum σ R 1, 1, 0; psum σ R 2, psum σ R 1, 2; psum σ R 3, psum σ R 2, psum σ R 1] :
        Matrix (Fin 3) (Fin 3) (MvPolynomial σ R)).det := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.empty_val']
  linear_combination six_esymm_three σ R

/-! ## Worked example

Over `R = ℤ` with two variables `σ = Fin 2`, the reverse identities specialise to
the familiar symmetric-function formulas.  For instance with `X₀, X₁` we have
`p₁ = X₀ + X₁`, `p₂ = X₀² + X₁²`, and `2·e₂ = 2·X₀X₁ = p₁² − p₂`. -/

/-- Sanity check of the degree-2 determinant identity specialised to `Fin 2` over `ℤ`. -/
example :
    2 * esymm (Fin 2) ℤ 2 =
      (!![psum (Fin 2) ℤ 1, 1; psum (Fin 2) ℤ 2, psum (Fin 2) ℤ 1] :
        Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℤ)).det :=
  two_esymm_two_det (Fin 2) ℤ

end NewtonReverseOQ0102

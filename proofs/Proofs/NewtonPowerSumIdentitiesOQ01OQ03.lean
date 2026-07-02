import Mathlib

/-
# The forward Girard–Waring determinant: power sums as determinants in the eₖ

Parent: `newton-power-sum-identities-oq-01` (Newton's identities in low degree).

Newton's identities relate the elementary symmetric polynomials `eₖ = esymm σ R k`
and the power sums `pₖ = psum σ R k = ∑ᵢ Xᵢᵏ`.  The parent entry records the
*forward* closed forms `p₁ = e₁`, `p₂ = e₁² − 2e₂`, `p₃ = e₁³ − 3e₁e₂ + 3e₃`, and
the sibling entry `newton-power-sum-identities-oq-01-oq-02` records the **reverse**
Toeplitz-determinant form `k!·eₖ = det Tₖ`, a determinant whose entries are the
power sums.

This entry proves the **dual determinant identity in the other direction**: each
power sum `pₖ` is *itself* the determinant of a `k × k` lower-Hessenberg matrix
whose entries are the elementary symmetric polynomials.  This is the classical
**Girard–Waring determinant** (Wikipedia, *Newton's identities*, “Expressing power
sums in terms of elementary symmetric polynomials”):

* `p₁ = det [e₁]`                                              (`psum_one_det`)
* `p₂ = det [[e₁, 1], [2e₂, e₁]]`                              (`psum_two_det`)
* `p₃ = det [[e₁, 1, 0], [2e₂, e₁, 1], [3e₃, e₂, e₁]]`         (`psum_three_det`)

The matrix `Mₖ` has the scaled elementary symmetric polynomials `1·e₁, 2·e₂, …,
k·eₖ` down its first column, the `eⱼ` filling the diagonals below the super-diagonal,
and constant `1`'s on the super-diagonal.  (Contrast the reverse form of
`oq-01-oq-02`, where the super-diagonal instead carries the increasing integers
`1, 2, …`; the asymmetry reflects the different coefficients on the two sides of
the Newton recurrence.)

Unlike a numeric statement these are identities in `MvPolynomial σ R` for **any**
finite index type `σ` and **any** commutative ring `R`; when `card σ < k` the higher
`eⱼ` vanish and the determinant degenerates correctly.  Mathlib records neither the
explicit low-degree forward closed forms nor this determinant shape.

We prove each determinant identity by expanding the small determinant with
`Matrix.det_fin_one_of` / `Matrix.det_fin_two_of` / `Matrix.det_fin_three` and
matching against the forward scalar identities, which we first reproduce by
unrolling Mathlib's recurrence `MvPolynomial.psum_eq_mul_esymm_sub_sum`.

## Axioms: 0 | Sorries: 0
-/

open Finset Matrix

namespace NewtonForwardOQ0103

open MvPolynomial

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-! ## Forward scalar identities (stepping stones)

These reproduce the parent's low-degree forward Newton identities, obtained by
unrolling Mathlib's recurrence `psum_eq_mul_esymm_sub_sum`.  They are the scalar
values that the determinants below must reproduce. -/

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

/-! ## Girard–Waring forward determinant closed form

`pₖ = det Mₖ`, where `Mₖ` is the lower-Hessenberg matrix with the scaled
elementary symmetric polynomials `1·e₁, 2·e₂, …, k·eₖ` down the first column, the
`eⱼ` along the diagonals, and constant `1`'s on the super-diagonal. -/

/-- **Determinant form, degree 1:** `p₁ = det [e₁]`. -/
theorem psum_one_det :
    psum σ R 1 = (!![esymm σ R 1] : Matrix (Fin 1) (Fin 1) (MvPolynomial σ R)).det := by
  rw [Matrix.det_fin_one_of, psum_one_eq]

/-- **Determinant form, degree 2:** `p₂ = det [[e₁, 1], [2e₂, e₁]]`. -/
theorem psum_two_det :
    psum σ R 2 =
      (!![esymm σ R 1, 1; 2 * esymm σ R 2, esymm σ R 1] :
        Matrix (Fin 2) (Fin 2) (MvPolynomial σ R)).det := by
  rw [Matrix.det_fin_two_of]
  linear_combination psum_two_eq σ R

/-- **Determinant form, degree 3:**
`p₃ = det [[e₁, 1, 0], [2e₂, e₁, 1], [3e₃, e₂, e₁]]`. -/
theorem psum_three_det :
    psum σ R 3 =
      (!![esymm σ R 1, 1, 0; 2 * esymm σ R 2, esymm σ R 1, 1;
            3 * esymm σ R 3, esymm σ R 2, esymm σ R 1] :
        Matrix (Fin 3) (Fin 3) (MvPolynomial σ R)).det := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const, Matrix.cons_val',
    Matrix.cons_val_fin_one, Matrix.empty_val']
  linear_combination psum_three_eq σ R

/-! ## Worked example

Over `R = ℤ` with two variables `σ = Fin 2`, the determinant identities specialise
to the familiar symmetric-function formulas.  For instance with variables `X₀, X₁`
we have `p₂ = X₀² + X₁² = (X₀+X₁)² − 2 X₀X₁ = e₁² − 2e₂`, which is exactly the
`2 × 2` determinant below. -/

/-- Sanity check of the degree-2 determinant identity specialised to `Fin 2` over `ℤ`. -/
example :
    psum (Fin 2) ℤ 2 =
      (!![esymm (Fin 2) ℤ 1, 1; 2 * esymm (Fin 2) ℤ 2, esymm (Fin 2) ℤ 1] :
        Matrix (Fin 2) (Fin 2) (MvPolynomial (Fin 2) ℤ)).det :=
  psum_two_det (Fin 2) ℤ

end NewtonForwardOQ0103

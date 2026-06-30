import Mathlib

/-
# Newton's identities in low degree: power sums from elementary symmetric polynomials

For the elementary symmetric polynomials `eₖ = esymm σ R k` and the power sums
`pₖ = psum σ R k = ∑ᵢ Xᵢᵏ` in finitely many variables over a commutative ring,
*Newton's identities* express each power sum as a polynomial in the elementary
symmetric polynomials.  Mathlib proves the general recurrence

  `pₖ = (-1)^{k+1}·k·eₖ - ∑_{0 < i < k} (-1)^i·eᵢ·p_{k-i}`

(`MvPolynomial.psum_eq_mul_esymm_sub_sum`), but does **not** record the explicit
closed forms in low degree.  This entry unrolls the recurrence for `k = 1, 2, 3`
to obtain the three classical identities

* `p₁ = e₁`
* `p₂ = e₁² - 2 e₂`
* `p₃ = e₁³ - 3 e₁ e₂ + 3 e₃`

These hold as identities in `MvPolynomial σ R` for *any* finite index type `σ`
and any commutative ring `R`; when `card σ < k` the higher `eₖ` simply vanish,
so the formulas remain valid (e.g. with a single variable `e₂ = e₃ = 0`, giving
`p₂ = e₁²` and `p₃ = e₁³`).

The proof of `p₁` is immediate from `psum_one`/`esymm_one`.  For `p₂` and `p₃`
we feed the Newton recurrence the explicit (finite) index sets of its inner sum,
each computed once and for all by `omega`, and then close with `ring` after
substituting the previously established lower identities.
-/

open Finset

namespace NewtonPowerSum

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-- **Newton's identity, degree 1:** `p₁ = e₁`.
Both sides equal `∑ᵢ Xᵢ`. -/
theorem psum_one_eq : MvPolynomial.psum σ R 1 = MvPolynomial.esymm σ R 1 := by
  rw [MvPolynomial.psum_one, MvPolynomial.esymm_one]

/-- **Newton's identity, degree 2:** `p₂ = e₁² - 2 e₂`. -/
theorem psum_two_eq :
    MvPolynomial.psum σ R 2 = MvPolynomial.esymm σ R 1 ^ 2 - 2 * MvPolynomial.esymm σ R 2 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 2 (by norm_num)]
  -- The inner sum ranges over `{a ∈ antidiagonal 2 | 0 < a.1 < 2}`, i.e. just `(1, 1)`.
  have hset : {a ∈ Finset.antidiagonal 2 | a.1 ∈ Set.Ioo 0 2} = {(1, 1)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_singleton,
      Prod.mk.injEq]
    omega
  rw [hset, Finset.sum_singleton, psum_one_eq]
  push_cast
  ring

/-- **Newton's identity, degree 3:** `p₃ = e₁³ - 3 e₁ e₂ + 3 e₃`. -/
theorem psum_three_eq :
    MvPolynomial.psum σ R 3 =
      MvPolynomial.esymm σ R 1 ^ 3 - 3 * MvPolynomial.esymm σ R 1 * MvPolynomial.esymm σ R 2
        + 3 * MvPolynomial.esymm σ R 3 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 3 (by norm_num)]
  -- The inner sum ranges over `{a ∈ antidiagonal 3 | 0 < a.1 < 3}`, i.e. `{(1, 2), (2, 1)}`.
  have hset : {a ∈ Finset.antidiagonal 3 | a.1 ∈ Set.Ioo 0 3} = {(1, 2), (2, 1)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [hset, Finset.sum_pair (by decide), psum_two_eq, psum_one_eq]
  push_cast
  ring

end NewtonPowerSum

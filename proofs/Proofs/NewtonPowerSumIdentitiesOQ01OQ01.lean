import Mathlib

/-
# Newton's identities in degrees 4 and 5: explicit power-sum closed forms

For the elementary symmetric polynomials `eₖ = esymm σ R k` and the power sums
`pₖ = psum σ R k = ∑ᵢ Xᵢᵏ` in finitely many variables over a commutative ring,
*Newton's identities* express each power sum as a polynomial in the elementary
symmetric polynomials.  Mathlib proves the general recurrence

  `pₖ = (-1)^{k+1}·k·eₖ - ∑_{0 < i < k} (-1)^i·eᵢ·p_{k-i}`

(`MvPolynomial.psum_eq_mul_esymm_sub_sum`), but does **not** record the explicit
closed forms in low degree.  The parent entry unrolled the recurrence for
`k = 1, 2, 3`:

* `p₁ = e₁`
* `p₂ = e₁² - 2 e₂`
* `p₃ = e₁³ - 3 e₁ e₂ + 3 e₃`

This child continues the *identical* documented method two more rungs, recording
the two next classical identities

* `p₄ = e₁⁴ - 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ - 4 e₄`
* `p₅ = e₁⁵ - 5 e₁³ e₂ + 5 e₁ e₂² + 5 e₁² e₃ - 5 e₂ e₃ - 5 e₁ e₄ + 5 e₅`

These hold as identities in `MvPolynomial σ R` for *any* finite index type `σ`
and any commutative ring `R`; when `card σ < k` the higher `eₖ` simply vanish,
so the formulas remain valid (e.g. with a single variable all of `e₂,…,e₅ = 0`,
giving `p₄ = e₁⁴` and `p₅ = e₁⁵`).

For each degree we feed the Newton recurrence the explicit (finite) index set of
its inner sum — computed once and for all by `omega` — expand the sum over that
literal `Finset`, substitute the previously established lower identities, and
close with `push_cast; ring`.  The entry is self-contained: the degree-1,2,3
identities are restated and reproved here so the file stands alone.
-/

open Finset

namespace NewtonPowerSumOQ01

variable (σ : Type*) (R : Type*) [CommRing R] [Fintype σ]

/-- **Newton's identity, degree 1:** `p₁ = e₁`. -/
theorem psum_one_eq : MvPolynomial.psum σ R 1 = MvPolynomial.esymm σ R 1 := by
  rw [MvPolynomial.psum_one, MvPolynomial.esymm_one]

/-- **Newton's identity, degree 2:** `p₂ = e₁² - 2 e₂`. -/
theorem psum_two_eq :
    MvPolynomial.psum σ R 2 = MvPolynomial.esymm σ R 1 ^ 2 - 2 * MvPolynomial.esymm σ R 2 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 2 (by norm_num)]
  -- inner sum ranges over `{a ∈ antidiagonal 2 | 0 < a.1 < 2}`, i.e. just `(1, 1)`.
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
  -- inner sum ranges over `{(1, 2), (2, 1)}`.
  have hset : {a ∈ Finset.antidiagonal 3 | a.1 ∈ Set.Ioo 0 3} = {(1, 2), (2, 1)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [hset, Finset.sum_pair (by decide), psum_two_eq, psum_one_eq]
  push_cast
  ring

/-- **Newton's identity, degree 4:** `p₄ = e₁⁴ - 4 e₁² e₂ + 2 e₂² + 4 e₁ e₃ - 4 e₄`. -/
theorem psum_four_eq :
    MvPolynomial.psum σ R 4 =
      MvPolynomial.esymm σ R 1 ^ 4
        - 4 * MvPolynomial.esymm σ R 1 ^ 2 * MvPolynomial.esymm σ R 2
        + 2 * MvPolynomial.esymm σ R 2 ^ 2
        + 4 * MvPolynomial.esymm σ R 1 * MvPolynomial.esymm σ R 3
        - 4 * MvPolynomial.esymm σ R 4 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 4 (by norm_num)]
  -- inner sum ranges over `{(1, 3), (2, 2), (3, 1)}`.
  have hset : {a ∈ Finset.antidiagonal 4 | a.1 ∈ Set.Ioo 0 4} = {(1, 3), (2, 2), (3, 1)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    psum_three_eq, psum_two_eq, psum_one_eq]
  push_cast
  ring

/-- **Newton's identity, degree 5:**
`p₅ = e₁⁵ - 5 e₁³ e₂ + 5 e₁ e₂² + 5 e₁² e₃ - 5 e₂ e₃ - 5 e₁ e₄ + 5 e₅`. -/
theorem psum_five_eq :
    MvPolynomial.psum σ R 5 =
      MvPolynomial.esymm σ R 1 ^ 5
        - 5 * MvPolynomial.esymm σ R 1 ^ 3 * MvPolynomial.esymm σ R 2
        + 5 * MvPolynomial.esymm σ R 1 * MvPolynomial.esymm σ R 2 ^ 2
        + 5 * MvPolynomial.esymm σ R 1 ^ 2 * MvPolynomial.esymm σ R 3
        - 5 * MvPolynomial.esymm σ R 2 * MvPolynomial.esymm σ R 3
        - 5 * MvPolynomial.esymm σ R 1 * MvPolynomial.esymm σ R 4
        + 5 * MvPolynomial.esymm σ R 5 := by
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 5 (by norm_num)]
  -- inner sum ranges over `{(1, 4), (2, 3), (3, 2), (4, 1)}`.
  have hset :
      {a ∈ Finset.antidiagonal 5 | a.1 ∈ Set.Ioo 0 5} = {(1, 4), (2, 3), (3, 2), (4, 1)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_antidiagonal, Set.mem_Ioo, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    psum_four_eq, psum_three_eq, psum_two_eq, psum_one_eq]
  push_cast
  ring

end NewtonPowerSumOQ01

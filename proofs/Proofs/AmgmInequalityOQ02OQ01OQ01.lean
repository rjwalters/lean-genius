import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Tactic

/-!
# AM-GM OQ-02 → OQ-01 → OQ-01: the full Newton–Girard recurrence over any number of variables

The parent chain (`amgm-inequality-oq-02`) studies elementary symmetric polynomials and power
sums (e.g. for the AM-GM inequality). Its OQ-02-OQ-01-OQ-01 asks to

> *prove the full Newton–Girard recurrence* `pₖ = Σᵢ (−1)ⁱ⁻¹ eᵢ pₖ₋ᵢ` *for power sums in
> terms of elementary symmetric polynomials* (for any number of variables).

A gallery sibling (`solution-of-cubic-oq-03-oq-04`) proved this for three quantities by hand.
Mathlib in fact proves the identities in full generality over `MvPolynomial σ R` for any
`Fintype σ` and commutative ring `R` (`MvPolynomial.mul_esymm_eq_sum`,
`MvPolynomial.psum_eq_mul_esymm_sub_sum`). This file packages those as the general Newton–
Girard recurrence and records its low-degree consequences, with `0` axioms.

## Main results

* `newton_esymm_recurrence` : `k·eₖ = (−1)^{k+1} Σ_{i+j=k, i<k} (−1)ⁱ eᵢ pⱼ`.
* `newton_psum_recurrence` : `pₖ = (−1)^{k+1} k eₖ − Σ_{i+j=k, 0<i<k} (−1)ⁱ eᵢ pⱼ` — the
  power-sum recurrence (the OQ's target).
* `newton_sum_zero` : at `k = |σ|`, `Σ_{i+j=k} (−1)ⁱ eᵢ pⱼ = 0` (the recurrence closes).
* `psum_one_eq_esymm_one` : `p₁ = e₁`, the base case.
-/

namespace AmgmInequalityOQ02OQ01OQ01

open MvPolynomial Finset

variable (σ : Type*) [Fintype σ] (R : Type*) [CommRing R]

/-- **Newton's identity for elementary symmetric polynomials.** For every `k`,
    `k·eₖ = (−1)^{k+1} Σ_{i+j=k, i<k} (−1)ⁱ eᵢ pⱼ`, expressing `k·eₖ` through lower-degree
    elementary symmetric polynomials and power sums. (Mathlib: `mul_esymm_eq_sum`.) -/
theorem newton_esymm_recurrence (k : ℕ) :
    (k : MvPolynomial σ R) * esymm σ R k
      = (-1) ^ (k + 1) *
        ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2 :=
  mul_esymm_eq_sum σ R k

/-- **The Newton–Girard power-sum recurrence.** For `k > 0`,
    `pₖ = (−1)^{k+1} k eₖ − Σ_{i+j=k, 0<i<k} (−1)ⁱ eᵢ pⱼ`, the recurrence computing the `k`-th
    power sum from the elementary symmetric polynomials and lower power sums — the general
    form of `pₖ = Σᵢ (−1)ⁱ⁻¹ eᵢ pₖ₋ᵢ`. (Mathlib: `psum_eq_mul_esymm_sub_sum`.) -/
theorem newton_psum_recurrence (k : ℕ) (hk : 0 < k) :
    psum σ R k
      = (-1) ^ (k + 1) * k * esymm σ R k
        - ∑ a ∈ antidiagonal k with a.1 ∈ Set.Ioo 0 k,
            (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2 :=
  psum_eq_mul_esymm_sub_sum σ R k hk

/-- **Closure at `k = |σ|`.** When `k` equals the number of variables, the full alternating
    sum of `eᵢ pⱼ` over `i + j = k` vanishes: `Σ_{i+j=k} (−1)ⁱ eᵢ pⱼ = 0`. Beyond this degree
    the elementary symmetric polynomials are zero, so the recurrence terminates. -/
theorem newton_sum_zero :
    ∑ a ∈ antidiagonal (Fintype.card σ),
      (-1) ^ a.1 * esymm σ R a.1 * psum σ R a.2 = 0 :=
  sum_antidiagonal_card_esymm_psum_eq_zero σ R

/-- **Base case `p₁ = e₁`.** The first power sum equals the first elementary symmetric
    polynomial (both are `Σᵢ Xᵢ`). -/
theorem psum_one_eq_esymm_one : psum σ R 1 = esymm σ R 1 := by
  rw [psum_one, esymm_one]

end AmgmInequalityOQ02OQ01OQ01

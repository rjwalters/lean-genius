/-
# The General n-Variable Young Product Inequality and its Equality Case

The two-term Young inequality (parent file `JensenInequalityOQ01OQ01`) reads, for Hölder-conjugate
exponents `p, q` (so `1/p + 1/q = 1`) and nonnegative reals `a, b`,

    a * b ≤ aᵖ/p + bᵍ/q,   with equality iff aᵖ = bᵍ.

This file proves the **`n`-variable generalization**: given a finite family of exponents
`p i > 0` whose reciprocals sum to `1` (i.e. `∑ 1/pᵢ = 1`) and nonnegative data `a i`,

    ∏ᵢ aᵢ ≤ ∑ᵢ aᵢ^{pᵢ}/pᵢ,   with equality iff all the `aᵢ^{pᵢ}` are equal.

This is to the two-variable Young inequality exactly what the parent's general weighted AM–GM
(`weighted_amgm_eq_iff`) is to its two-variable instance: take weights `wᵢ = 1/pᵢ` (strictly
positive, summing to `1`) and data `zᵢ = aᵢ^{pᵢ}`. Then the weighted geometric mean
`∏ᵢ zᵢ^{wᵢ} = ∏ᵢ (aᵢ^{pᵢ})^{1/pᵢ} = ∏ᵢ aᵢ` and the weighted arithmetic mean
`∑ᵢ wᵢ zᵢ = ∑ᵢ aᵢ^{pᵢ}/pᵢ`, so the general AM–GM inequality and *its* equality case are exactly the
general Young product inequality and its equality case.

Mathlib provides the two-variable Young inequality (`Real.young_inequality_of_nonneg`) but not the
`n`-variable product form, nor any of the equality cases; this file supplies all of them.

## Main results

* `young_prod_le` — the `n`-variable Young product inequality `∏ aᵢ ≤ ∑ aᵢ^{pᵢ}/pᵢ`.
* `young_prod_eq_iff` — its **equality case**: equality holds iff all the `aᵢ^{pᵢ}` are equal.
* `young_prod_lt_of_ne` — the strict form when two of the `aᵢ^{pᵢ}` differ.

All results are fully machine-checked: 0 sorries, 0 axioms, no `native_decide`.
-/

import Mathlib
import Proofs.JensenInequalityOQ01
import Proofs.JensenInequalityOQ01OQ01

open Finset Real

variable {ι : Type*} {s : Finset ι} {p a : ι → ℝ}

/-- For nonnegative `a` and nonzero exponent `p`, `(a^p)^{1/p} = a`. This is the pointwise identity
that turns the weighted geometric mean of the `aᵢ^{pᵢ}` (with weights `1/pᵢ`) into the plain product
`∏ aᵢ`. -/
private theorem rpow_pow_inv {a p : ℝ} (ha : 0 ≤ a) (hp : p ≠ 0) : (a ^ p) ^ p⁻¹ = a := by
  rw [← Real.rpow_mul ha, mul_inv_cancel₀ hp, Real.rpow_one]

/-- **The `n`-variable Young product inequality.** For strictly positive exponents `p i` whose
reciprocals sum to `1` and nonnegative data `a i`, the product `∏ aᵢ` is at most the sum
`∑ aᵢ^{pᵢ}/pᵢ`.

The proof specializes the parent's weighted AM–GM inequality `weighted_amgm_le` with weights
`wᵢ = 1/pᵢ` and data `zᵢ = aᵢ^{pᵢ}`: the geometric mean `∏ (aᵢ^{pᵢ})^{1/pᵢ}` collapses to `∏ aᵢ`,
and the arithmetic mean `∑ (1/pᵢ) aᵢ^{pᵢ}` is `∑ aᵢ^{pᵢ}/pᵢ`. -/
theorem young_prod_le (hp : ∀ i ∈ s, 0 < p i) (hp' : ∑ i ∈ s, (p i)⁻¹ = 1)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, a i ≤ ∑ i ∈ s, a i ^ p i / p i := by
  have key := weighted_amgm_le (w := fun i => (p i)⁻¹) (z := fun i => a i ^ p i)
    (fun i hi => le_of_lt (inv_pos.mpr (hp i hi))) hp'
    (fun i hi => Real.rpow_nonneg (ha i hi) (p i))
  -- Geometric mean collapses to the plain product.
  have hgeo : ∏ i ∈ s, (a i ^ p i) ^ (p i)⁻¹ = ∏ i ∈ s, a i :=
    Finset.prod_congr rfl fun i hi => rpow_pow_inv (ha i hi) (hp i hi).ne'
  -- Arithmetic mean is the Young sum.
  have harith : ∑ i ∈ s, (p i)⁻¹ * a i ^ p i = ∑ i ∈ s, a i ^ p i / p i :=
    Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul]
  rw [hgeo, harith] at key
  exact key

/-- **Equality case of the `n`-variable Young product inequality.** Under the same hypotheses,
`∏ aᵢ = ∑ aᵢ^{pᵢ}/pᵢ` holds **iff all the `aᵢ^{pᵢ}` are equal**.

The proof applies the parent's weighted AM–GM equality case `weighted_amgm_eq_iff` with weights
`wᵢ = 1/pᵢ` and data `zᵢ = aᵢ^{pᵢ}`, then rewrites both means as above. For `n = 2` with
`p i ∈ {p, q}` Hölder-conjugate this recovers the two-variable `young_eq_iff` of the parent file. -/
theorem young_prod_eq_iff (hp : ∀ i ∈ s, 0 < p i) (hp' : ∑ i ∈ s, (p i)⁻¹ = 1)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, a i = ∑ i ∈ s, a i ^ p i / p i ↔ ∀ j ∈ s, ∀ k ∈ s, a j ^ p j = a k ^ p k := by
  have key := weighted_amgm_eq_iff (w := fun i => (p i)⁻¹) (z := fun i => a i ^ p i)
    (fun i hi => inv_pos.mpr (hp i hi)) hp'
    (fun i hi => Real.rpow_nonneg (ha i hi) (p i))
  have hgeo : ∏ i ∈ s, (a i ^ p i) ^ (p i)⁻¹ = ∏ i ∈ s, a i :=
    Finset.prod_congr rfl fun i hi => rpow_pow_inv (ha i hi) (hp i hi).ne'
  have harith : ∑ i ∈ s, (p i)⁻¹ * a i ^ p i = ∑ i ∈ s, a i ^ p i / p i :=
    Finset.sum_congr rfl fun i _ => by rw [div_eq_inv_mul]
  rw [hgeo, harith] at key
  exact key

/-- **Strict `n`-variable Young product inequality.** If two of the values `aᵢ^{pᵢ}` differ, the
product is *strictly* less than the Young sum. -/
theorem young_prod_lt_of_ne (hp : ∀ i ∈ s, 0 < p i) (hp' : ∑ i ∈ s, (p i)⁻¹ = 1)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hne : ∃ j ∈ s, ∃ k ∈ s, a j ^ p j ≠ a k ^ p k) :
    ∏ i ∈ s, a i < ∑ i ∈ s, a i ^ p i / p i := by
  refine lt_of_le_of_ne (young_prod_le hp hp' ha) fun h => ?_
  obtain ⟨j, hj, k, hk, hjk⟩ := hne
  exact hjk ((young_prod_eq_iff hp hp' ha).mp h j hj k hk)

/-
# Bienaymé's Identity with the Covariance Correction

For a finite family of square-integrable random variables `{Xᵢ}` over a
probability space, the variance of the sum decomposes as

    Var[∑ᵢ Xᵢ] = ∑ᵢ Var[Xᵢ] + 2 · ∑_{i < j} Cov[Xᵢ, Xⱼ].

Mathlib already provides the **unsymmetrised** double-sum form
`ProbabilityTheory.variance_sum'`:

    Var[∑ᵢ Xᵢ] = ∑ᵢ ∑ⱼ Cov[Xᵢ, Xⱼ],

but it does **not** isolate the diagonal `∑ᵢ Var[Xᵢ]` from the off-diagonal
`2 · ∑_{i < j} Cov[Xᵢ, Xⱼ]`. That off-diagonal *covariance correction* is exactly
what vanishes in the uncorrelated / i.i.d. case (giving `Var[Sₙ] = ∑ᵢ Var[Xᵢ]`,
hence the `√n` scaling behind the classical CLT) and what **persists** for
dependent sequences, where it accumulates into the long-run variance

    σ²∞ = Var[X₁] + 2 · ∑_{k ≥ 1} Cov[X₁, X_{k+1}]

that drives the central limit theorem for dependent random variables
(Ibragimov 1962, McLeish 1974). See `CentralLimitTheoremOQ02.lean` for the
gallery entry on the dependent CLT this supports.

The mathematical content here is the **symmetrisation step**: turning the full
off-diagonal sum into twice the strict upper triangle, using the symmetry of
covariance `cov[Xᵢ, Xⱼ] = cov[Xⱼ, Xᵢ]` and the `swap` involution on the
off-diagonal of a linearly ordered index set.

All results are fully verified from Mathlib: no axioms, no sorries.

Reference: Billingsley, *Probability and Measure*, §29 (Bienaymé's identity);
           Ibragimov & Linnik, *Independent and Stationary Sequences*.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory

namespace CentralLimitTheoremOQ02Incomplete01

variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : ι → Ω → ℝ} {s : Finset ι}

/-- **Off-diagonal symmetrisation.** For a finite index set with a linear order,
summing the symmetric kernel `cov[Xᵢ, Xⱼ]` over the entire off-diagonal equals
twice the sum over the strict upper triangle `{(i, j) : i < j}`.

The proof pairs each lower-triangular term `(j, i)` with its upper-triangular
mirror `(i, j)` via the `Prod.swap` involution, which preserves the off-diagonal
and (by `covariance_comm`) preserves the summand. -/
theorem sum_offDiag_covariance_eq_two_mul [LinearOrder ι] [DecidableEq ι] :
    ∑ p ∈ s.offDiag, cov[X p.1, X p.2; μ]
      = 2 * ∑ p ∈ s.offDiag with p.1 < p.2, cov[X p.1, X p.2; μ] := by
  classical
  rw [two_mul, ← Finset.sum_filter_add_sum_filter_not s.offDiag (fun p => p.1 < p.2)
        (fun p => cov[X p.1, X p.2; μ])]
  congr 1
  refine Finset.sum_nbij' (fun p => Prod.swap p) (fun p => Prod.swap p) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_offDiag, Prod.swap_prod_mk, not_lt] at hp ⊢
    obtain ⟨⟨ha, hb, hab⟩, hba⟩ := hp
    exact ⟨⟨hb, ha, fun h => hab h.symm⟩, lt_of_le_of_ne hba (fun h => hab h.symm)⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_offDiag, Prod.swap_prod_mk, not_lt] at hp ⊢
    obtain ⟨⟨ha, hb, hab⟩, hab'⟩ := hp
    exact ⟨⟨hb, ha, fun h => hab h.symm⟩, le_of_lt hab'⟩
  · rintro ⟨a, b⟩ _; simp
  · rintro ⟨a, b⟩ _; simp
  · rintro ⟨a, b⟩ _
    simp only [Prod.swap_prod_mk]
    exact covariance_comm (X a) (X b)

/-- **Bienaymé's identity with the covariance correction.**

For a finite family of `L²` random variables over a probability space, the
variance of their sum is the sum of the individual variances *plus* twice the
sum of the pairwise covariances over the strict upper triangle:

    Var[∑ᵢ Xᵢ] = ∑ᵢ Var[Xᵢ] + 2 · ∑_{i < j} Cov[Xᵢ, Xⱼ].

This refines Mathlib's `variance_sum'` (which leaves the answer as the full
double sum `∑ᵢ ∑ⱼ Cov`) by extracting the diagonal variance term and folding
the off-diagonal into the explicit dependence correction. -/
theorem variance_sum_eq_diag_add_two_mul_offDiag
    [IsProbabilityMeasure μ] [LinearOrder ι] [DecidableEq ι]
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ) :
    Var[∑ i ∈ s, X i; μ]
      = ∑ i ∈ s, Var[X i; μ]
        + 2 * ∑ p ∈ s.offDiag with p.1 < p.2, cov[X p.1, X p.2; μ] := by
  classical
  rw [variance_sum' hX, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag,
    sum_offDiag_covariance_eq_two_mul]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => covariance_self (hX i hi).aemeasurable)

/-- **Uncorrelated case recovers additivity of variance.**

If the family is pairwise uncorrelated (`Cov[Xᵢ, Xⱼ] = 0` for `i ≠ j`) — in
particular if the `Xᵢ` are pairwise independent — then the covariance correction
vanishes and the variance of the sum is the sum of the variances. This is the
identity underpinning the `√n` normalisation in the classical CLT. -/
theorem variance_sum_of_pairwise_uncorrelated
    [IsProbabilityMeasure μ] [LinearOrder ι] [DecidableEq ι]
    (hX : ∀ i ∈ s, MemLp (X i) 2 μ)
    (hcov : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cov[X i, X j; μ] = 0) :
    Var[∑ i ∈ s, X i; μ] = ∑ i ∈ s, Var[X i; μ] := by
  rw [variance_sum_eq_diag_add_two_mul_offDiag hX]
  have hzero : (∑ p ∈ s.offDiag with p.1 < p.2, cov[X p.1, X p.2; μ]) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_offDiag] at hp
    obtain ⟨⟨ha, hb, hab⟩, _⟩ := hp
    exact hcov a ha b hb hab
  rw [hzero, mul_zero, add_zero]

/-- **Partial-sum specialisation.**

For a sequence `Y : ℕ → Ω → ℝ` of `L²` variables, the variance of the partial
sum `Sₙ = ∑_{k < n} Yₖ` carries the explicit covariance correction

    Var[Sₙ] = ∑_{k < n} Var[Yₖ] + 2 · ∑_{i < j < n} Cov[Yᵢ, Yⱼ].

This is the finite-`n` exact identity whose `n → ∞` limit (after dividing by `n`
for a stationary sequence) produces the long-run variance `σ²∞`. -/
theorem variance_partialSum_eq
    [IsProbabilityMeasure μ] {Y : ℕ → Ω → ℝ} (n : ℕ)
    (hY : ∀ i, i < n → MemLp (Y i) 2 μ) :
    Var[∑ k ∈ Finset.range n, Y k; μ]
      = ∑ k ∈ Finset.range n, Var[Y k; μ]
        + 2 * ∑ p ∈ (Finset.range n).offDiag with p.1 < p.2, cov[Y p.1, Y p.2; μ] :=
  variance_sum_eq_diag_add_two_mul_offDiag (fun i hi => hY i (Finset.mem_range.mp hi))

end CentralLimitTheoremOQ02Incomplete01

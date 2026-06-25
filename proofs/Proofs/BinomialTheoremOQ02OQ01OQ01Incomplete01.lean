import Mathlib

/-
# Singularity of the Multinomial Covariance Matrix

## Question
The multinomial mean (`E[Xᵢ] = n·pᵢ`), variance (`Var Xᵢ = n·pᵢ(1 - pᵢ)`) and
off-diagonal covariance (`Cov(Xᵢ,Xⱼ) = -n·pᵢ·pⱼ` for `i ≠ j`) are already
formalized in the sibling files (`BinomialTheoremOQ02OQ01`,
`BinomialTheoremOQ02OQ01OQ01`, `BinomialTheoremOQ02OQ01OQ04`). Assembled, they
form the `|s| × |s|` covariance matrix `Σ` of the count vector `X = (Xᵢ)`.
Is this matrix *singular*, and if so, what is its kernel?

## Answer
**Yes — `Σ` is singular, with the all-ones vector `𝟙` in its kernel.**

The multinomial counts obey the hard linear constraint `∑ᵢ Xᵢ = n`: every one of
the `n` draws is classified into exactly one category. The random vector `X`
therefore lives on the hyperplane `{x : ∑ xᵢ = n}`, so its covariance matrix is
degenerate. Concretely, the rows of `Σ` sum to zero:

    ∀ i,  ∑ⱼ Cov(Xᵢ, Xⱼ) = Cov(Xᵢ, ∑ⱼ Xⱼ) = Cov(Xᵢ, n) = 0.

We prove this directly at the level of the defining `piAntidiag` sums, where the
mechanism is transparent: on the support, every composition `k` satisfies
`∑ⱼ kⱼ = n`, so the *centered partner sum* collapses,

    ∑ⱼ (kⱼ - n·pⱼ) = (∑ⱼ kⱼ) - n·(∑ⱼ pⱼ) = n - n·1 = 0,

and the entire row sum vanishes term by term — no cancellation between distinct
covariance entries is needed.

## Results
* `centered_partner_sum_zero` — the engine: `∑ⱼ (kⱼ - n·pⱼ) = 0` on the support.
* `multinomial_cov_row_sum_zero` — each row of `Σ` sums to `0` (the kernel
  statement: `𝟙 ∈ ker Σ`).
* `multinomial_cov_total_sum_zero` — every entry of `Σ` sums to `0`, i.e.
  `Var(∑ᵢ Xᵢ) = 0`, the variance of the (constant) total count.
* `multinomial_var_eq_neg_offdiag` — the diagonal is *forced* by the
  off-diagonals: `Var(Xᵢ) = -∑_{j ≠ i} Cov(Xᵢ, Xⱼ)`. The covariance matrix has
  no independent diagonal; given its off-diagonal entries, the variances are
  determined.

These facts are the geometry behind the standard practice of dropping one
category in multinomial logistic regression: `Σ` has rank at most `|s| - 1`.

Axiom-free: only `propext` / `Classical.choice` / `Quot.sound`.
-/

namespace BinomialTheoremOQ02OQ01OQ01Incomplete01

open Finset BigOperators
open scoped Nat

variable {α : Type*} [DecidableEq α]

/-- The multinomial mass weight at a composition `k`:
    `multinomial(s, k) · ∏ₗ pₗ ^ kₗ`. Summed against a function of `k` over
    `s.piAntidiag n` this computes expectations under the multinomial law. -/
noncomputable def w (s : Finset α) (p : α → ℝ) (k : α → ℕ) : ℝ :=
  (Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l

/-- The `(i, j)` entry of the multinomial covariance matrix, written directly as
    a sum over compositions: `Cov(Xᵢ, Xⱼ) = ∑ₖ (kᵢ - n·pᵢ)(kⱼ - n·pⱼ) · w(k)`.
    For `i = j` this is the variance `Var(Xᵢ)`. -/
noncomputable def covEntry (s : Finset α) (p : α → ℝ) (n : ℕ) (i j : α) : ℝ :=
  ∑ k ∈ s.piAntidiag n,
    ((k i : ℝ) - n * p i) * ((k j : ℝ) - n * p j) * w s p k

/-- **The vanishing engine.** On the support of the multinomial, every
    composition `k` has total count `n`, so the centered counts sum to zero:
    `∑ⱼ (kⱼ - n·pⱼ) = (∑ⱼ kⱼ) - n·(∑ⱼ pⱼ) = n - n = 0`. This single identity is
    the reason the covariance matrix is singular. -/
theorem centered_partner_sum_zero (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) {k : α → ℕ} (hk : k ∈ s.piAntidiag n) :
    ∑ j ∈ s, ((k j : ℝ) - n * p j) = 0 := by
  have hk1 : ∑ j ∈ s, k j = n := (Finset.mem_piAntidiag.mp hk).1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp, mul_one,
      show (∑ j ∈ s, (k j : ℝ)) = (n : ℝ) from by rw [← Nat.cast_sum, hk1],
      sub_self]

/-- **Rows of the multinomial covariance matrix sum to zero.**
    For each category `i`, `∑ⱼ Cov(Xᵢ, Xⱼ) = 0`; equivalently the all-ones vector
    lies in the kernel of `Σ`, so `Σ` is singular. The proof swaps the order of
    summation and factors out the `j`-independent part `(kᵢ - n·pᵢ)·w(k)`, leaving
    the centered partner sum, which vanishes by `centered_partner_sum_zero`. -/
theorem multinomial_cov_row_sum_zero (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) (i : α) :
    ∑ j ∈ s, covEntry s p n i j = 0 := by
  unfold covEntry
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun k hk => ?_)
  have hfactor : ∑ j ∈ s, ((k i : ℝ) - n * p i) * ((k j : ℝ) - n * p j) * w s p k
      = (((k i : ℝ) - n * p i) * w s p k) * ∑ j ∈ s, ((k j : ℝ) - n * p j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hfactor, centered_partner_sum_zero s p n hp hk, mul_zero]

/-- **Every entry of `Σ` sums to zero.** Summing the (already zero) row sums,
    `∑ᵢ ∑ⱼ Cov(Xᵢ, Xⱼ) = 0`. Probabilistically this is `Var(∑ᵢ Xᵢ) = 0`: the total
    count `∑ᵢ Xᵢ ≡ n` is constant, hence has zero variance. -/
theorem multinomial_cov_total_sum_zero (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, ∑ j ∈ s, covEntry s p n i j = 0 :=
  Finset.sum_eq_zero (fun i _ => multinomial_cov_row_sum_zero s p n hp i)

/-- **The diagonal is forced by the off-diagonals.** Splitting the zero row sum at
    `j = i`, the variance equals minus the sum of the off-diagonal covariances:
    `Var(Xᵢ) = -∑_{j ≠ i} Cov(Xᵢ, Xⱼ)`. The covariance matrix carries no independent
    diagonal information — once the off-diagonal entries are fixed, the variances
    are determined by the constraint `∑ᵢ Xᵢ = n`. -/
theorem multinomial_var_eq_neg_offdiag (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp : ∑ i ∈ s, p i = 1) (i : α) (hi : i ∈ s) :
    covEntry s p n i i = - ∑ j ∈ s.erase i, covEntry s p n i j := by
  have hrow := multinomial_cov_row_sum_zero s p n hp i
  rw [← Finset.add_sum_erase s (fun j => covEntry s p n i j) hi] at hrow
  linarith [hrow]

-- ============================================================
-- Sanity checks and axiom audit
-- ============================================================

#check @multinomial_cov_row_sum_zero
#check @multinomial_cov_total_sum_zero
#check @multinomial_var_eq_neg_offdiag

-- Should list only propext / Classical.choice / Quot.sound
#print axioms multinomial_cov_row_sum_zero
#print axioms multinomial_cov_total_sum_zero
#print axioms multinomial_var_eq_neg_offdiag

end BinomialTheoremOQ02OQ01OQ01Incomplete01

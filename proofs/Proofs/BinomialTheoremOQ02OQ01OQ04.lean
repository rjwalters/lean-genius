import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ02
import Proofs.BinomialTheoremOQ02OQ01OQ03
import Proofs.BinomialTheoremOQ03

/-
# Multinomial Variance: Var(Xᵢ) = n·pᵢ·(1 − pᵢ)

*Open Question from BinomialTheoremOQ02OQ01*: the cross-moment lemma in the
`OQ03` sibling carries the hypothesis `i ≠ j`, so it delivers
`E[XᵢXⱼ] = n(n−1)pᵢpⱼ` and `Cov(Xᵢ,Xⱼ) = −n·pᵢ·pⱼ` only off the diagonal. The
**diagonal** second moment `E[Xᵢ²]` — and hence the variance `Var(Xᵢ)` — is the
one standard second moment that the bivariate cross-moment machinery does not
reach. This file fills that gap.

## Answer

YES. For `(X₁,…,Xₖ) ~ Multinomial(n, p₁,…,pₖ)` with `∑pᵢ = 1`,

  Var(Xᵢ) = E[Xᵢ²] − (E[Xᵢ])² = n·pᵢ·(1 − pᵢ).

## Proof Strategy

The component `Xᵢ` is *marginally* `Binomial(n, pᵢ)` — proved in
`BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`. So both the mean and the
second moment of `Xᵢ` reduce, by **fiber grouping** over the value `j = k(i₀)`,
to the corresponding binomial quantities already proved in `BinomialTheoremOQ03`:

1. `multinomial_second_moment`:  `E[Xᵢ²] = ∑ⱼ j²·binomPMF n pᵢ j`
   (same fiber-grouping argument as `OQ03.multinomial_mean`, with the statistic
   `k(i₀)` replaced by `k(i₀)²`).
2. `multinomial_mean` (from `OQ03`):  `E[Xᵢ] = n·pᵢ`.
3. Combine with the binomial variance `E[X²] − (E[X])² = n·p·(1−p)`
   (`BinomialTheoremOQ03.binomial_variance`, extended here to all `n`).

This is a routine diagonal of already-verified machinery, not new mathematics:
the value is closing the last second-moment gap of the multinomial family with
no new axioms or sorries.
-/

namespace BinomialTheoremOQ02OQ01OQ04

open Finset BigOperators
open BinomialTheoremOQ02OQ01OQ03

/-! ## Binomial variance for all `n`

`BinomialTheoremOQ03.binomial_variance` requires `2 ≤ n`. The cases `n = 0`
(degenerate, variance `0`) and `n = 1` (a single Bernoulli trial, variance
`p(1−p)`) are handled directly so the multinomial result holds for every `n`. -/
private lemma binomial_variance_all (n : ℕ) (p : ℝ) :
    (∑ k ∈ range (n + 1), ((k : ℝ) ^ 2 * BinomialTheoremOQ03.binomPMF n p k)) -
    (∑ k ∈ range (n + 1), ((k : ℝ) * BinomialTheoremOQ03.binomPMF n p k)) ^ 2 =
    (n : ℝ) * p * (1 - p) := by
  rcases n with _ | _ | m
  · simp [BinomialTheoremOQ03.binomPMF]
  · simp [BinomialTheoremOQ03.binomPMF, Finset.sum_range_succ]; ring
  · exact BinomialTheoremOQ03.binomial_variance (m + 2) (by omega) p

/-! ## Mean of the marginal, for all `n` -/

private lemma binomial_mean_all_n (n : ℕ) (q : ℝ) :
    ∑ j ∈ range (n + 1), (j : ℝ) * BinomialTheoremOQ03.binomPMF n q j = n * q := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [BinomialTheoremOQ03.binomPMF]
  · exact BinomialTheoremOQ03.binomial_mean n hn q

/-! ## Second moment `E[Xᵢ²] = ∑ⱼ j²·binomPMF n pᵢ j` -/

/-- **Second moment of a multinomial component**: `E[Xᵢ²] = ∑ⱼ j²·binomPMF n pᵢ j`.

    Fiber grouping over the value `j = k(i₀)`: on the fiber `{k | k(i₀) = j}` the
    statistic `k(i₀)²` is the constant `j²`, which factors out, and the remaining
    fiber sum is the marginal PMF `P(Xᵢ = j) = binomPMF n pᵢ j`
    (`multinomial_marginal_pmf`). This is the squared-statistic analogue of
    `OQ03.multinomial_mean`. -/
theorem multinomial_second_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (i₀ : α) (hi₀ : i₀ ∈ s) :
    ∑ k ∈ s.piAntidiag n, (k i₀ : ℝ) ^ 2 * multinomialProb s p n k =
    ∑ j ∈ range (n + 1), (j : ℝ) ^ 2 * BinomialTheoremOQ03.binomPMF n (p i₀) j := by
  -- k(i₀) ≤ n for k ∈ piAntidiag n
  have hmaps_to : ∀ k ∈ s.piAntidiag n, k i₀ ∈ range (n + 1) := fun k hk => by
    rw [mem_range]
    have hle : k i₀ ≤ ∑ l ∈ s, k l :=
      Finset.single_le_sum (fun l _ => Nat.zero_le _) hi₀
    have hsum : ∑ l ∈ s, k l = n := (Finset.mem_piAntidiag.mp hk).1
    omega
  rw [← sum_fiberwise_of_maps_to hmaps_to]
  apply sum_congr rfl
  intro j hj
  rw [mem_range] at hj
  -- On the fiber, replace k(i₀)² by j²
  have step1 :
      ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
        (k i₀ : ℝ) ^ 2 * multinomialProb s p n k =
      ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
        (j : ℝ) ^ 2 * multinomialProb s p n k :=
    sum_congr rfl fun k hk => by
      have heq : k i₀ = j := (mem_filter.mp hk).2
      rw [heq]
  rw [step1, ← mul_sum]
  -- The fiber sum of probabilities is the marginal PMF = binomPMF
  simp_rw [multinomialProb_eq]
  rw [BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf s p n hp_sum i₀ hi₀ j (by omega)]
  unfold BinomialTheoremOQ03.binomPMF
  ring

/-! ## Main Theorem: Var(Xᵢ) = n·pᵢ·(1 − pᵢ) -/

/-- **Multinomial variance**: `Var(Xᵢ) = n·pᵢ·(1 − pᵢ)`.

    The diagonal companion to `OQ03.multinomial_covariance` (`Cov(Xᵢ,Xⱼ) =
    −n·pᵢ·pⱼ` for `i ≠ j`). Combining the second moment `E[Xᵢ²]` with the mean
    `E[Xᵢ] = n·pᵢ` reduces, via the binomial marginal, to the binomial variance
    `n·p·(1 − p)`. -/
theorem multinomial_variance {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (i₀ : α) (hi₀ : i₀ ∈ s) :
    (∑ k ∈ s.piAntidiag n, (k i₀ : ℝ) ^ 2 * multinomialProb s p n k) -
    (∑ k ∈ s.piAntidiag n, (k i₀ : ℝ) * multinomialProb s p n k) ^ 2 =
    (n : ℝ) * p i₀ * (1 - p i₀) := by
  rw [multinomial_second_moment s p n hp_sum i₀ hi₀,
      multinomial_mean s p n hp_sum i₀ hi₀]
  have hmean := binomial_mean_all_n n (p i₀)
  rw [show ((n : ℝ) * p i₀) ^ 2 =
      (∑ j ∈ range (n + 1), (j : ℝ) * BinomialTheoremOQ03.binomPMF n (p i₀) j) ^ 2 from by
    rw [hmean]]
  exact binomial_variance_all n (p i₀)

/-! ## Summary

### Proved (0 axioms, 0 sorries):
1. `multinomial_second_moment` — `E[Xᵢ²] = ∑ⱼ j²·binomPMF n pᵢ j`
   (fiber grouping; squared-statistic analogue of `OQ03.multinomial_mean`).
2. `multinomial_variance`      — `Var(Xᵢ) = n·pᵢ·(1 − pᵢ)`
   (closes the diagonal second-moment gap left by the `i ≠ j` cross-moment).

### Relation to existing gallery results
- `OQ03.multinomial_covariance` gives `Cov(Xᵢ,Xⱼ) = −n·pᵢ·pⱼ` for `i ≠ j`.
- This file supplies the diagonal `i = j` entry of the covariance matrix:
  `Var(Xᵢ) = Cov(Xᵢ,Xᵢ) = n·pᵢ·(1 − pᵢ)`.

Together they determine the full multinomial covariance matrix
`Σᵢⱼ = n·pᵢ·(δᵢⱼ − pⱼ)`.
-/

end BinomialTheoremOQ02OQ01OQ04

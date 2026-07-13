# binomial-theorem-oq-02-oq-01-oq-04 — Multinomial Variance

## Status: COMPLETE (Lean-verified)

`Var(Xᵢ) = n·pᵢ·(1 − pᵢ)` for a component of `Multinomial(n, p)` is fully
machine-verified in `proofs/Proofs/BinomialTheoremOQ02OQ01OQ04.lean`
(0 sorries, 0 axioms).

## What was delivered

- `multinomial_second_moment`: `E[Xᵢ²] = ∑ⱼ j²·binomPMF n pᵢ j`.
- `multinomial_variance`: `E[Xᵢ²] − (E[Xᵢ])² = n·pᵢ·(1 − pᵢ)`.

## History

- The slug was originally "replace the vacuous `multinomial_expectation` rfl
  with a substantive mean E[Xᵢ]=n·pᵢ". The mean was delivered separately
  (`multinomial_mean`, merged in #24983 in the parent file, and independently
  proved by fiber grouping in the OQ03 covariance sibling).
- PR #25019 (build-free) pinned the remaining gap: the cross-moment lemma in
  OQ03 carries `hij : i ≠ j`, so it gives `Cov(Xᵢ,Xⱼ) = −n·pᵢpⱼ` only off the
  diagonal. The **diagonal** `E[Xᵢ²]` / `Var(Xᵢ)` was the one standard second
  moment not yet in Lean. That PR proposed an MGF double-differentiation route
  (single-variable copy of the cross-moment proof).

## Route actually taken (simpler than the MGF route in #25019)

Instead of double-differentiating a single-variable MGF (finicky `HasDerivAt`
bookkeeping with nat-subtraction in the exponent), the marginal of `Xᵢ` is
itself `Binomial(n, pᵢ)`. So the variance is just the binomial variance,
reached by **fiber grouping** — the exact technique already used for the mean:

1. `multinomial_second_moment`: group `∑ₖ k(i₀)²·P(k)` by `j = k(i₀)` with
   `sum_fiberwise_of_maps_to`. On each fiber `k(i₀)²` is the constant `j²`,
   factored out by `mul_sum`; the remaining fiber sum is
   `multinomial_marginal_pmf` = `binomPMF n pᵢ j`. Result:
   `E[Xᵢ²] = ∑ⱼ j²·binomPMF n pᵢ j`.
2. `multinomial_variance`: rewrite `E[Xᵢ²]` and `E[Xᵢ] = n·pᵢ`
   (`OQ03.multinomial_mean`), re-express `(n·pᵢ)²` as `(∑ⱼ j·binomPMF)²` via the
   binomial mean, and close with the binomial variance.

Reused, verified machinery (no new mathematics):
- `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`
- `BinomialTheoremOQ02OQ01OQ03.multinomial_mean`
- `BinomialTheoremOQ03.binomial_variance` (needs `2 ≤ n`)

The only new bookkeeping: `binomial_variance_all` / `multinomial_mean_all_n`
discharge the degenerate `n = 0` (variance 0) and `n = 1` (single Bernoulli,
variance `p(1−p)`) cases so the result holds for every `n`.

## Together with the sibling

`multinomial_covariance` (OQ03, `i ≠ j`) + `multinomial_variance` (this file,
`i = j`) determine the full covariance matrix `Σᵢⱼ = n·pᵢ·(δᵢⱼ − pⱼ)`.

## Possible follow-ups

- Assemble `Σᵢⱼ = n·pᵢ·(δᵢⱼ − pⱼ)` as a single matrix-valued statement.
- Singularity / rank `k − 1` of `Σ` from the constraint `∑Xₗ = n`.

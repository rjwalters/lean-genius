# Research State: binomial-theorem-oq-02-oq-01-oq-02-oq-02

## Current State
**Phase**: ACT (complete)
**Path**: full
**Iteration**: 2
**Last Updated**: 2026-07-01 (researcher-6)

## Result (VERIFIED, 0-axiom)
`proofs/Proofs/BinomialTheoremOQ02OQ01OQ02OQ02.lean` (237 lines, 4 theorems, 0 sorries):
the **off-diagonal multinomial covariance** `Cov(Xᵢ, Xⱼ) = − n · pᵢ · pⱼ` for `i ≠ j`,
in the parent's self-contained combinatorial framework (explicit PMF sums over
`s.piAntidiag n`, no measure theory).

Proof via probability generating functions (reusing the parent
`BinomialTheoremOQ02OQ01OQ02.multinomial_mgf_real`):
- `multinomial_pair_pgf` — joint PGF `E[x^Xᵢ y^Xⱼ] = (pᵢx + pⱼy + (1−pᵢ−pⱼ))ⁿ`.
- `multinomial_mean` — `E[Xᵢ] = n·pᵢ` (differentiate the marginal PGF once at 1).
- `multinomial_mixed_moment` — `E[XᵢXⱼ] = n(n−1)·pᵢpⱼ` (differentiate the pair PGF in
  `y` then `x`, both at 1).
- `multinomial_covariance` — `E[XᵢXⱼ] − E[Xᵢ]E[Xⱼ] = −n·pᵢpⱼ` (algebra).

`#print axioms` on all: only `propext / Classical.choice / Quot.sound`.

## History
The proof was drafted (ORIENT: PR #30889) and completed on branch
`research/binomial-oq02010202-covariance` but never merged to `main`. Researcher-6
(2026-07-01) adopted that draft, repaired 4 Mathlib bit-rot points — a contradictory
`split_ifs` branch (`h1.symm.trans h2`) and three `HasDerivAt.sum` higher-order
unification failures (fixed by rewriting `fun t => ∑ k, g k t` into
`∑ k, (fun t => g k t)` via `Finset.sum_apply'` before applying `HasDerivAt.sum`) —
re-verified 0-axiom, and shipped.

## Next Steps
Gallery integration (`src/data/proofs/…`) if desired; the sibling
`binomial-theorem-oq-02-oq-01-oq-01-oq-04` (full covariance matrix) already has an
entry that this off-diagonal result complements.

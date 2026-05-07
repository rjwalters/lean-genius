# Research State: binomial-theorem-oq-02-oq-01-oq-01-oq-03

## Current State
**Phase**: ORIENT (advanced from OBSERVE this session)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-07
**Iteration**: 1

## Current Focus
Reduce the marginal Multinomial CLT to the Binomial CLT (de Moivre–Laplace)
via the already-formalised `multinomial_marginal_pmf` and Mathlib's i.i.d.
CLT applied to the Bernoulli-sum representation of `Binomial(n, p)`.

## Active Approach
Decomposition (see knowledge.md for details):
- **Sublemma A**: marginal-is-Binomial (DONE in `BinomialTheoremOQ02OQ01OQ02.lean`).
- **Sublemma B**: `Binomial = ∑ Bernoulli i.i.d.` (Mathlib lookup needed).
- **Sublemma C**: i.i.d. CLT to Bernoulli (likely a Mathlib one-liner; the
  genuine Mathlib gap if missing).
- **Sublemma D**: assembly A + B + C → marginal CLT.

## Attempt Count
- Total attempts: 1 (this session)
- Approaches tried: 1 (decomposition path documented; no Lean code yet)

## Blockers
- Local Docker build has limited memory (~7.65 GiB), making large
  Mathlib-dependent files risky to verify locally. CI is the ground truth.
- Mathlib's i.i.d. CLT availability in v4.26.0 needs concrete confirmation
  before scaffolding the new file.

## Next Action
**ACT — scaffold new Lean file** in a future session:
1. Confirm Mathlib's i.i.d. CLT signature.
2. Create `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` with the
   marginal-CLT statement and sublemmas A + D as fully proved theorems.
3. If Mathlib's i.i.d. CLT applies directly, complete sublemma C.
   Otherwise, axiomatise sublemma C and isolate the Mathlib gap.

## References
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean:167` —
  `multinomial_marginal_pmf` (sublemma A, already proved).
- `proofs/Proofs/CentralLimitTheorem.lean:375` — local general CLT
  (axiomatised at the standardisation step; characteristic-function form).
- Mathlib: `Mathlib.Probability.Distributions.Binomial` — PMF only,
  no CLT.
- Mathlib: `Mathlib.Probability.CentralLimitTheorem` — i.i.d. CLT
  scaffolding (signature to be verified).

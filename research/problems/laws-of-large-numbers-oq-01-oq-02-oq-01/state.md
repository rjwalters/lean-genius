# Current State

**Phase**: ACT (S3 ready to build)
**Since**: 2026-07-03
**Iteration**: 3 (S3 scoping; S2 shipped)

## Current Focus

**S2 is DONE — do not re-attempt Kronecker.** This leaf's `state.md` previously
still listed S2 as the next action even though S2 had shipped; that staleness
caused a duplicate re-derivation of Kronecker on 2026-07-03 (caught before merge
and discarded). Corrected here.

Kronecker's lemma and the Toeplitz/Silverman weighted-average null step are
already **verified 0-sorry / 0-axiom** on `main`:

- `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02OQ01.lean`
  - `LawsOfLargeNumbers.MZ.kronecker_lemma` (L122)
  - `LawsOfLargeNumbers.MZ.tendsto_weighted_average_zero` (L47)

Current work = **S3 scoping**: the a.s.-convergence-of-independent-`L²`-series
criterion (Kolmogorov). The 2026-07-02 survey called this a ">300 LOC bottleneck"
but never checked Mathlib's martingale-convergence machinery. It turns out the
a.s.-convergence *engine* and every glue lemma already exist in Mathlib (see
`knowledge.md` §S3); the remaining work is **assembly**, not foundations.

## Active Approach

None in-flight (docs/scoping iteration). Next work item is the S3 assembly
below — a real Lean build for a future session.

## Blockers

- **S3 (assembly, multi-session):** wire the existing Mathlib pieces into
  "partial sums of independent mean-zero `L²` variables converge a.s." No
  foundational gap remains; it is glue + bookkeeping (natural filtration →
  martingale property via `condExp_indep_eq` → uniform `L¹` bound via
  `IndepFun.variance_sum` → `Submartingale.exists_ae_tendsto_of_bdd`).

## Next Action

- **S3 (next session, real Lean build):** formalise Kolmogorov's a.s.-convergence
  criterion by assembling the named Mathlib lemmas in `knowledge.md` §S3.
  Start a `*.lean` file, build the natural filtration of `X`, prove the partial
  sums form a `Martingale`, bound `eLpNorm S_n 1 μ` uniformly, and apply
  `Submartingale.exists_ae_tendsto_of_bdd`. Estimated 1–2 sessions now that the
  engine is located (down from the survey's "multi-session, >300 LOC").
- **S4:** assemble truncation (steps 1–3 of the MZ decomposition) + Kronecker
  (S2, done) + Kolmogorov (S3) to conclude MZ.

## Attempt Counts

- Total attempts: 3 (S1 survey; S2 shipped Kronecker; S3 scoping)
- Current approach attempts: 0 (S3 assembly not yet started)
- Approaches tried: 2 (S1 literature/decomposition; S2 Abel+Toeplitz Kronecker)

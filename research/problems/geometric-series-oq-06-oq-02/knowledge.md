# geometric-series-oq-06-oq-02 — Negative-Binomial Series

## Problem

Parent `geometric-series-oq-06` differentiates the geometric series once to get
`∑' n, n·rⁿ = r/(1−r)²`. The open question asks whether term-by-term
differentiation generalizes cleanly to

    ∑' n, binom(n+k, k)·rⁿ = 1/(1−r)^(k+1)   (‖r‖ < 1),

via a descending-factorial weighted geometric series.

**Answer: yes.**

## Summary

The `k`-fold term-by-term derivative of `∑ rⁿ = 1/(1−r)`, normalized by `k!`, is
the negative-binomial series above. Mathlib packages exactly this identity as
`hasSum_choose_mul_geometric_of_norm_lt_one`
(`Mathlib.Analysis.SpecificLimits.Normed`), so the file records named wrappers
plus two genuine derivations. 8 theorems, 0 axioms, 0 sorries, ~218 lines.

## Sessions

### Session 2026-07-01 (Session 1) — Adopt orphan + verify

**Mode**: FRESH
**Outcome**: complete (build verification in progress)

#### What I Did
- Adopted the untracked orphan draft `proofs/Proofs/GeometricSeriesOQ06OQ02.lean`
  + gallery data (created by a prior process that died holding the claim lock,
  never committed, no PR).
- Confirmed the key Mathlib lemma `hasSum_choose_mul_geometric_of_norm_lt_one`
  exists at `Mathlib/Analysis/SpecificLimits/Normed.lean:468` over a
  `NormedDivisionRing 𝕜`; the draft's `[NormedField 𝕜]` extends that and
  `NormedDivisionRing` auto-supplies `HasSummableGeomSeries` (instance at line
  368), so the wrappers typecheck.
- Committed on branch `research/geometric-negbinom-oq0602`; launched docker build.

#### Key Findings
- The parent result `∑ n·rⁿ = r/(1−r)²` is the `(k=1)` family minus the `(k=0)`
  geometric series (`HasSum.sub`), so the parent is a genuine special case.
- Descending-factorial form `∑ (n+k)‿ₖ·rⁿ = k!/(1−r)^(k+1)` follows by rescaling
  by `k!` via `Nat.descFactorial_eq_factorial_mul_choose`.

#### Files
- `proofs/Proofs/GeometricSeriesOQ06OQ02.lean`
- `src/data/proofs/geometric-series-oq-06-oq-02/{meta,annotations}.json`

#### Next Steps
- Confirm `docker-build.sh Proofs.GeometricSeriesOQ06OQ02` compiles clean, then PR.

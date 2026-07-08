# Research State: cauchy-schwarz-integral-lp-duality-synthesis

## Current State
**Phase**: ACT (axiom-elimination reduction, one measure-theory gap from a new brick)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 24

## Current Focus
Eliminate the `riesz_lp_surjective` axiom (`CauchySchwarzIntegralOQ01OQ01OQ02.lean`) via the
σ-finite-support reduction. Per-function step done (`…LpSigmaFiniteSupport.lean`, 0/0). This
session (researcher-2, S24) targeted step (2) COMMON CARRIER: a countable union of
σ-finite-restricted sets is σ-finite.

## Progress this session
The clean **sum-bound** proof of `sigmaFinite_restrict_iUnion` compiles end-to-end in v4.26
**except one line**: `μ.restrict (⋃ n, s n) ≤ Measure.sum (fun n => μ.restrict (s n))` type-checks
and `Measure.sigmaFinite_of_le` applies, but instance resolution cannot find
`SigmaFinite (Measure.sum fun n => μ.restrict (s n))` — i.e. the single missing fact is
"a countable `Measure.sum` of σ-finite measures is σ-finite". See knowledge.md (S24) for the
exact compiling snippet and the three next-step options (inferInstance retry / direct
`FiniteSpanningSetsIn` diagonal with `Nat.unpair` + `MeasurableSet (s n)` / Aristotle).

## Blockers
- **One measure-theory fact**: `SigmaFinite (Measure.sum m)` for countable σ-finite `m` — not
  an available instance; needs a lemma or a `FiniteSpanningSetsIn` diagonal (~short).
- **Parallel**: the `gseq_norm_bound` rpow-drift chain in `…Incomplete01Norm.lean` (~16
  mechanical errors, S19 note) — fast-iteration / Aristotle territory.

## Next Action
Close `SigmaFinite (Measure.sum m)` (one of the three routes in knowledge.md S24) → lands
`sigmaFinite_restrict_iUnion` → step (2) done → steps (3)–(4) eliminate the axiom. No code
shipped this session (the sum-bound file builds up to the one gap and was not committed to
avoid a non-building file).

# Current State

**Phase**: AXIOMATIZED (main conjecture remains as `axiom erdos_1137`)
**Since**: 2026-03-24
**Last Updated**: 2026-06-04 (S1 STATE-SYNC, researcher-1)
**Iteration**: 2

## Current Focus

S1 STATE-SYNC — reconcile stale state.md (Phase: ACT, Iteration: 1,
"Initial exploration") with the shipped `Proofs/Erdos1137Problem.lean`:

- 322 lines, 23 theorems (incl. 3 private), 3 noncomputable defs,
  1 axiom, 0 sorries
- Status: `axiomatized`, badge: `axiom`
- Counts independently verified vs `src/data/proofs/erdos-1137/meta.json`
  (top-level + `leanFile` object) — all consistent
- History: previous iterations eliminated 2 of the original 3 axioms
  via PRs #5614, #32623bc, #5783, #6267, #7364

## Active Approach

Conjecture is encoded as a single axiom `erdos_1137` (the main open
question: `lim_{x→∞} R(x) = 0` where `R(x)` is the Erdős correlation
ratio for consecutive prime gaps). Three definitions support the
statement: `primeGap`, `maxGap`, `erdosRatio`.

Already-proved supporting theorems (axiom-elimination work, all in
the shipped file):
- `nth_prime_strictMono`, `nth_prime_*` enumeration lemmas (5 total)
- `primeGap_pos`, `primeGap_zero..three`, `primeGap_even`,
  `primeGap_ge_two` (parity + small-case bounds)
- `maxGap_mono`, `maxGap_tendsto_atTop` (monotonicity + unboundedness)
- `erdosRatio_le_one` (upper bound; previously axiom #2)
- `primeGap_unbounded` (private; via factorial + Galois connection)

## Blockers

The remaining axiom `erdos_1137` is the open Erdős conjecture itself.
Discharging it requires substantive analytic number theory beyond
the current Mathlib infrastructure (correlation results in the spirit
of Cramér's 1936 work on prime-gap distributions).

## Next Action

No urgent action. Future iterations may:
- Strengthen the small-case enumeration (compute more `primeGap_n`
  values) — purely mechanical via `native_decide`.
- Extract auxiliary lemmas (e.g. a quantitative `maxGap_tendsto_atTop`
  with explicit bounds) once Mathlib's prime-gap library matures.
- Track Mathlib upstream for Cramér-type results that would enable
  partial reductions of `erdos_1137`.

## Attempt Counts

- Total attempts: 5 (PRs #5614, #32623bc, #5783, #6267, #7364)
- Current approach attempts: 5
- Approaches tried: 1 (axiom-elimination via Mathlib supporting lemmas — partial success: 3 axioms → 1)

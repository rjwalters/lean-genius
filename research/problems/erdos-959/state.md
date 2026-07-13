# Current State

**Phase**: COMPLETED
**Status**: axiomatized (open conjecture imported via published result)
**Since**: 2026-03-27T00:41:59.421Z
**Iteration**: 2
**Last Update**: 2026-05-17

## Current Focus

State-sync only. The slug graduated 2026-03-27 (registry COMPLETED) but state.md remained at NEW iter 1 with stale "Initial exploration" focus. Lean formalization is complete with axiomatized references to the Clemen–Dumitrescu–Liu lower bound (arXiv:2505.04283, 2025) — no sorries, two stated axioms.

## Active Approach

Axiomatized statement of Erdős #959 via the Clemen–Dumitrescu–Liu (2025) lower bound:

- `frequencyGap A := maxFrequency A - secondFrequency A`
- `ErdosProblem959 := ∃ C > 0, ∀ n ≥ 2, ∃ A, |A| = n ∧ C·n·log n ≤ frequencyGap A`
- `axiom clemen_dumitrescu_liu` imports the existence statement
- `theorem erdos_959_resolved : ErdosProblem959 := clemen_dumitrescu_liu`

Plus a generalized version:
- `frequencyGapR A r := f(d_r) - f(d_{r+1})` (sorted descending)
- `axiom clemen_dumitrescu_liu_general` imports the r-indexed `C·n·log n / r` bound

## Blockers

None. Slug is at rest-state.

## Next Action

None unless future Mathlib/research progress allows replacing one of the two axioms with a proof.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (axiomatization of CDL'25 result)

## Lean File Inventory

`proofs/Proofs/Erdos959Problem.lean` — 158 LOC

- 7 theorems (`erdos_959_resolved`, `distFrequency_nonneg`, `maxFreq_ge_second`, `distFrequency_zero`, `frequencyGap_empty`, `total_pairs`, `avg_frequency_bound`)
- 8 definitions (`distFrequency`, `distinctDistances`, `maxFrequency`, `secondFrequency`, `frequencyGap`, `frequencyGapR`, `ErdosProblem959`, `ErdosProblem959_strong`)
- 2 axioms (`clemen_dumitrescu_liu`, `clemen_dumitrescu_liu_general`)
- 0 sorries

## Gallery

`src/data/proofs/erdos-959/` exists with canonical `meta.json` (status=axiomatized, badge=axiom, axiomCount=2, lineCount=158, theoremCount=7, definitionCount=8, sorries=0). No drift between Lean file and gallery meta.

## References

- Erdős #959: erdosproblems.com/959
- [CDL25] F. Clemen, A. Dumitrescu, D. Liu, *On multiplicities of interpoint distances*, arXiv:2505.04283 (2025)
- Conjectured strengthening: max gap grows as `n^(1 + c / log log n)` for some `c > 0` (not formalized; open).

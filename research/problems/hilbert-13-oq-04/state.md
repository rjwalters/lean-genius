# Research State: hilbert-13-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-03-30T06:33:00-07:00
**Iteration**: 2 (STATE-SYNC)
**Last touched**: 2026-05-16T08:55Z

## Current Focus
Formalisation of covering dimension (`covDimLE`) and the generalised Kolmogorov–Arnold
representation theorem on compact metric spaces. Two companion Lean files exist on `main`:

- `proofs/Proofs/Hilbert13GeneralSpaces.lean` (480 LOC, 9 theorems, 8 defs, **6 axioms**, 0 sorries)
- `proofs/Proofs/Hilbert13Superposition.lean` (399 LOC, 4 theorems, 8 defs, **4 axioms**, 0 sorries)

Both files build clean against Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` on
`leanprover/lean4:v4.26.0`.

## Active Approach
Discharge the six remaining axioms in `Hilbert13GeneralSpaces.lean` one at a time, starting
with the most tractable: `unitCube_covDimLE_pos` for the interval case (`n = 1`).

## Attempt Count
- Total attempts: 1 (PR #15643 reduced GeneralSpaces axiom count 6→5 by proving
  `covDimLE_of_unique`; PR #15693 restored the count to 6 because the singleton case did not
  also retire `unitCube_covDimLE_pos` — they cover *disjoint* `n` values)
- Current approach attempts: 0 (no Lean ACT yet for the n=1 interval reduction)
- Approaches tried: 1 (singleton base case via `Unique` instance)

## Blockers
None at the math level. **Build infrastructure caveat**: host disk pressure (100% on
`/System/Volumes/Data`, ~7.2 Gi available) makes any new Docker ACT iteration high-risk
until the host is cleaned. This STATE-SYNC is doc-only and does NOT require Docker.

## Sibling files

| Lean file | LOC | theorems | defs | axioms | sorries |
|---|---:|---:|---:|---:|---:|
| `Hilbert13GeneralSpaces.lean` | 480 | 9 | 8 | 6 | 0 |
| `Hilbert13Superposition.lean` | 399 | 4 | 8 | 4 | 0 |

Note: `src/data/proofs/hilbert-13-oq-04/meta.json` only tracks `Hilbert13GeneralSpaces.lean`
(axiomCount: 6). The companion `Hilbert13Superposition.lean` adds 4 further axioms but is
listed as a co-file in the gallery; the `meta.assumptions` field describes the six
`GeneralSpaces` axioms only.

## Remaining axioms (Hilbert13GeneralSpaces.lean)

1. `unitCube_covDimLE_pos (n) (hn : 0 < n)` — upper bound on `dim([0,1]^n)` for n≥1
2. `unitCube_covDim_lower_bound (n) (hn : n ≥ 1)` — sharpness of the upper bound
3. `ostrand_separating_maps` — Ostrand 1965 separating-map theorem
4. `generalized_kolmogorov_arnold` — the generalised KA representation
5. `sternfeld_characterization` — Sternfeld 1985 iff
6. `superposition_2n_plus_1_sharp` — 2n+1 is optimal

The remaining `theorem`-level results (`covDimLE_of_embedding`, `unitCube_superposition`,
`classical_KA_from_general`, `unitCube_superposition_sharp`) are fully discharged from the
six axioms above with no further sorries.

## Next Action
Attempt to prove `unitCube_covDimLE_pos` for `n = 1` (the interval case) as the next ACT.

**Why this is the most tractable axiom**: in dimension 1, the unit cube is `Fin 1 → Set.Icc 0 1`
(equivalent to `Set.Icc 0 1` via uncurrying), and "covering dimension ≤ 1" unfolds to "every
finite open cover admits a refinement of order ≤ 2" — i.e. every point lies in at most 2
refinement sets. For the interval, this is the classical Lebesgue covering theorem restricted
to the one-dimensional case, which admits a direct combinatorial proof via the extreme points
of cover intersections.

See `sessions/2026-05-16-s2-statesync.md` §6 for the full plan, dependency map, LOC forecast,
and risk inventory.

## Iteration History

| Iter | Date (UTC) | Type | Net change | PR / Notes |
|---:|---|---|---|---|
| 1 | 2026-05-04 | ACT | +20 LOC, 6→5 axioms (then restored) | PR #15643 `covDimLE_of_unique` |
| 1 | 2026-05-04 | mechanic-fix | axiom 5→6 | PR #15693 (singleton ≠ general n≥1) |
| 1 | 2026-05-12 | infra | files re-inserted unchanged | PR #18059 (incidental, angle-trisection commit) |
| 2 | 2026-05-16 | STATE-SYNC | docs only | this PR — close 6-week drift |

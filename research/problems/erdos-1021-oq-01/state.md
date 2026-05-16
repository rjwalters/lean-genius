# Current State

**Phase**: ORIENT
**Since**: 2026-05-16 (researcher-11, S2 PREP — orientation survey + sorry inventory + S3 ACT plan)
**Iteration**: 2

## Current Focus

Bootstrap orientation. The Lean infrastructure (`Erdos1021OQ01.lean`,
191 LOC, 8 thms, 2 axioms, **4 sorries**) was scaffolded pre-2026-04-03
via the SCAFFOLD pass but state.md was never updated to reflect that
work. This S2 PREP:

1. Catches state.md up from the 2026-03-30 NEW bootstrap to current
   reality (ORIENT, iter 2).
2. Classifies the 4 sorries by discharge difficulty: MECHANICAL (L112,
   L165) / BLOCKED on parent `k3_case_solved` (L127) / HARD or possibly
   unprovable-as-stated (L136).
3. Proposes S3 ACT targeting the most mechanical (L165 Filter.Tendsto
   chain, ~8 LOC paste-ready).

## Active Approach

Stepwise sorry discharge:
- **S3 ACT (next)**: L165 — `1/(k-1) → 0` via `Tendsto.inv_tendsto_atTop`
  chain (~8 LOC, 2-3 Docker iters expected).
- **S4 ACT (deferred until disk pressure clears)**: L112 — convert local
  `isLittleO` ε=1 instance to a `IsBigO` bound using `Finset.sup`
  ceiling extraction (~15-25 LOC, 3-5 Docker iters expected).
- **S5+ deferred**: L127 unblocks once parent `k3_case_solved` is
  converted from sorry to axiom (a 4-LOC parent edit). L136 needs
  re-examination — the asserted negation may be false (pair-graph
  monotonicity argument seems to support the original statement).

## Blockers

None for S3 ACT (target L165).

## Iteration History

| Iter | Date | Researcher | Type | Outcome |
|---|---|---|---|---|
| 0 | (pre-2026-04-03) | enricher/scaffold | SCAFFOLD | Created `Erdos1021OQ01.lean` (191 LOC, 8 thms, 2 axioms, 4 sorries); gallery entry `src/data/proofs/erdos-1021-oq-01/` |
| 1 | 2026-03-30 | (seeker bootstrap) | INIT | bootstrapped `problem.md` + `state.md` (NEW) and research JSON; never updated post-SCAFFOLD |
| 2 | 2026-05-16 | researcher-11 | PREP | THIS — S2 PREP: orientation survey, 4-sorry inventory + classification, Mathlib bearer survey, S3 ACT plan for L165 |

## Next Action

**S3 ACT (next session)**: discharge sorry #4 at L165 in
`proofs/Proofs/Erdos1021OQ01.lean` (`lower_bound_exponent_tendsto`)
using the paste-ready ~8-LOC `Filter.Tendsto` chain in
`sessions/2026-05-16-s2-prep-orient-survey.md` §3.1.

Replacement code (verbatim from session memo §3.1):

```lean
theorem lower_bound_exponent_tendsto :
    Filter.Tendsto (fun k : ℕ => (3 : ℝ)/2 - 1/((k : ℝ) - 1)) Filter.atTop (nhds (3/2)) := by
  have h1 : Filter.Tendsto (fun k : ℕ => (1 : ℝ) / ((k : ℝ) - 1)) Filter.atTop (nhds 0) := by
    have hk : Filter.Tendsto (fun k : ℕ => ((k : ℝ) - 1)) Filter.atTop Filter.atTop := by
      exact (tendsto_natCast_atTop_atTop).atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
    simpa using hk.inv_tendsto_atTop
  have h2 : Filter.Tendsto (fun k : ℕ => (3 : ℝ)/2 - 1/((k : ℝ) - 1)) Filter.atTop
      (nhds ((3 : ℝ)/2 - 0)) := tendsto_const_nhds.sub h1
  simpa using h2
```

Expected LOC delta: **+6** (replace 1 sorry-line with 7-LOC chain).
Sorry count: 4 → 3. Axiom count: unchanged (2). Docker iters: 2-3
(name-resolution for `inv_tendsto_atTop` variant). Build-pending
fallback if disk hits 100% mid-build (memory trap
`_docker_build_disk_full_ship_build_pending_…`).

**S4 ACT (deferred until disk avail ≥ 50 Gi)**: L112
(`oq01_strictly_beyond_kst`) — see session memo §3.2 for paste-ready
draft with secondary `sorry` for `n < N` Finset.sup extraction.

## Attempt Counts

- Total attempts: 1 (this PREP)
- Current approach attempts: 0
- Approaches tried: 0

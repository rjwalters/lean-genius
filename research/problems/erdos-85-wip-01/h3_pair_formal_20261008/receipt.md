# H3 pair cell (t = 0): build receipt, 2026-10-08

All builds ran on the erdos85 cloud builder through `e85-remote build`,
branch `erdos85/h3-pair-formal-20261008`. Log excerpts are in `logs/`.

## Result

`Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero :
OrderFortyNineTripleCellExcluded 3 0` and
`Erdos85.H3Pair.threeHighCanonicalRepresentativeExcluded_zero :
ThreeHighCanonicalRepresentativeExcluded 0`
(`proofs/Proofs/Erdos85H3PairCell.lean`) are built.

`#print axioms` for both (job 394958, `logs/job-394958-cell.log`):
`propext`, `Classical.choice`, `Quot.sound`, and the 24 axioms
`Erdos85.H3Pair.pairPart_24_NN._native.native_decide.ax_1_1`, NN = 00..23.
No `sorryAx`. The 24 native axioms are what Lean v4.31 `native_decide`
emits for the 24 part theorems; they assert that compiled evaluation of
`pairPart 24 NN` returns `true`. This is not a kernel-only proof.

## Jobs

| Job | Commit | Target | Exit | Notes |
|-----|--------|--------|------|-------|
| 329751 | bc7532e9303 | `Erdos85H3PairSplit` | 0 | Engine, Bridge, Split built; all exports `[propext, Classical.choice, Quot.sound]` |
| 331716 | b3545ac16ae | `Erdos85H3PairCell` | 1 | All 24 parts Built; only the final composition module failed (max recursion in a tactic) |
| 393582 | 64210258477 | `Erdos85H3PairCell` | 0 | Composition fixed; parts replayed, not rebuilt |
| 394958 | dc7f78d47d7 | `Erdos85H3PairCell` | 0 | Doc-comment change in the Cell module only; this is the receipt build |

The part modules, `Split`, `Bridge` and `Engine` are byte-identical between
b3545ac16ae and dc7f78d47d7, so the 24 native results from job 331716 are
the objects the final module imports.

Earlier runs that produced no result: job 302533 (unsplit single-module
search, cancelled by me after about 26 min) and job 320500 (first 24-part
run, cancelled by me after about 13 min to replace a slow heuristic). The
unsplit module was then deleted from the branch.

## Timings (job 331716)

Six Lean processes at a time in one container (32 GiB limit). The
container CPU quota was the wrapper default of 16; `--threads 6` limits
Lake's parallelism, not the cgroup.

- Wall time for the 24 parts: about 100 min (08:17Z to 09:58Z).
- Sum of per-part build times: 31,238 s (8.7 CPU-hours); minimum 838 s,
  maximum 2,005 s, mean 1,302 s. Each figure includes a few seconds of
  import time.
- Engine + Bridge + Split + Cell without the parts: under 30 s.

Per-part seconds: 00 1606, 01 1274, 02 1529, 03 1103, 04 1027, 05 1364,
06 1510, 07 1769, 08 851, 09 1513, 10 1021, 11 1527, 12 884, 13 1104,
14 1530, 15 1263, 16 1505, 17 1070, 18 838, 19 2005, 20 1350, 21 1383,
22 1074, 23 1138.

## Python prototype (sizing only, not evidence)

`engine_prototype.py` mirrors the search. A phase-1-only run reports 1,448
phase-1 leaves and 14,873 phase-1 nodes. A full run was stopped by me at
383 of 1,448 leaves (20,676,243 phase-2 nodes, 182,791 phase-2 leaves,
283,263 phase-3 nodes, no completion found). It was not run to the end,
so there are no full prototype totals. The Lean `pickCore` now counts
through `triCounts`; the prototype still uses the direct count, which
selects the same vertex.

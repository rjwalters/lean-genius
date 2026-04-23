# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 30 available, 556 in-progress, 1406 completed, 8 graduated, 4 blocked

## Selected Problem

- **ID**: erdos-512-incomplete-01
- **Name**: Erdős #512 — Fill Measure Theory Gaps in Littlewood Conjecture Formalization
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 5/10 (estimated higher in practice — see rationale)
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available (fresh — no prior selection)

## Selection Rationale

1. **Fresh candidate** — one of only 4 unselected, unclaimed available problems; highest
   priority over previously-selected problems with equivalent composite scores
2. **High significance (A-tier, 8/10)** — closes concrete gaps in the Erdős #512 gallery
   proof, a flagship formalization; directly improves gallery integrity
3. **Actually more tractable than score suggests** — both sorries are classical results:
   - `L1norm_upper_bound`: triangle inequality + |e^{ix}|=1, a 1-2 hour Mathlib API search
   - `L2_norm (Parseval)`: character orthogonality on [0,1], 2-4 hours; Mathlib has this
   - The comment in problem.md explicitly calls these "mathematically trivial" — the work
     is purely finding the right Mathlib API (norm_integral_le_integral_norm, etc.)
4. **Domain**: Fourier analysis on integers / measure theory — distinct from the last 3
   individual seeker selections (graph theory, combinatorics, integral analysis)
5. **No infrastructure gap** — unlike erdos-268-incomplete-01 which requires missing
   Kovač-Tao 2024 Lean infrastructure, both Erdős #512 sorries use well-established
   Mathlib APIs (Complex.abs_exp_ofReal_mul_I, MeasureTheory.integral_finset_sum)

## Rejection Summary

- **Candidates considered**: 30 available, 6 without prior selection reports (fresh)
- **sperner-ndim-oq-04** (A, sig=8): CLAIMED — active lock file, skip
- **erdos-476-oq-05-wip-01** (B, sig=7): CLAIMED — active lock file, skip
- **szemeredi-full-oq-02** (A, sig=8, tract=3): tract=3 too low — moonshot territory,
  Szemerédi density bound is an extremely hard open problem
- **erdos-268-incomplete-01** (B, sig=7, tract=6): good candidate but lower tier/sig than
  erdos-512; also blocked by missing Kovač-Tao 2024 Lean infrastructure
- **erdos-1155-oq-02** (B, sig=6, tract=5): lower significance, open research question
  about a limiting distribution — probabilistic, very hard to formalize
- **Previously-selected candidates** (24 with selection reports): de-prioritized in favor
  of fresh candidates needing initialization
- **Confidence**: high (clear winner among fresh unclaimed candidates)

## Related Gallery Proofs

- `erdos-512`: Parent proof with sorries at lines 104 and 167 — direct target
- `cauchy-schwarz-integral`: Fourier/integral techniques — method overlap

## Suggested First Steps

1. **OBSERVE**: Read `Proofs/Erdos512Problem.lean` at lines 100-115 and 160-175; understand
   how `expSum`, `expSumNorm`, `L1norm` are defined; map out what's already proven
2. **ORIENT**: Search Mathlib for `norm_integral_le_integral_norm`, `Complex.abs_exp`,
   `Finset.card_eq_sum_ones`, `MeasureTheory.integral_finset_sum`; check if Fourier
   orthogonality on [0,1] exists under `MeasureTheory.Periodic` or `Analysis.Fourier`
3. **DECIDE**: For L1 sorry, attempt triangle inequality route first (highest confidence);
   for L2 sorry, expand `|expSumNorm|²` into double sum and use character orthogonality

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 30 |
| In Progress | 556 |
| Completed | 1406 |
| Graduated | 8 |
| Blocked | 4 |

## Candidate Pool Health

- **Pool depth**: adequate (30 available, well above threshold of 15)
- **Fresh candidates remaining**: 3 (erdos-268-incomplete-01, erdos-1155-oq-02,
  szemeredi-full-oq-02 pending tractability review)
- **Recommendation**: Pool healthy — no replenishment needed this cycle
- **Next refresh**: standard 30-minute interval

## Initialized

- [x] Research workspace exists (approaches/, lean/, literature/, problem.md, state.md)
- [x] Registered in database (status: available)
- [x] Selection report written
- [ ] Ready for /researcher

# Selection Report: fourier-series-oq-02-oq-02

**Date**: 2026-04-23
**Seeker Batch**: seeker/batch-selections-2026-04-23
**Pool Status**: 71 available, 2 in-progress (seeker worktree)

## Selected Problem

- **ID**: fourier-series-oq-02-oq-02
- **Name**: Fourier Coefficient Decay: fourierCoeff_sq_summable_of_holder via p-Series
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Analysis/Harmonic Analysis domain**: Not covered in recent batch selections (Analysis covered L'Hôpital, but not Fourier analysis). Harmonic analysis is a rich area with growing Mathlib support.
2. **Concrete sorry removal**: Directly targets `fourierCoeff_sq_summable_of_holder` in `fourier-series-oq-02`, closing a specific open gap in the gallery.
3. **Mathlib tractability**: The proof is a comparison test using p-series convergence — standard Mathlib tools exist.
4. **Gallery infrastructure**: `fourier-series-oq-02` already establishes the decay bound, providing the key input for this proof.

## Rejection Summary

- **Candidates considered**: 71 available in pool
- **Lower tractability than Catalan (6 vs 7)**: API discovery overhead for integer-indexed summability may require more exploration
- **Still valuable**: Concrete sorry removal + harmonic analysis domain diversification
- **Confidence**: medium-high (mathematical path clear, but API navigation uncertain)

## Related Gallery Proofs

- `fourier-series-oq-02`: Parent proof with Hölder decay bound — provides key input lemma
- `fourier-series`: Base Fourier series gallery entry

## Suggested First Steps

1. **OBSERVE**: Read `fourier-series-oq-02` Lean source to understand current sorry structure
2. **ORIENT**: Search Mathlib for `summable_one_div_pow`, `Real.summable_pow_div`, `HasSum.of_norm`
3. **DECIDE**: Verify decay bound is sorry-free or can be assumed; then compose with comparison test

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 71 |
| In Progress | 2 |
| Graduated | 661 |

## Candidate Pool Health

- Pool depth: adequate (71 available >> 15 threshold)
- Harmonic Analysis domain added
- Next refresh recommended: 30 minutes (standard interval)

## Initialized

- [x] Research workspace created: `research/problems/fourier-series-oq-02-oq-02/`
- [x] problem.md populated with mathematical context
- [x] Registered in database with status 'available'
- [x] Pool synced (research/candidate-pool.json → .lean/state/candidate-pool.json)
- [ ] Ready for /researcher

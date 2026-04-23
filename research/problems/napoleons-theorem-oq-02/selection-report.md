# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 26 available, 558 in-progress, 1408 completed, 3 graduated, 1 blocked

## Selected Problem

- **ID**: napoleons-theorem-oq-02
- **Name**: Napoleon's Theorem: Connection to Discrete Fourier Transform
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 5/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Composite score 57** — third-ranked fresh candidate. Lower than the two co-leaders
   (score=67) but selected for domain diversity: this is geometry + complex analysis +
   Fourier theory, a fresh combination not covered by any active claims or recent selections.

2. **DFT interpretation is elegant and novel** — the connection between Napoleon's theorem
   and the DFT is not a shallow observation. The outer Napoleon triangle centroids are
   precisely the DFT coefficients of the vertex positions (3-point DFT). This lifts the
   theorem from a Euclidean geometry curiosity to a Fourier analysis statement, with
   potential connections to `MeasureTheory.fourier` and `Mathlib.Analysis.InnerProductSpace`.

3. **Clear workspace with concrete Lean goal** — the workspace has a specific theorem
   statement (`napoleon_dft_connection`) involving primitive 3rd roots of unity. The
   mathematical content reduces to verifying a linear algebraic identity over ℂ, which
   should be within reach of `ring` and `norm_num`.

4. **Domain diversity** — geometry/complex analysis has not appeared in recent fresh
   selections. The DFT angle makes this distinct from the main Napoleon gallery proof.

## Rejection Summary

- **Candidates considered**: 26 available (12 fresh, 14 with prior selection reports)
- **All moonshot candidates (tract ≤ 2)**: rejected — Goldbach, twin primes, Sophie Germain
- **Szemerédi family**: rejected (4 problems) — domain saturation from recent selections
- **erdos-476-oq-05-wip-01**: rejected — has active claim
- **isoperimetric-theorem-oq-03**: considered (A-tier, sig=8, tract=4, score=48) but
  requires Riemannian geometry infrastructure not available in Mathlib; deprioritized
- **Confidence**: high (clear domain diversity justification; no competing geometry candidates)

## Related Gallery Proofs

- `napoleons-theorem`: Parent proof — establishes the equilateral Napoleon triangle via
  Euclidean geometry. This OQ asks for the DFT reformulation of the same fact.
- `triangle-angle-sum`: Angle geometry infrastructure shared with Napoleon proof

## Suggested First Steps

1. **OBSERVE**: Read `proofs/Proofs/NapoleonsTheorem.lean` to find the centroid computation
   and `napoleon_outer_centroid`. Verify what definition is used for centroid and how
   vertices are represented (as `ℂ` or as `EuclideanSpace`).

2. **ORIENT**: Define the 3-point DFT over ℂ:
   `Z k := ∑ j : Fin 3, z j * ω ^ (j.val * k)`
   where `ω = exp(2πi/3)`. The claim is that `napoleon_outer_centroid z k = Z 1 / 3 * ω^k`.
   Verify this by direct computation on a triangle.

3. **DECIDE**: The proof likely splits into:
   - Prove the DFT identity: `Z 1 / 3 * ω^k` equals the centroid formula (pure complex arithmetic)
   - Connect to `napoleon_outer_centroid` using `IsPrimitiveRoot ω 3`
   The `ring` tactic or `norm_num` with primitive root hypotheses may close the arithmetic.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 26 |
| In Progress | 558 |
| Completed | 1408 |
| Graduated | 3 |
| Blocked | 1 |

## Candidate Pool Health

- Pool depth: **adequate** (26 available, threshold=15)
- Recommendation: Pool healthy
- Next refresh recommended: next scheduled cycle (~30 min)

## Initialized

- [x] Research workspace exists (`research/problems/napoleons-theorem-oq-02/`)
- [x] problem.md populated
- [x] state.md: OBSERVE phase
- [x] Ready for /researcher

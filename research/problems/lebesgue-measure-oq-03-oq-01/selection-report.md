# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 84 available, 1257 in-progress, 589 completed, 7 graduated

## Selected Problem

- **ID**: lebesgue-measure-oq-03-oq-01
- **Name**: No Translation-Invariant Measure on Infinite-Dimensional Spaces
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **A-tier, high significance (8/10)**: This is a foundational result in infinite-dimensional analysis — the non-existence of a σ-finite translation-invariant Borel measure on any infinite-dimensional normed space (analogous to Lebesgue measure). It explains why Gaussian measures (rather than Lebesgue-type measures) are central to stochastic analysis and QFT.
2. **Tractability (7/10)**: The classical proof (Anderson-Kadec; or direct construction via covering argument) is well-established. The key step is showing that the unit ball in an infinite-dimensional space can be covered by countably many balls of radius 1/2 — combined with translation invariance, this forces measure 0 or ∞. This is a clean ε-ball argument amenable to Lean.
3. **Domain diversity**: Infinite-dimensional measure theory / functional analysis — completely distinct from recent seeker selections (Szemerédi combinatorics, isoperimetric geometry, p-adic analysis).

## Quality Gate

- Near-duplicate of recent completions? **No** — the gallery's `lebesgue-measure` proof covers finite-dimensional measure theory; infinite dimensions are a separate regime.
- Shallow specialization? **No** — the non-existence of translation-invariant measure is a structural theorem with deep implications for probability theory and QFT.
- One-off example check? **No** — applies to ANY infinite-dimensional normed space.
- Significance ≥ 3? **Yes** (8/10).
- Last 3 selections same domain? **No** — functional analysis/infinite-dimensional has not appeared recently.

## Rejection Summary

- **Candidates considered**: 84
- **Confidence**: high — tied for score 78 with ptolemys-theorem-oq-01-oq-01; both selected this batch

## Related Gallery Proofs

- `lebesgue-measure`: Finite-dimensional Lebesgue measure construction — direct precursor.
- `lebesgue-measure-oq-03`: Parent open question about measure theory in infinite dimensions.
- `2d-navier-stokes`: Uses measure theory on function spaces — conceptual connection.

## Suggested First Steps

1. **OBSERVE**: Search Mathlib for `MeasureTheory.Measure.IsLocallyFiniteMeasure` and translations invariance lemmas. Check `MeasureTheory.Measure.haar_measure` (Haar measure) documentation — for infinite-dim spaces, Haar measure is not locally finite.
2. **ORIENT**: The classical proof via infinite covering: in any infinite-dimensional Banach space, the closed unit ball is NOT compact, and can be covered by countably many open ε-balls (for any ε < 1). If translation-invariant measure μ existed, then μ(B(0,1)) = μ(B(x,1)) for all x, leading to contradiction with σ-finiteness.
3. **DECIDE**: State the theorem as `theorem no_translation_invariant_locally_finite_measure (E : Type*) [NormedAddCommGroup E] [InfinitelyDimensional ℝ E] : ¬∃ μ : Measure E, ...`. Check if Mathlib has `InfinitelyDimensional` or equivalent.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 84 |
| In Progress | 1257 |
| Completed | 589 |
| Graduated | 7 |
| Blocked | 2 |

## Candidate Pool Health

Pool is **adequate** (84 >> threshold 15). No replenishment needed.

- Pool depth: adequate
- Recommendation: Pool healthy
- Next refresh recommended: 30 minutes

## Initialized

- [x] Research workspace exists at `research/problems/lebesgue-measure-oq-03-oq-01/`
- [x] problem.md present (formal statement to be refined during OBSERVE phase)
- [x] Registered in `research/db/knowledge.db` with status 'available'
- [x] Ready for /researcher

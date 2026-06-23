# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 1222 in-progress, 545 completed, 3 graduated, 2 blocked

## Selected Problem

- **ID**: triangular-reciprocals-oq-02
- **Name**: Formalize connection: ∑1/(n(n+k)) = H_k/k via digamma function
- **Tier**: C
- **Significance**: 5/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among truly fresh candidates**: Composite = 75 = (tractability 7 × 10) + significance 5,
   with knowledge_tier=0 (EMPTY). Tied with `taylor-sincos-convergence-oq-01` at 75, but the latter
   is a potential shallow extension (axiom bridging on an already-completed proof family), making
   this the stronger selection.
2. **Not recently selected on any branch**: `triangular-reciprocals-oq-02` has no seeker commit
   across all branches, ensuring no 2-hour cooldown conflict and fresh research territory.
3. **Domain diversity**: Recent selections across branches concentrated in Algebra/Group Theory
   (`burnside-counting-oq-01`), Geometry/Graph Theory (`unit-distance-independence-oq-02`), and
   Number Theory (`erdos-109`). Analysis/Special Functions adds clear diversity.
4. **Active sibling research**: `triangular-reciprocals-oq-01` is in-progress, `oq-03` and
   `oq-03-oq-02` are completed. The researcher can leverage existing lemma infrastructure from
   the `triangular-reciprocals` family while tackling the new digamma connection.

## Ranking Summary (top 10 candidates)

| ID | Sig | Tract | KTier | Composite | Notes |
|----|-----|-------|-------|-----------|-------|
| unit-distance-independence-oq-02 | 8 | 7 | 0 | 78 | Cooldown (selected 19:49 today) |
| mean-value-theorem-oq-04 | 7 | 7 | 0 | 77 | Selected on main/other branches |
| erdos-szekeres-oq-01 | 6 | 7 | 0 | 76 | Selected recently on mechanic branch |
| euler-identity-oq-01-oq-04 | 6 | 7 | 0 | 76 | Selected on this branch |
| taylor-theorem-oq-02 | 6 | 7 | 0 | 76 | Selected on main |
| vietas-formulas-oq-02 | 6 | 7 | 0 | 76 | Selected on main |
| taylor-sincos-convergence-oq-01 | 5 | 7 | 0 | 75 | Quality gate: shallow extension |
| **triangular-reciprocals-oq-02** | **5** | **7** | **0** | **75** | **SELECTED — fresh, passes quality gate** |
| factor-remainder-nullstellensatz-oq-02 | 7 | 6 | 0 | 67 | Next if rejected |
| prime-gap-bounds-oq-03 | 7 | 7 | 3 | -2923 | RICH knowledge (93 lines) — deprioritized |

## Rejection Summary

- **Candidates considered**: 15 available
- **Candidates rejected**: 14
  - 6 rejected: recently selected on this branch or sibling branches (unit-distance, mean-value, erdos-szekeres, euler-identity, taylor-theorem, vietas-formulas)
  - 1 rejected: quality gate — `taylor-sincos-convergence-oq-01` is a shallow extension of two already-completed proofs in the same family
  - 1 rejected: RICH knowledge tier — `prime-gap-bounds-oq-03` (93 knowledge lines, composite -2923)
  - 6 lower scores: buffons-needle, wolstenholme, erdos-ko-rado, brouwer, szemeredi, factor-nullstellensatz
- **Confidence**: medium (two candidates tied at 75; primary tiebreaker is quality gate)

## Related Gallery Proofs

- `triangular-reciprocals`: Sum of reciprocals of triangular numbers (base proof)
- `triangular-reciprocals-oq-01`: Reciprocal sums of higher figurate numbers (in-progress — sibling)
- `triangular-reciprocals-oq-03`: Alternating sum of triangular reciprocals (completed)
- `harmonic-divergence`: Harmonic series divergence — H_k appears as the target value
- `harmonic-divergence-oq-01/oq-02/oq-04`: Extensions with harmonic number bounds

## Suggested First Steps

1. **OBSERVE**: Survey what `triangular-reciprocals-oq-01` (in-progress) has proved so far —
   specifically what lemmas about partial fractions and telescoping sums are already available.
   Also check Mathlib for `Real.digamma` or `Complex.Gamma` API.
2. **ORIENT**: The key identity is ∑_{n=1}^∞ 1/(n(n+k)) = (1/k)(H_k) where H_k is the k-th
   harmonic number. The digamma connection is ψ(k+1) = H_k - γ (Euler-Mascheroni constant).
   Scout for whether Mathlib formalizes this relationship in `Analysis.SpecialFunctions.Gamma`.
3. **DECIDE**: If Mathlib lacks digamma, decide whether to (a) prove the identity directly via
   partial fractions (1/(n(n+k)) = (1/k)(1/n - 1/(n+k))) and telescoping, or (b) axiomatize
   the digamma connection and prove the main identity under that assumption.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 1222 |
| Completed | 545 |
| Graduated | 3 |
| Blocked | 2 |
| **Total** | **1787** |

## Candidate Pool Health

- **Pool depth**: adequate (15 available > threshold of 5)
- **Recommendation**: Pool health is satisfactory. Many high-scoring problems (76-78) have already
  been selected on various branches, leaving Tier B composite 60-70 and Tier C composite 75 as
  the live frontier. Consider a replenishment run if available count drops below 5.
- **Next refresh recommended**: When available count < 5 or after 5 more seeker cycles

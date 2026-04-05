# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 2 available, 386 in-progress, 1222 completed, 1 graduated

## Selected Problem

- **ID**: hilbert-10-oq-03
- **Name**: Characterize number fields with decidable H10 (Hilbert's 10th)
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 4/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Only Tier A available problem**: hilbert-10-oq-03 is the sole Tier A candidate that is genuinely available in both the database and candidate pool.
2. **EMPTY knowledge tier**: The workspace exists (initialized scaffolding) but contains no knowledge content — composite score 48 (highest positive score among all available candidates).
3. **Significance 8**: Characterizing which number fields have decidable H10 is a deep open problem in computability and number theory, touching Mazur's conjecture, Shlapentokh's undecidability results, and the status of H10 over ℚ.
4. **Domain diversity**: Computability/number theory — different from recent selections (combinatorics/Erdős, geometry/lattices, probability/integral geometry).
5. **Pool sync applied**: Fixed stale `.lean/state/candidate-pool.json` — 10 in-progress problems were incorrectly marked "available" in the old file. Restored to 2 true available candidates.

## Rejection Summary

- **Candidates considered**: 2 truly available (after DB/pool sync correction)
- **Rejected**: `binary-gcd-oq-01-oq-04-oq-01` — Tier C, significance 5, tractability 6; lower tier and lower significance than the selected problem.
- **Pool sync correction**: 10 previously "available" in old `.lean/state/candidate-pool.json` (e.g., `cube-root-2-irrational-oq-01`, `minkowski-theorem-oq-02-oq-01`, `erdos-191-incomplete-01`, etc.) were "in-progress" in the database — the pool file was stale and has been corrected.
- **Confidence**: high (only one Tier A available candidate, clear winner)

## Related Gallery Proofs

- **hilbert-10**: Parent proof — MRDP theorem (undecidability over ℤ), axiomatized with 4 load-bearing axioms. The target must reduce to or extend this framework.
- **hilbert-10-oq-01**: H10 over ℚ (in-progress) — directly related; the two open sibling questions partition the characterization problem.
- **hilbert-10-oq-02**: DPRM extensions and decidability connections (in-progress) — shares DPRM framework.

## Suggested First Steps

1. **OBSERVE**: Survey the known decidability landscape for H10 over number fields. Key sources: Shlapentokh (2007) "Hilbert's Tenth Problem: Diophantine Classes and Extensions to Global Fields"; Poonen (2003) survey on undecidability in number theory; Denef (1975) — undecidability for rings of integers of imaginary quadratic fields.
2. **ORIENT**: Map the known cases — undecidable: rings of integers of imaginary quadratic fields (Denef 1975), many subrings of number fields (Shlapentokh). Open: H10 over ℚ, real quadratic fields. Identify the sharpest formalization target that is both known and non-trivial.
3. **DECIDE**: Feasible Lean 4 angle — formalize undecidability for the ring of integers of at least one imaginary quadratic field (e.g., ℤ[i] or ℤ[√-2]) by reduction to the parent `hilbert-10` axioms, giving a concrete positive result for the "characterization" question.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 2 |
| In Progress | 386 |
| Completed | 1222 |
| Graduated | 1 |
| **Total** | **1611** |

## Candidate Pool Health

- **Pool depth**: critical (only 2 truly available problems after sync)
- **Sync note**: The old `.lean/state/candidate-pool.json` was 10 "available" entries ahead of the database. These 10 problems (previously worked on by researchers) were reset to "in-progress" in the DB-authoritative pool. This selection run corrected the discrepancy.
- **Recommendation**: Pool needs immediate replenishment. Run `--refresh` to extract new open questions from gallery proofs, or promote high-value stalled in-progress problems back to "available" after reviewing their research state.
- **Next refresh recommended**: immediately (critical depth)

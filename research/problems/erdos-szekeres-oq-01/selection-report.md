# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 15 available, 1211 in-progress, 545 completed

## Selected Problem

- **ID**: erdos-szekeres-oq-01
- **Name**: Formalize Erdős-Szekeres with explicit pair tracking for pigeonhole
- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **Highest composite score among unselected candidates**: Score = 76 (EMPTY knowledge tier: 0 penalty + tractability×10=70 + significance=6). Three higher-scoring problems (unit-distance-independence-oq-02 score 78, mean-value-theorem-oq-04 score 77, euler-identity-oq-01-oq-04 score 76) were already selected in earlier seeker runs today.
2. **EMPTY knowledge tier**: No prior research workspace — first-exploration priority.
3. **Domain diversity**: Today's earlier selections covered combinatorial geometry, analysis, and algebra. Erdős-Szekeres is combinatorics/order theory — a fresh domain.
4. **Tractability 7**: The core proof strategy is explicit: use a pigeonhole argument over pairs (a_i, length of longest increasing subsequence ending at i). The Lean challenge is making this pair tracking fully formal. Mathlib has strong Finset/List/Order infrastructure.
5. **Meaningful advance**: The parent proof `erdos-szekeres` has 2 axioms. Fully formalizing the pigeonhole argument with explicit pair tracking would address the first open question directly, potentially reducing the axiom count.

## Rejection Summary

- **Candidates considered**: 15 available
- **Candidates rejected**: 14
  - `unit-distance-independence-oq-02` (score 78): Already selected today (selection-report.md dated 2026-04-05)
  - `mean-value-theorem-oq-04` (score 77): Already selected today
  - `euler-identity-oq-01-oq-04` (score 76, tie): Already selected today; also algebra domain covered
  - `vietas-formulas-oq-02` (score 76, tie): Algebra — same domain as euler-identity already selected; domain diversity penalty applied
  - `taylor-theorem-oq-02` (score 76, tie): Analysis — same domain as mean-value-theorem already selected; domain diversity penalty applied
  - `taylor-sincos-convergence-oq-01` (score 75, tier C): Lower significance (5/10), tier C
  - `triangular-reciprocals-oq-02` (score 75, tier C): Lower significance (5/10), tier C
  - `factor-remainder-nullstellensatz-oq-02` (score 67): Lower tractability (6)
  - `buffons-needle-oq-01-oq-04` (score 66): Lower tractability (6) and significance
  - `wolstenholme-theorem-oq-03` (score 66): Lower tractability (6) and significance
  - `erdos-ko-rado-oq-04` (score 57): Lower tractability (5)
  - `brouwer-fixed-point-oq-04-oq-04` (score 56): Lower tractability (5)
  - `szemeredi-theorem-oq-01` (score 48): Low tractability (4)
  - `prime-gap-bounds-oq-03` (score -2923): RICH knowledge tier (93 lines), only if new approach found
- **Confidence**: medium (three-way tie at score 76; diversity tiebreaker applied)

## Related Gallery Proofs

- `erdos-szekeres`: Parent proof — axiomatized (2 axioms), 0 sorries. OQ-01 asks for explicit pair tracking in the pigeonhole argument.
- `ramseys-theorem`: Closely related — both prove existence of structure in large sequences/graphs via pigeonhole-style reasoning.
- `pigeonhole-principle`: Core technique — explicit pair tracking generalizes standard pigeonhole applications.

## Suggested First Steps

1. **OBSERVE**: Read `src/data/proofs/erdos-szekeres/meta.json` and the Lean source `proofs/Proofs/ErdosSzekeres.lean` to understand what the 2 axioms are and where the pigeonhole argument is currently stated vs. proved.
2. **ORIENT**: Survey Mathlib for `List.Sublist`, `Finset.exists_ne_map_eq_of_card_lt_of_mem` (pigeonhole), and order theory lemmas about monotone subsequences. Check if `Finset.exists_monotone_subseq` or similar exists.
3. **DECIDE**: Determine whether the full proof can be written using Mathlib's existing `List.Sublist` and Finset pigeonhole directly, or whether custom pair-tracking infrastructure is needed.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 15 |
| In Progress | 1211 |
| Completed | 545 |
| Graduated | 3 |
| Blocked | 2 |

## Candidate Pool Health

Pool depth: adequate (15 available). No replenishment needed.

- **Pool depth**: adequate
- **Recommendation**: Pool healthy — 15 available problems span combinatorics, geometry, analysis, algebra, number theory
- **Next refresh recommended**: When available count drops below 5

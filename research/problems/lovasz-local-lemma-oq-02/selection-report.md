# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 17 available, 509 in-progress, 1236 completed

## Selected Problem

- **ID**: lovasz-local-lemma-oq-02
- **Name**: Prove that the LLL threshold T(d) is tight: there exist instances where p = T(d) is the exact threshold
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 6/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge tier** gives highest composite score priority. No research has been started on the threshold tightness question, making it a fresh target.

2. **Diversity**: Recent selections (euler-identity-oq-01-oq-04, mathematical-induction-oq-03, prime-gap-bounds-oq-03) are in analysis and number theory. This problem is in combinatorics/probabilistic method — a distinct domain.

3. **Tractability assessment**: Tier B with tractability 6/10. The full probabilistic tightness proof requires measure theory, but there's a tractable algebraic reformulation: proving the symmetric LLL assignment achieves equality in the condition — the algebraic sharpness statement — stays within the existing rational arithmetic framework.

4. **Strong foundation**: `LovaszLocalLemma.lean` already defines `lllThreshold` and proves `threshold_satisfies_lll`. The tightness direction extends naturally from existing infrastructure.

## Rejection Summary

- **Candidates considered**: 17 available
- **Candidates rejected**: 16
  - **euler-identity-oq-01-oq-04**: selected 2 commits ago — domain overlap, cooldown
  - **mathematical-induction-oq-03**: selected 3 commits ago — cooldown
  - **prime-gap-bounds-oq-03**: selected 4 commits ago, MODERATE knowledge (93 lines) — lower composite score
  - **isosceles-triangle-oq-03**: C tier, sig=5 — basic area formula, fails quality gate (no theory-level implications)
  - **mean-value-theorem-oq-04**: analysis domain — same area as euler-identity, diversity penalty
  - **divisibility-rules-oq-03**: number theory — domain overlap with recent selections
  - **minkowski-fundamental-theorem-oq-02**: Tier A/sig=8 but tract=6 — strong second choice; deprioritized due to higher difficulty vs this session's exploration phase
  - **feuerbachs-theorem-defs-oq-02**: template-only knowledge.md but equal score — deprioritized for geometry domain
  - **remaining 8**: lower composite scores or same domain
- **Confidence**: medium (several candidates in the 66-68 score range; score spread is tight)

## Related Gallery Proofs

- `lovasz-local-lemma`: Core LLL formalization — direct foundation, `lllThreshold d` already defined
- `lovasz-local-lemma-oq-03` (Moser-Tardos): sibling OQ, algorithmic direction — different angle

## Suggested First Steps

1. **OBSERVE**: Read `LovaszLocalLemma.lean` Parts V-VI and the `lllThreshold_eq_product` / `threshold_satisfies_lll` theorems — understand the existing threshold bridge
2. **ORIENT**: Survey Shearer's 1985 tightness result; identify what algebraic lemmas can be formalized without full measure theory
3. **DECIDE**: Target the algebraic sharpness statement first — prove that x_i = 1/(d+1) is the unique minimizer of the LLL product condition, so no smaller assignment satisfies the general LLL condition

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 17 |
| In Progress | 509 |
| Completed | 1236 |
| Blocked | 2 |

## Candidate Pool Health

Pool is adequate with 17 available problems across combinatorics, geometry, algebra, and analysis domains.

- Pool depth: **adequate** (17 available)
- Recommendation: Pool healthy; no replenishment needed this cycle
- Next refresh recommended: when available count drops below 5

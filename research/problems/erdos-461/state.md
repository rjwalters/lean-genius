# Current State

**Phase**: ACT
**Path**: full
**Since**: 2026-06-04 (S5 ACT, researcher-1: added `smoothDistinctCount_one` boundary-case identity)
**Iteration**: 5

## S5 ACT (researcher-1, 2026-06-04)

Added `smoothDistinctCount_one (n : ℕ) : smoothDistinctCount n 1 = 1` —
a tiny derived corollary combining the existing `smoothDistinctCount_pos`
(≥ 1) and `smoothDistinctCount_t_le_one` (≤ 1) bounds at `t = 1`,
closed by `omega`. The single value is `1` because `smoothComponent 1 m = 1`
for all `m` (no primes are below 1). Fills the trivial `t = 1` boundary
case as an exact identity rather than two-sided bound.

Stats: 281 → 290 LOC, 23 → 24 theorems, 1 axiom (unchanged, deep classical
`erdos_graham_lower`), 0 sorries (unchanged). Build verification deferred
to Mechanic/Auditor (local Docker daemon I/O-error state — same precedent
as earlier researcher-1 sessions this period).

## Current Focus

Infrastructure building for smooth components (`smoothComponent`, `smoothDistinctCount`)
and `ErdosProblem461` main conjecture (`∃ C > 0, ∃ t₀, ∀ t ≥ t₀, ∀ n,
C·t ≤ f(n,t)`). The weaker Erdős–Graham bound `f(n,t) ≫ t/log t` is captured as
an axiom (`erdos_graham_lower`, deep) per Erdős–Graham (1980).

Lean file `proofs/Proofs/Erdos461Problem.lean` (290 LOC, 24 theorems, 1 axiom,
3 definitions, 0 sorries) contains: smooth component definition, infrastructure
lemmas (multiplicativity, unit characterization, divisibility), trivial-`t`
boundary cases (including the new exact `t = 1` identity), distinct-count
positivity.

## Active Approach

Mathlib bearer-driven infrastructure development. Per knowledge.insights:
- `Nat.factors`-list manipulation for `smoothComponent`
- `Nat.factors_mul` permutation for multiplicativity
- `List.dvd_prod` contradiction for unit characterization

## Blockers

None. `erdos_graham_lower` axiom is intentional (deep classical bound — Erdős–Graham
1980 proved it; formalization would require sieve theory beyond current scope).

## Next Action

Continue ACT-phase infrastructure:
- Candidate next lemmas: `smoothComponent_largest` (already proved per PR #4902);
  factor count bounds; `smoothDistinctCount` lower bound for small `t` cases.
- Long-term: `ErdosProblem461` main conjecture (`f(n,t) ≫ t`) remains the OQ; the
  Erdős–Graham `t/log t` bound is the best known unconditional lower bound.

## Attempt Counts

- Total attempts: 6 (estimated from 4 merged substantive research PRs + 2 enrichment PRs)
- Current approach attempts: 1
- Approaches tried: 1 (Mathlib bearer-driven infrastructure)

## PR History (snapshot)

| # | Title | Date | Type |
|---|---|---|---|
| #4902 | Research: prove `smoothComponent_largest` (0 sorries) | 2026-03-22 | research |
| #2940 | enrich: deepen erdos-461 mathContext + cross-refs | 2026-02-14 | enrichment |
| #2465 | enrich(batch): erdos-461 + 3 — mathContext, deepen annotations | 2026-02-10 | enrichment |
| #2441 | enrich(batch): erdos-461 + 5 — mathContext, deepen annotations | 2026-02-10 | enrichment |
| #2275 | Research: fix unsound axiom, add smooth component lemmas | 2026-02-08 | research |
| #1183 | Enhance erdos-461: Distinct Smooth Components in Short Intervals | 2026-01-26 | research |

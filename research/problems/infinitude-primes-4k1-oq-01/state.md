# Research State: infinitude-primes-4k1-oq-01

## Current State
**Phase**: OBSERVE (S1 — Mathlib `SumTwoSquares.lean` API pin-survey complete; paste-ready S2 SCAFFOLD code documented)
**Path**: full
**Since**: 2026-05-30 (S1 OBSERVE; problem created 2026-04-12T14:53:27-07:00, 48d idle)
**Iteration**: 1 OBSERVE

## Current Focus
Mathlib API pin-verified at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Key finding: `Nat.Prime.sq_add_sq` at line 35 of `Mathlib/NumberTheory/SumTwoSquares.lean` provides the hard direction (`p % 4 ≠ 3 → ∃ a b, a^2 + b^2 = p`) directly. The OQ-01 biconditional is a ~50-LOC wrapper.

## Active Approach
**Approach 1 (Direct Mathlib wrapper)** — per problem.md §"Potential Approaches" §1. Confirmed feasible.

Paste-ready Lean blueprint in S1 session note `sessions/2026-05-30-s1-observe-mathlib-sumtwosquares-api-survey.md` §4.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0 (S1 is OBSERVE-only)
- Approaches tried: 0

## Blockers
None.

## Next Action
**S2 SCAFFOLD/ACT**: paste §4 code from S1 session note into new file `proofs/Proofs/InfinitudePrimes4k1OQ01.lean`. Pre-flight build `Proofs.InfinitudePrimes4k1` at Docker first (per S20 INFRA-RECOVERY lesson from concurrent slug `angle-trisection-oq-05-oq-04`) to verify no latent Mathlib regressions in parent infrastructure.

## Session Log

| Iter | PR | Type | Author | Title summary |
|------|------|------|--------|---------------|
| S1 | this PR | OBSERVE | researcher-1 | Mathlib `SumTwoSquares.lean` API pin-survey at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; 6 bearers pin-verified (F1 `Nat.Prime.sq_add_sq` + 5 supporting); paste-ready S2 SCAFFOLD Lean (~50 LOC, 0 sorries) (doc-only) |

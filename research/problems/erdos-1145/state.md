# Research State: erdos-1145

## Current State
**Phase**: AXIOMATIZED — formalization in final state for an open conjecture (researcher-10 S2 COMPLETION-SYNC 2026-05-13)
**Path**: full
**Since**: 2026-05-13 (S2 COMPLETION-SYNC; original since: 2026-01-15)
**Iteration**: 2

## Conclusion (S2 COMPLETION-SYNC)

The Lean formalization is **complete in the only sense possible** for an unresolved Erdős conjecture:
- `proofs/Proofs/Erdos1145Problem.lean` is 737 lines, **0 sorries**, **1 axiom**.
- The single remaining axiom is `erdos_sarkozy_conjecture` itself (the open conjecture being formalized, L151).
- 25 supporting theorems are proved, including:
  - `isTwoSetBasis_iff` (L70), `twoSetRepFunc_pos_of_mem` (L107), `twoSetRepFunc_mono` (L120)
  - `erdos_1145_implies_28` (L184) — shows this conjecture implies Erdős–Turán #28
  - `ruzsa_unique_rep` (L343), `ruzsa_rep_bounded` (L430), `ruzsa_is_basis` (L439) — Ruzsa example
  - `ratio_condition_necessary` (L594) — the asymptotic-ratio hypothesis is necessary
  - `sum_of_reps_bound` (L630), `sum_of_reps_lower_bound` (L645) — sum-of-reps inequalities

## What this slug claims, honestly

`erdos-1145` formalizes the Erdős–Sárközy Conjecture (https://erdosproblems.com/1145):
> If `A, B ⊆ ℕ` are infinite, `a_n / b_n → 1` (asymptotic ratio), and `A + B` covers all sufficiently large integers, then `r_{A,B}(n)` is unbounded.

The conjecture itself is **OPEN** in the literature. The formalization:
1. States the conjecture precisely as `axiom erdos_sarkozy_conjecture`.
2. Proves all standard supporting machinery (representation function, asymptotic ratio, two-set basis, Ruzsa counterexamples).
3. Connects to Erdős–Turán #28 via `erdos_1145_implies_28`.

There is **no further research session** that can resolve this slug without resolving the open mathematical conjecture itself.

## Why this PR is doc-only

The prior `state.md` was a 2026-01-15 seeker-init stub (Phase: NEW, "Begin problem exploration"). The JSON `currentState.phase` was `ACT`. Both are out of sync with the actual reality: the Lean file has been at `0 sorries, 1 axiom (= the conjecture)` since the 2026-03-30 work merged.

Updating these documents:
- Prevents future researcher sessions from wasting claims on this slug (the `claim-random` script picks RICH-tier slugs based on JSON knowledge richness; an honest `AXIOMATIZED` phase + `completed` pool sync should remove it from the candidate pool).
- Documents the natural endpoint for an "Erdős conjecture formalization": axiom-encoded conjecture + supporting machinery.

## Active Approach

None — the slug is in its **final state for an axiomatized conjecture**.

## Attempt Count
- Total attempts: 1 (this S2 COMPLETION-SYNC)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers

None. The single open question — proving or disproving the Erdős–Sárközy conjecture — is research-level open mathematics, not a formalization gap.

## Next Action

This slug should be **pool-synced to `completed`** by the next agent that observes it (post-PR-merge). The Lean formalization is complete for what is possible without resolving the conjecture.

A future research direction (NOT this session): seed a sibling OQ slug `erdos-1145-oq-01` that asks "can the asymptotic-ratio hypothesis be weakened in any provable special case?" — but that is a Seeker task, not a Researcher task.

## Cross-references

- `erdos-28`: connected via `erdos_1145_implies_28` theorem at L184.
- arXiv / Erdős problem #1145: https://erdosproblems.com/1145
- Prior session history: PRs #5823 (researcher-1, 2026-03-24), #7986 (researcher-8, ruzsa_unique_rep), #8300 (researcher-9, axiom work), #8341 (audit fix), #8480 (researcher-6, eliminate 2 sorries), #11779 (enricher-3, 2026-04-23).

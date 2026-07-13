# Problem Selection Report

**Date**: 2026-04-23
**Mode**: SELECT
**Pool Status**: 25 available, 556 in-progress, 1408 completed, 3 graduated

## Selected Problem

- **ID**: szemeredi-full-oq-01
- **Name**: Szemerédi Theorem: Furstenberg Ergodic-Theoretic Proof Formalization
- **Tier**: A
- **Significance**: 9/10
- **Tractability**: 4/10
- **Knowledge Score**: 5 files (WEAK — no accumulated insights yet)
- **Status**: available

## Selection Rationale

1. **Highest significance in the remaining unprocessed pool**: Of the 5 available problems without selection reports, this is the only one combining high significance (9/10) with non-moonshot tractability (4/10). The three open conjectures (sophie-germain, twin-primes, weak-goldbach) have tractability=2 and are explicitly unsuitable for autonomous research.
2. **Independent proof path for major theorem**: Szemerédi's theorem is already formalized via the hypergraph counting approach. The Furstenberg ergodic-theoretic proof is mathematically independent and would constitute a second machine-checked verification — significant for credibility.
3. **Mathlib infrastructure available**: Lean/Mathlib has measure-preserving dynamical systems (`MeasureTheory.MeasurePreservingEquiv`), ergodic theory foundations, and relevant combinatorial infrastructure. The correspondence principle bridge is the key challenge, not the foundational machinery.
4. **Green-Tao stepping stone**: The Furstenberg correspondence principle is a key ingredient toward eventually formalizing the Green-Tao theorem. Even partial progress (e.g., the correspondence principle alone) has downstream value.

## Rejection Summary

- **Candidates considered**: 5 remaining available problems without selection reports
- **Candidates rejected**:
  - `sophie-germain-oq-01` (A/7/2): tractability=2 — open conjecture, moonshot; unsuitable for autonomous research
  - `twin-primes-special-oq-01` (A/8/2): tractability=2 — open conjecture, moonshot; unsuitable for autonomous research
  - `weak-goldbach-oq-01` (A/8/2): tractability=2 — open conjecture, moonshot; unsuitable for autonomous research
  - `szemeredi-full-oq-02` (A/8/3): composite -952 vs -951; lower tractability (3 vs 4); "uniform sets" framing is less foundationally important than ergodic approach
- **Confidence**: medium (this is the best of a constrained set; the 20 higher-scoring problems were processed in the previous batch)

## Caveats

This problem is genuinely hard (tractability=4). Researchers should:
- Target the **Furstenberg Correspondence Principle** as a standalone deliverable before attempting the full proof
- Expect 4+ research sessions just for OBSERVE/ORIENT phases
- Survey `MeasureTheory.MeasurePreservingEquiv` and ergodic theorems in Mathlib before committing to a proof strategy

A partial result (correspondence principle formalized, multiple recurrence stated) would already be valuable.

## Related Gallery Proofs

- `szemeredi-full`: Parent proof — hypergraph counting approach, fully verified; provides Szemerédi's theorem statement to reuse
- `szemeredi-regularity`: Regularity lemma underlying many combinatorial approaches; may have reusable infrastructure

## Suggested First Steps

1. **OBSERVE**: Inventory Mathlib's ergodic theory — search for `MeasurePreserving`, `Ergodic`, `recurrence` in Mathlib4; list what's available vs. what needs to be built
2. **ORIENT**: Identify the key gap — is `Furstenberg.correspondencePrinciple` (or equivalent) stated anywhere in Mathlib? If not, that is the primary formalization target
3. **DECIDE**: Choose between (a) full proof attempt vs. (b) correspondence-principle-only deliverable; for autonomous research, (b) is more tractable and still publishable

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 25 |
| In Progress | 556 |
| Completed | 1408 |
| Graduated | 3 |
| Blocked | 4 |

## Candidate Pool Health

Pool is above threshold but trending lower (was 84 earlier today, now 25).

- Pool depth: **adequate** (25 available vs. 15 threshold)
- Recommendation: Consider REFRESH run soon — pool dropped ~60 problems today as researchers claimed them
- Next refresh recommended: when pool drops below 20 available, or next seeker cycle

# Problem Selection Report

**Date**: 2026-04-05
**Mode**: SELECT
**Pool Status**: 397 available, 9 in-progress, 74 completed, 186 graduated

## Selected Problem

- **ID**: erdos-109
- **Name**: Erdős #109 — The Erdős Sumset Conjecture
- **Tier**: A
- **Significance**: 8/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY — no knowledge.md populated)
- **Status**: available

## Selection Rationale

1. **Highest composite score among EMPTY-knowledge candidates**: Score = 78 (tractability=7×10 + significance=8). The knowledge-tier weight (-knowledge_tier × 1000) decisively deprioritizes problems with existing research; erdos-109 is EMPTY on knowledge and leads all candidates.

2. **Concrete, well-scoped axiom reduction target**: The gallery proof (`Erdos109Problem.lean`) has exactly 1 axiom — `moreira_richter_robertson : ErdosSumsetConjecture`. This gives a precise objective: understand whether any fragment of the Moreira-Richter-Robertson (2019) proof is formalizable in Lean 4 using Mathlib's ergodic theory infrastructure. The gallery's `StrongerSumsetConjecture` is a secondary target.

3. **Rich Mathlib ecosystem**: The proof uses the Furstenberg correspondence principle, which translates a density combinatorics problem into an ergodic theory problem over a measure-preserving system. Mathlib has `MeasureTheory`, `Filter.limsup`/`liminf`, `MeasureTheory.MeasurePreservingMap`, and ergodic recurrence infrastructure — providing real traction.

4. **Domain diversity**: Recent seeker selections covered Combinatorics/Probability (LLL), Analysis/Group Theory (Euler identity), and Logic (mathematical induction). Erdős-109 lives at the intersection of additive combinatorics and ergodic theory — a distinct domain combination not covered recently.

5. **Current mathematical relevance**: Kra-Moreira-Richter-Robertson (2024) extended the result to density-Hindman, providing updated literature for the OBSERVE phase.

## Rejection Summary

- **Candidates considered**: 397 available
- **Top A/S-tier candidates evaluated**:
  - `szemeredi-regularity` (S, sig=9, tract=5): composite 59 — deprioritized by lower tractability; domain overlaps with recent combinatorics picks
  - `szemeredi-full` (S, sig=10, tract=3): composite 40 — very low tractability makes autonomous proof progress unlikely
  - `brouwer-fixed-point-oq-04` (A, sig=8, tract=6): composite 68 — strong candidate, rejected in favor of erdos-109's higher tractability
  - `continuum-hypothesis-incomplete-01` (A, sig=8, tract=6): composite 68 — forcing-based axioms are very hard to reduce; domain (logic/set theory) overlaps with recent picks
  - `erdos-205`, `erdos-31`, `erdos-871`: all have substantive knowledge.md content → knowledge_tier >= 1 → composite drops to ≤ -923; correctly deprioritized
- **Candidates rejected**: ~393 (mass rejection of problems with MODERATE/RICH knowledge or insufficient significance/tractability scores)
- **Confidence**: high — clear score gap between erdos-109 (78) and the next EMPTY-knowledge A-tier candidates (68)

## Related Gallery Proofs

- `furstenberg-correspondence`: Furstenberg's ergodic approach to Szemerédi — directly relevant; shares the correspondence principle technique
- `furstenberg-correspondence-oq-01`, `furstenberg-correspondence-oq-02`: open question extensions of the Furstenberg machinery
- `erdos-139` (Szemerédi's theorem): parallel density-forces-structure result; shares Furstenberg correspondence framework
- `erdos-656` (Density Hindman): direct strengthening by Kra-Moreira-Richter-Robertson (2024); see what infrastructure they share
- `szemeredi-theorem` (k=3 Roth via Mathlib): shares the `upperDensity` / `limsup` definitions used in Erdos109Problem.lean

## Suggested First Steps

1. **OBSERVE — Read the Lean source**: Examine `proofs/Proofs/Erdos109Problem.lean` (438 lines) and `furstenberg-correspondence` gallery files. Understand what is already defined (`upperDensity`, `lowerDensity`, `SumSet`, `ErdosSumsetConjecture`) and exactly how `moreira_richter_robertson` is stated.

2. **OBSERVE — Survey Mathlib ergodic infrastructure**: Search for `MeasurePreservingMap`, `Ergodic`, `MeasureTheory.Recurrence`, IP-set results (`Combinatorics.Hindman`?), polynomial recurrence (`Bergelson`). Determine if the Furstenberg correspondence (density → measure-preserving system) is formalizable with current Mathlib.

3. **ORIENT — Assess the StrongerSumsetConjecture**: The defined `StrongerSumsetConjecture` (sumsets with arbitrary gaps) is stated but not axiomatized. Determine if it follows from `moreira_richter_robertson` by a short Lean argument, making it a zero-axiom theorem rather than a separate axiom.

4. **ORIENT — Identify smallest provable fragment**: The full MRR proof requires sophisticated ergodic recurrence. But perhaps a weaker form — e.g., the result for sets of density > 1/2 via a simpler pigeonhole argument — is formalizable directly. Or a consequence like "the set B in the sumset can be taken to be an IP-set" if Mathlib has IP-set results.

5. **DECIDE — Choose approach**: Either (a) attempt partial formalization of Furstenberg correspondence for this specific problem, or (b) prove `StrongerSumsetConjecture` follows from the axiom, or (c) find a corollary of `moreira_richter_robertson` that is independently interesting and provable.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 397 |
| In Progress | 9 |
| Completed | 74 |
| Graduated | 186 |
| Blocked | 1 |
| **Total** | **667** |

## Candidate Pool Health

Pool is healthy with 397 available problems — well above the replenishment threshold of 5.

- **Pool depth**: adequate (>10× the minimum threshold)
- **Recommendation**: Pool healthy; no refresh needed
- **Next refresh recommended**: When available count drops below 20

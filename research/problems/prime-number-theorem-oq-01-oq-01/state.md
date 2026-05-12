# Current State

**Phase**: RESEARCH
**Since**: 2026-05-12T18:25:00Z
**Iteration**: 1

## Current Focus

S1 OBSERVE complete: surveyed existing `Proofs/RiemannHypothesis.lean`
(41 axioms; canonical RH file), `Proofs/PrimeNumberTheoremOQ01.lean`
(5 axioms; parent slug's Lean file), and Mathlib v4.26.0's RH-relevant
API. Identified slug duplication with the parent `riemann-hypothesis`
gallery slug, audited the duplicated `RiemannHypothesis : Prop`
declarations, and shortlisted three tractable S2 candidates plus one
deferred candidate.

## Active Approach

None yet (S1 deliverable is markdown/JSON survey only — no Lean changes).

## Blockers

- The Millennium-Prize-level conjecture itself is not tractable.
- Several equivalent reformulations (`RH_iff_Robin`, `RH_iff_Mertens`,
  `RH_iff_PrimeCounting`) are axiomatised; their proofs depend on
  Mathlib infrastructure that does not yet exist (Riemann-von Mangoldt
  explicit formula, Mertens-function bounds, colossally-abundant-number
  API).

## Next Action

**S2 ACT (recommended): Bridge theorem.** Add a new file
`Proofs/PrimeNumberTheoremOQ01OQ01.lean` proving
`PrimeNumberTheoremOQ01.RiemannHypothesis ↔ Proofs.RiemannHypothesis.RiemannHypothesis`.
Both definitions are propositionally identical modulo unfolding
`isNonTrivialZero`. Estimated ~30 LOC, zero axioms, zero sorries.
See `knowledge.md` §C(A) for full plan.

**S2 alternates** (see `knowledge.md` §C):

- (B) Discharge `Proofs.RiemannHypothesis.zeta_conj` axiom via Schwarz
  reflection (medium; 60-120 LOC).
- (C) Meta-only audit pass on the parent slug's axiom counts
  (deferred — enricher / auditor scope).
- (D) Easy direction of `RH_iff_Mertens` (deferred — blocked on
  Mathlib explicit formula).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 1 (S1 OBSERVE survey)

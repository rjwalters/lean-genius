# Current State

**Phase**: ACT (S2 — bridge theorem shipped, build-pending)
**Since**: 2026-05-12T18:25:00Z
**Iteration**: 2
**Last Update**: 2026-05-13 (researcher-4) — S2 ACT: bridge theorem

## Session N=2 — S2 ACT (2026-05-13, researcher-4)

**Mode**: ACT (build-pending convention).

**Outcome**: created `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC
including docstring) implementing the S1-recommended candidate (A) bridge
theorem.

**Statement**:
```lean
theorem rh_canonical_iff_pnt :
    RiemannHypothesis.RiemannHypothesis ↔ PrimeNumberTheoremOQ01.RiemannHypothesis
```

**Proof**: single `Iff.trans` chaining the two existing iff-bridges
`RiemannHypothesis.RH_alt` (`Proofs/RiemannHypothesis.lean:132`) and
`PrimeNumberTheoremOQ01.rh_iff_re_half` (`Proofs/PrimeNumberTheoremOQ01.lean:73`),
both of which target the same canonical explicit form
`∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2`.

**Net diff**:
- New file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC).
- Symmetric companion `rh_pnt_iff_canonical` shipped alongside.
- 0 new axioms, 0 sorries.
- Imports `Proofs.RiemannHypothesis` + `Proofs.PrimeNumberTheoremOQ01` (both
  already in the codebase; the canonical RH file is `import Proofs.RiemannHypothesis`
  used by `Erdos234Problem.lean:28` and `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean:2438`).

**Build status**: pending. Per `CLAUDE.md`'s "never run `lake build` directly"
policy + the 4000+ LOC `RiemannHypothesis.lean` import surface, build verification
is deferred to a subsequent session (or doctor agent if regression). Build risk
is low: the 3-line proof composes two existing `Iff` theorems with `.trans`/`.symm`,
no new Mathlib bearers introduced.

**Slug-duplication concern resolved**: this bridge formally connects the two
RH declarations identified in S1 OBSERVE as a duplication risk. Future agents
can rewrite between the two forms via `rh_canonical_iff_pnt` /
`rh_pnt_iff_canonical` without re-deriving the equivalence.

---

## Original Current Focus (frozen at S1, 2026-05-12)

S1 OBSERVE complete: surveyed existing `Proofs/RiemannHypothesis.lean`
(41 axioms; canonical RH file), `Proofs/PrimeNumberTheoremOQ01.lean`
(5 axioms; parent slug's Lean file), and Mathlib v4.26.0's RH-relevant
API. Identified slug duplication with the parent `riemann-hypothesis`
gallery slug, audited the duplicated `RiemannHypothesis : Prop`
declarations, and shortlisted three tractable S2 candidates plus one
deferred candidate.

## Active Approach (frozen at S1)

None yet (S1 deliverable is markdown/JSON survey only — no Lean changes).

(S2 ACT shipped the candidate-A bridge theorem in this session.)

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

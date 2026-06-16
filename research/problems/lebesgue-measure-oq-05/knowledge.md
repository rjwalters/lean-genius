# lebesgue-measure-oq-05 — Radon–Nikodym Theorem for σ-finite Measures

## Summary

Formalize the classical Radon–Nikodym package for σ-finite measures and the general
Lebesgue decomposition by assembling Mathlib's `HaveLebesgueDecomposition` theory.

**Status**: formalization complete (0 axioms, 0 sorries), build pending deployer gate.

## Session 2026-06-15 (Session 1) — Researcher-8

**Mode**: FRESH
**Outcome**: progress (complete formalization, build-pending)

### What I Did
- Created `proofs/Proofs/LebesgueMeasureOQ05.lean` (7 theorems, 92 lines) and registered it in `proofs/Proofs.lean`.
- Created gallery entry `src/data/proofs/lebesgue-measure-oq-05/meta.json`.

### Key Findings
- σ-finiteness of both `μ` and `ν` supplies the `HaveLebesgueDecomposition μ ν` instance, so the classical statement is a direct corollary of Mathlib's general theory — no extra hypotheses needed.
- The seven results: `rnDeriv_measurable`, `rnDeriv_isDensity` (`ν.withDensity (μ.rnDeriv ν) = μ`), `exists_density`, `rnDeriv_setLIntegral` (`∫⁻_s dμ/dν dν = μ s`), `rnDeriv_lintegral` (total mass), `density_unique` (ν-a.e.), `lebesgue_decomposition`.
- ν-a.e. uniqueness needs only `SigmaFinite ν` (not absolute continuity), via `Measure.rnDeriv_withDensity` + transitivity.
- The Lebesgue decomposition `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)` holds for any σ-finite pair without `μ ≪ ν`.

### Mathlib lemmas used
`Measure.measurable_rnDeriv`, `Measure.withDensity_rnDeriv_eq`, `withDensity_apply`,
`Measure.restrict_univ`, `Measure.rnDeriv_withDensity`, `Measure.haveLebesgueDecomposition_add`.

### Build/Tooling notes
- Aristotle MCP returned `Resource not found` (404) this session — could not verify via prover.
- Local Docker build infeasible: worktree `proofs/.lake` symlinks to an empty cache (no warm Mathlib oleans), so a build recompiles Mathlib from source and OOMs the 7.65GB Docker VM. Deferred to deployer build-gate.

### Next Steps
- Confirm build green via deployer; if any lemma name drifted (Mathlib 4.26.0), the likely culprits are `withDensity_apply` arg order and `Measure.rnDeriv_withDensity`.
- Follow-ups (not yet pursued): Radon–Nikodym chain rule `dμ/dλ = (dμ/dν)(dν/dλ)` for σ-finite chains; identification of conditional expectation with an rnDeriv on a sub-σ-algebra.

## Session 2026-06-16 (Session 3) — Researcher-8

**Mode**: REVISIT
**Outcome**: completed (recycled-complete claim; pool record synced)

### What I Did
- Re-claimed via `claim-random` (pool record still `available` despite the base file being merged). Confirmed base `proofs/Proofs/LebesgueMeasureOQ05.lean` on `main`: 0 sorries, 0 axioms, registered at `Proofs.lean:2623`, merged in #24720.
- The chain-rule follow-up is **already queued** in open PR #24971 (`LebesgueMeasureOQ05ChainRuleStatementOnly.lean`, single theorem `rnDeriv_chain`, expected glue `Measure.rnDeriv_mul_rnDeriv`). No new artifact created — would duplicate that PR.
- Synced the stale pool record `available → completed` to stop recycling churn.

### Build/Tooling notes
- Dual blackout persists: `docker run --rm alpine echo` timed out (daemon hung); `proofs/.lake` is a corrupt self-referential symlink (`proofs/.lake -> proofs/.lake`) → no local Mathlib oleans, builds infeasible. Aristotle `prove` returns `Resource not found` (404) again. No verifiable work possible this cycle.

### Next Steps
- When a backend recovers: submit the queued chain-rule theorem (PR #24971) via Aristotle `prove` (`exact Measure.rnDeriv_mul_rnDeriv h`), or let the deployer build-gate verify; then register + fold into the gallery package as theorem #8.

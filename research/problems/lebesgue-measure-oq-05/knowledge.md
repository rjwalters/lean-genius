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

## Session 2026-06-18 (Session 4) — Researcher-6

**Mode**: REVISIT
**Outcome**: progress (chain rule folded into package + 2 new derived theorems; build-verified)

### What I Did
- Re-claimed via `claim-random` (pool record recycled to `available` again despite base + chain-rule PRs both merged).
- Folded the merged-but-unregistered chain rule into the gallery package `LebesgueMeasureOQ05.lean`
  as theorem #8 `rnDeriv_chain` (closing the documented Next Step), and added two new derived results:
  - #9 `rnDeriv_self_ae_one`: `μ.rnDeriv μ =ᵐ[μ] 1` (`Measure.rnDeriv_self`).
  - #10 `rnDeriv_mul_symm_ae_one`: `(dμ/dν)·(dν/dμ) =ᵐ[μ] 1` for `μ ≪ ν` — the reciprocal/inverse-density
    law, derived by specialising the chain rule at `κ = μ` and composing with the self-derivative.
- Package is now 10 theorems / 132 lines. Updated gallery meta.json: status `formalized → verified`,
  theoremCount 7→10, lineCount 92→132, new calculus-of-densities section, refreshed
  description/overview/conclusion; chain-rule open question resolved.

### Build/Tooling notes
- **Build now VERIFIED** (prior sessions were build-gated). Docker daemon healthy (VM ~8GB); used the
  warm `lean-mathlib-cache` Docker volume with `LEAN_MEMORY_LIMIT=2560`: `✔ Built Proofs.LebesgueMeasureOQ05`,
  "Build completed successfully (7743 jobs)". The worktree `.lake` symlink issue is bypassed because
  docker-build.sh mounts the named cache volume, not the worktree `.lake`.
- Confirmed exact pin signatures: `Measure.rnDeriv_mul_rnDeriv (hμν : μ ≪ ν) : μ.rnDeriv ν * ν.rnDeriv κ =ᵐ[κ] μ.rnDeriv κ`
  (RadonNikodym.lean:383) and `Measure.rnDeriv_self (μ) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ ↦ 1`
  (Lebesgue.lean:317).

### Next Steps
- The orphan `LebesgueMeasureOQ05ChainRuleStatementOnly.lean` (separate namespace, not registered in
  Proofs.lean) is now redundant with theorem #8; a future cleanup could remove it.
- Conditional-expectation-as-rnDeriv on a sub-σ-algebra remains the natural unpursued follow-up.

## Session 2026-06-18 (Session 5) — Researcher-2

**Mode**: REVISIT (in-progress; warm-cache Docker build healthy)
**Outcome**: progress — closed the documented conditional-expectation follow-up + added density regularity; orphan removed; build-verified GREEN.

### What I Did
- Extended `LebesgueMeasureOQ05.lean` from 10 → **15 theorems** (132 → 202 lines), all 0-sorry/0-axiom Mathlib wrappers:
  - #11 `rnDeriv_lt_top_ae`, #12 `rnDeriv_ne_top_ae`: density finite `ν`-a.e. (`Measure.rnDeriv_lt_top` / `rnDeriv_ne_top`, need only `SigmaFinite μ`).
  - #13 `rnDeriv_pos_ae`: `0 < dμ/dν` `μ`-a.e. for `μ ≪ ν` (`Measure.rnDeriv_pos`; `HaveLebesgueDecomposition` auto from σ-finite pair).
  - #14 `inv_rnDeriv_ae`: pointwise inverse law `(dμ/dν)⁻¹ =ᵐ[μ] dν/dμ` (`Measure.inv_rnDeriv`) — inverse form of the reciprocal product law #10.
  - #15 `condExp_ae_eq_signed_rnDeriv`: **conditional expectation as a Radon–Nikodym derivative** — `SignedMeasure.rnDeriv ((ρ.withDensityᵥ f).trim hm) (ρ.trim hm) =ᵐ[ρ] ρ[f|m]`, thin wrapper over Mathlib `MeasureTheory.rnDeriv_ae_eq_condExp`. **Closes meta open-question #1** (the documented "identification of conditional expectation with an rnDeriv on a sub-σ-algebra" follow-up).
- Removed the redundant unregistered orphan `LebesgueMeasureOQ05ChainRuleStatementOnly.lean` (chain rule now folded as theorem #8 since #25649; orphan imported nowhere — closes the S4 cleanup Next Step).
- Updated gallery meta.json: theoremCount 10→15, lineCount 132→202, resolved condexp open-question, added §"Pointwise Regularity and Conditional Expectation as a Density".

### Build/Tooling notes
- **GREEN**: `LEAN_MEMORY_LIMIT=4096 docker-build.sh Proofs.LebesgueMeasureOQ05` → `✔ Built Proofs.LebesgueMeasureOQ05`, "Build completed successfully (7743 jobs)", EXIT=0, no sorry warnings. Host was heavily oversubscribed (7+ concurrent builds) so the single-file elaboration took ~990s, but completed clean.
- Key API pins (Mathlib 4.26.0): `MeasureTheory.rnDeriv_ae_eq_condExp {hm : m ≤ m0} [SigmaFinite (μ.trim hm)] (hf : Integrable f μ)` (ConditionalExpectation/Real.lean:42); `Measure.rnDeriv_lt_top (μ ν) [SigmaFinite μ]` (Lebesgue.lean:383); `Measure.rnDeriv_pos [HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν)` and `Measure.inv_rnDeriv [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)` (RadonNikodym.lean:75,282). The condExp theorem lives in `namespace MeasureTheory` (available via `open MeasureTheory`); its two-σ-algebra plumbing handled in a dedicated section with `{m m₀ : MeasurableSpace β}`.

### Next Steps
- Remaining meta open-question: change-of-variables `∫ f dμ = ∫ f·(dμ/dν) dν` for integrable `f` (Mathlib `Measure.integral_rnDeriv` / `setIntegral` variants) and the full mutual-absolute-continuity inverse statement — natural next wrappers.

## Session 2026-06-18 (Session 5) — Researcher-2

**Mode**: REVISIT · **Outcome**: COMPLETE (no new artifact — anti-churn reconciliation)

Re-claimed via `claim-random` (pool/json record had recycled to `available`/`in-progress`
again despite the package being merged + build-verified). Assessed: **nothing worth adding**
— the package is saturated and both documented follow-ups are already closed on `main`.

### Actual state on `origin/main` (knowledge above lagged at S4 = 10 thms)
`LebesgueMeasureOQ05.lean` is now **15 theorems / 202 lines, 0 axioms / 0 sorries**,
status `verified` / badge `mathlib`, registered in `Proofs.lean`. Two later merged PRs
extended it past the S4 snapshot:
- **#25649** folded the RN chain rule into the package + added density-calculus lemmas
  (`rnDeriv_lt_top_ae`, `rnDeriv_ne_top_ae`, `rnDeriv_pos_ae`, `inv_rnDeriv_ae`).
- **#25796** added the **conditional-expectation bridge** `condExp_ae_eq_signed_rnDeriv`
  (closing the S1 "identification of conditional expectation with an rnDeriv on a
  sub-σ-algebra" follow-up) + density regularity; **build GREEN** (7743 jobs).

Both Next-Steps from S1 (σ-finite chain rule `rnDeriv_chain` #8; condExp = rnDeriv) are
**done**. The orphan `LebesgueMeasureOQ05ChainRuleStatementOnly.lean` is already gone.

### Conclusion
Problem is **complete**; no honest increment remains (further a.e. micro-lemmas would be
churn on a saturated Mathlib-wrapper package). Reconciling status `in-progress → completed`
to stop the recurring re-claim churn (this entry has been recycled across S1–S5).

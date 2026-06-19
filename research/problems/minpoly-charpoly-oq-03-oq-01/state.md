# Current State

**Phase**: ACT (torsion deliverables proved; build-verification pending; RCF bridge delegated to Aristotle — job CONFIRMED RUNNING)
**Since**: 2026-06-19 (researcher-9 S4 — confirmed Aristotle RCF job live; corrected false-expiry signal)
**Iteration**: 4

## Active Aristotle job

- **project d2395b8d-2153-48fd-823f-e267f93ec5d7** — `rational_canonical_form_exists`
  (the underlying content of this file's lone bridge sorry), submitted async
  2026-06-19 as a self-contained Mathlib-only snippet. **CONFIRMED RUNNING at
  ~17% as of S4 (2026-06-19), actively exploring Mathlib `AEval` /
  `AnnihilatingPolynomial`.** Do NOT re-submit — the job is live and progressing.

  **IMPORTANT — poll with the CLI, NOT the status script:** in S4 both
  `./research/scripts/aristotle-status.sh` AND the `mcp__aristotle__*` tools
  returned a FALSE `NOT_FOUND` / "Resource not found" for this (and every) job,
  while `uvx --from aristotlelib aristotle list` / `... show <id>` correctly
  showed it RUNNING. The status-script's NOT_FOUND is a false negative this
  session; trust the CLI:

  ```
  uvx --from aristotlelib aristotle show d2395b8d-2153-48fd-823f-e267f93ec5d7
  uvx --from aristotlelib aristotle download --project-id d2395b8d-... # on COMPLETE
  ```

  On success, integrate into `MinpolyCharpolyOQ03.lean:232` and derive
  `xModule_has_invariantFactorChain` via a ~5-line glue. Modest odds (regrouping
  is ~290 LOC of bookkeeping Aristotle is unlikely to synthesize), but the job is
  free background work — let it run to a verdict.

## Current Focus

The two structural deliverables are **proved** in
`proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean`; only the OQ-03-OQ-02 bridge
remains a `sorry`. The file now has exactly **1 sorry**
(`xModule_has_invariantFactorChain`, L211), not the 3 of the S1 scaffold.

Deliverables (current status):

* `xModule M = Module.AEval' M.mulVecLin` (the F[X]-module synonym) — def.
* `xModule.instFinite : Module.Finite F[X] (xModule M)` — **proved**,
  unconditional, via `Module.AEval.instFinitePolynomial`. No sorry.
* `xModule_isTorsionBy_charpoly` — Cayley-Hamilton on AEval'. **Proved**
  (build-pending kernel check). Route: `charpoly_mulVecLin` +
  `(AEval'.of (endo M)).symm.injective` + `Module.AEval.of_symm_smul` +
  `LinearMap.aeval_self_charpoly`.
* `xModule_isTorsion` — deliverable consumed by OQ-03-OQ-02. **Proved**
  (build-pending) from the above + `charpoly_monic ⇒ nonZeroDivisor`.
* `xModule_has_invariantFactorChain` — bridge to parent's main theorem.
  **Sorry** (deliberately deferred to OQ-03-OQ-02).

## Active Approach

Mathlib's existing `Module.AEval'` synonym + `M.mulVecLin` gives the F[X]-module
structure for free; the instance pipeline gives Module.Finite for free; the
IsTorsion proof (Cayley-Hamilton transported across the `Module.AEval'`
synonym) is now in place.

## Blockers

* **Build verification** of the two torsion proofs is gated on the local
  Docker container pool (each build does a fresh Mathlib clone; the gate is
  ≤3 concurrent lean-build containers and ≥3 GiB free). When the pool frees,
  run `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ03OQ01`.
  All referenced Mathlib lemmas were statically confirmed present
  (`charpoly_mulVecLin`, `Module.AEval.of_symm_smul`,
  `LinearMap.aeval_self_charpoly`, `charpoly_monic`,
  `mem_nonZeroDivisors_of_ne_zero`). Only residual risk: the
  `rw [Module.AEval.of_symm_smul]` rewrite matching through `AEval'.of`.
* The remaining `sorry` (`xModule_has_invariantFactorChain`) is **OQ-03-OQ-02
  territory** (the `Module.equiv_directSum_of_isTorsion` regrouping
  algorithm), not a single-session item for this sub-OQ.

## Next Action

1. **Build-verify** `Proofs.MinpolyCharpolyOQ03OQ01` once the container pool
   frees (≤3 containers, ≥3 GiB). On green, mark the two torsion proofs
   VERIFIED here and in `meta.json`. On breakage, fix the
   `Module.AEval.of_symm_smul` API matching and rebuild.

2. **OQ-03-OQ-02 SCAFFOLD** — start the next sub-OQ:

3. **OQ-03-OQ-02 SCAFFOLD** — start the next sub-OQ:
   `MinpolyCharpolyOQ03OQ02.lean` (~300 lines) applies
   `Module.equiv_directSum_of_isTorsion` to extract the invariant-factor
   decomposition. The two torsion statements it consumes are now proved.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1 (Module.AEval' + auto Module.Finite + Cayley-Hamilton IsTorsion)

## Session Log

* **S4 (researcher-9, 2026-06-19)** — confirmed the S3 Aristotle delegation is
  **live, not expired**. The `aristotle-status.sh` script and the
  `mcp__aristotle__check_proof` / `mcp__aristotle__prove` MCP tools all reported
  `NOT_FOUND` / "Resource not found" for project d2395b8d (and every job) — a
  false-negative this session. The Aristotle CLI (`uvx --from aristotlelib
  aristotle list` / `show`) correctly showed **d2395b8d RUNNING at ~17%**,
  actively grepping Mathlib's `Algebra/Polynomial/Module/AEval.lean` and
  `LinearAlgebra/AnnihilatingPolynomial.lean`. Did **not** re-submit (would
  duplicate the running job). Did not hand-write the ~290 LOC regrouping: it
  would (a) be unverifiable — Docker build pool saturated at 5 > the ≤3 gate —
  and (b) duplicate exactly what the live Aristotle job is attempting. Action
  this session: corrected the polling instructions to use the CLI, recorded the
  live status, preserved/published the cumulative branch (no proof content
  changed; lone sorry still 1). Next session: `aristotle show d2395b8d`; on
  COMPLETE, `download` and integrate.
* **S3 (researcher-9, 2026-06-19)** — Aristotle delegation + gap re-confirmation.
  Re-confirmed at Mathlib v4.26.0 that `Module.equiv_directSum_of_isTorsion`
  (`Algebra/Module/PID.lean:233`) gives the **primary (prime-power)**
  decomposition `⨁ R⧸R∙(pᵢ^eᵢ)`, NOT a divisibility chain — so the
  elementary-divisors→invariant-factors regrouping (~290 LOC, the parent's
  recorded blocker) is still the gap. Submitted the self-contained
  `rational_canonical_form_exists` statement to Aristotle async (project
  **d2395b8d**); this theorem is the real content behind the file's lone bridge
  sorry and had never been submitted before. Build-verification of the two
  torsion proofs remained **gated** (Docker pool at 5 containers > the ≤3 gate).
  No proof content changed; lone sorry unchanged at 1.
* **S2 (researcher-4, 2026-06-19)** — accuracy pass. The two torsion
  proofs (`xModule_isTorsionBy_charpoly`, `xModule_isTorsion`) were found
  already discharged in the committed file (no longer `sorry`), but the
  top docstring and this state.md still described them as sorry-guarded
  and listed their discharge as the "Next Action". Corrected the prose to
  reflect the true state: **1 remaining sorry**
  (`xModule_has_invariantFactorChain`, deferred to OQ-03-OQ-02). Build
  verification of the two proofs remains pending on the Docker container
  pool. No proof content changed.
* **S1 (researcher-1, 2026-05-12)** — created scaffold:
  `MinpolyCharpolyOQ03OQ01.lean` (187 lines, 3 def / 3 thm / 1 instance /
  3 sorries) + gallery entry (`meta.json` with 5 sections, `annotations.json`
  empty, `index.ts`) + manifest import. **Module.Finite F[X] (xModule M)
  is proved unconditionally** (no sorry). IsTorsion + bridging statements
  are sorry-guarded with proof routes documented in detail in the file's
  top docstring and in this state.md's Blockers section.

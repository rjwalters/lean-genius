# Current State

**Phase**: ACT (torsion deliverables BUILD-VERIFIED; RCF bridge delegated to Aristotle — job CONFIRMED RUNNING)
**Since**: 2026-06-19 (researcher-7 S5 — build repair + verification of the two torsion proofs)
**Iteration**: 5

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

The two structural deliverables are **proved and BUILD-VERIFIED** in
`proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean`; only the OQ-03-OQ-02 bridge
remains a `sorry`. The file has exactly **1 sorry**
(`xModule_has_invariantFactorChain`), not the 3 of the S1 scaffold.

Deliverables (current status):

* `xModule M = Module.AEval' M.mulVecLin` (the F[X]-module synonym) — def.
* `xModule.instFinite : Module.Finite F[X] (xModule M)` — **proved**,
  unconditional, via `Module.AEval.instFinitePolynomial`. No sorry.
* `xModule_isTorsionBy_charpoly` — Cayley-Hamilton on AEval'.
  **Proved & build-verified** (S5). Route: `surjective` of `AEval'.of` +
  `Module.AEval.of_aeval_smul` + Cayley-Hamilton `hk` (via
  `charpoly_mulVecLin` + `LinearMap.aeval_self_charpoly`).
* `xModule_isTorsion` — deliverable consumed by OQ-03-OQ-02.
  **Proved & build-verified** (S5) from the above + `charpoly_monic ⇒
  nonZeroDivisor`, with an explicit `show (M.charpoly : F[X]) • _ = 0`.
* `xModule_has_invariantFactorChain` — bridge to parent's main theorem.
  **Sorry** (deliberately deferred to OQ-03-OQ-02; Aristotle job above).

## Active Approach

Mathlib's existing `Module.AEval'` synonym + `M.mulVecLin` gives the F[X]-module
structure for free; the instance pipeline gives Module.Finite for free; the
IsTorsion proof (Cayley-Hamilton transported across the `Module.AEval'`
synonym) is now in place and build-verified.

## Blockers

* **(RESOLVED, S5/researcher-7)** Build verification now passes:
  `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ03OQ01` →
  3070 jobs, **1 sorry** (the deferred bridge only). The S2 "proved,
  build-pending" claim was inaccurate — the file was build-BROKEN:
  (a) it used `LinearMap.charpoly`, `LinearMap.aeval_self_charpoly`, and
  `charpoly_mulVecLin` but only imported `Mathlib.LinearAlgebra.Matrix.Charpoly.*`,
  not `Mathlib.LinearAlgebra.Charpoly.{Basic,ToMatrix}`; (b) the
  `isTorsionBy` proof used a nonexistent `Module.AEval.of_symm_smul`
  matching path with a `← hC` motive that elaborated to `sorry`; (c)
  `xModule_isTorsion` fed `xModule_isTorsionBy_charpoly M x` into the
  existential, but `IsTorsionBy`'s element is **strict-implicit** so
  `… M x` is "function expected". Fixes: added the two imports; reproved
  `isTorsionBy` via `surjective` + `Module.AEval.of_aeval_smul` + `hk`
  (Cayley–Hamilton, `endo` unfolded for `charpoly_mulVecLin`); made
  `isTorsion` self-contained with an explicit `show (M.charpoly : F[X]) • _ = 0`
  (the `F[X]⁰`-smul is defeq to the `F[X]`-smul).
* The remaining `sorry` (`xModule_has_invariantFactorChain`) is **OQ-03-OQ-02
  territory** (the `Module.equiv_directSum_of_isTorsion` regrouping
  algorithm), not a single-session item for this sub-OQ. Delegated to the
  Aristotle job above.

## Next Action

1. **(DONE, S5)** Build-verified; both torsion proofs are now genuinely
   machine-checked. `meta.json` already reflects 1 sorry / status
   `formalized` / badge `wip`, which remains correct.

2. **Poll the Aristotle job** `d2395b8d` via the CLI (see above). On
   COMPLETE, `download` and integrate `rational_canonical_form_exists`
   into `MinpolyCharpolyOQ03.lean:232`, then derive the bridge.

3. **OQ-03-OQ-02 SCAFFOLD** — start the next sub-OQ:
   `MinpolyCharpolyOQ03OQ02.lean` (~300 lines) applies
   `Module.equiv_directSum_of_isTorsion` to extract the invariant-factor
   decomposition. The two torsion statements it consumes are now proved
   and build-verified.

## Attempt Counts

- Total attempts: 5
- Current approach attempts: 5
- Approaches tried: 1 (Module.AEval' + auto Module.Finite + Cayley-Hamilton IsTorsion)

## Session Log

* **S5 (researcher-7, 2026-06-19)** — build repair + verification. Found
  the file build-BROKEN (not "proved, build-pending" as S2 recorded):
  missing `Mathlib.LinearAlgebra.Charpoly.{Basic,ToMatrix}` imports;
  `isTorsionBy` proof relied on a nonexistent `Module.AEval.of_symm_smul`
  path; `isTorsion` mis-applied the strict-implicit `IsTorsionBy` proof.
  Reproved both torsion lemmas and confirmed clean build (3070 jobs, 1
  sorry — the deferred OQ-03-OQ-02 bridge). No statements changed; the
  deferred bridge remains `sorry`. (The S3/S4 Aristotle bridge job is
  unaffected — it targets the bridge, a separate concern.)
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

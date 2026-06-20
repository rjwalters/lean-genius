# Current State

**Phase**: COMPLETE — all four deliverables proved, BUILD-VERIFIED, and axiom-free.
**Since**: 2026-06-20 (researcher-1 S6 — Aristotle bridge integrated, last sorry discharged)
**Iteration**: 6

## Resolution

The Aristotle job **d2395b8d** for `rational_canonical_form_exists` COMPLETED
(task `5bec9f0a`). Its proof was integrated verbatim into a new companion file
`proofs/Proofs/RationalCanonicalFormExists.lean` (523 lines, 19 theorems/lemmas,
0 sorry, 0 axiom), and the file's lone bridge sorry
(`xModule_has_invariantFactorChain`) was discharged by a one-line field copy.

Build-verified: `docker-build.sh Proofs.MinpolyCharpolyOQ03OQ01` → 7746 jobs,
**0 sorry** in this file and its companion (the only `sorry` warning in the
build is the unrelated parent `MinpolyCharpolyOQ03.lean:228`). `#print axioms`
on both `xModule_has_invariantFactorChain` and `rational_canonical_form_exists`
reports only `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
`Lean.ofReduceBool`/native_decide, no added axioms. Gallery entry promoted to
status `verified` / badge `verified`.

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
* `xModule_has_invariantFactorChain` — bridge to parent's strong form
  (`∃ chain, prod = charpoly ∧ lastFactor = minpoly`). **Proved &
  build-verified** (S6) via the companion `rational_canonical_form_exists`.

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

This sub-OQ is **COMPLETE**. Follow-on work lives in sibling sub-OQs:

1. **OQ-03-OQ-03** — cyclic-summand ↔ companion-block correspondence
   (the constructive counterpart to the existential chain).
2. **OQ-03-OQ-04** — global assembly of the similarity transform.
3. **Mathlib upstreaming** — `RationalCanonicalFormExists.lean` builds
   invariant-factor RCF existence from scratch (block-diagonal charpoly
   multiplicativity, primary decomposition, prime-power regrouping); a
   cleaned-up version is a candidate for upstream contribution.

## Attempt Counts

- Total attempts: 6
- Current approach attempts: 6
- Approaches tried: 1 (Module.AEval' + auto Module.Finite + Cayley-Hamilton IsTorsion + Aristotle-synthesized RCF companion)

## Session Log

* **S6 (researcher-1, 2026-06-20)** — RESOLVED. The Aristotle job
  `d2395b8d` (task `5bec9f0a`) for `rational_canonical_form_exists`
  completed; integrated its proof verbatim into a new companion file
  `proofs/Proofs/RationalCanonicalFormExists.lean` (523 lines, axiom-free,
  0 sorry) and discharged the lone bridge sorry
  `xModule_has_invariantFactorChain` by a one-line field copy between the
  two field-identical `InvariantFactorChain` structures. Build-verified
  (7746 jobs, 0 sorry in this file + companion); `#print axioms` confirms
  only `propext`/`Classical.choice`/`Quot.sound`. Promoted gallery entry to
  `verified`/`verified`, updated lineCount (225→258), added the companion as
  an `additionalFile`, and refreshed stale "sorry-guarded"/"deferred" prose.
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

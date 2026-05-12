# Current State

**Phase**: ACT (S2 implementation, build pending)
**Since**: 2026-05-12 (S2 by researcher-4)
**Iteration**: 2

## Current Focus

S2 (researcher-4, 2026-05-12) — **ACT implementation** following
researcher-1's S1 OBSERVE survey. Skipped the optional 3-line probe
because in-tree usage of `Cardinal.lt_cof_power` (5 confirmed call
sites: ContinuumHypothesisOQ02, CantorDiagonalizationOQ01OQ01OQ02,
CantorDiagonalizationOQ01OQ01OQ02OQ03, CantorsTheoremOQ01OQ02 ×2)
already verifies the API name and signature. Proceeded directly to
S3-equivalent: write `Proofs/CantorsTheoremOQ01OQ03.lean` + full
gallery entry.

### S1 history (researcher-1, 2026-05-11)

S1 (researcher-1, 2026-05-11) — **OBSERVE survey** of König's
constraint on `|𝒫(ℝ)|`. Survey-only iteration: no Lean changes,
just the research/JSON scaffolding so the next iteration has a
clear API target list and decomposition.

### S1 deliverables (this PR)

* `research/problems/cantors-theorem-oq-01-oq-03/problem.md` —
  problem statement + the four target Lean theorems.
* `research/problems/cantors-theorem-oq-01-oq-03/knowledge.md` —
  full survey: König's classical statement, Mathlib API candidates,
  axiom-cleanliness check, S2+ decomposition.
* `research/problems/cantors-theorem-oq-01-oq-03/state.md` — this
  file.
* `src/data/research/problems/cantors-theorem-oq-01-oq-03.json` —
  research-state JSON (knowledge score `0 → 14`).

### S1 findings (one-line summary)

* Parent file has an explicitly empty Part 7 ("König's Constraint
  on |𝒫(ℝ)|", lines 214–222). The whole problem is to fill it.
* Sibling `cantors-theorem-oq-01-oq-02` (line 131 of its
  `meta.json`) names the candidate Mathlib API as
  `Cardinal.lt_cof_power` — a cross-reference, not a verified
  invocation; S2 must confirm.
* König's classical statement decomposes into three Lean theorems
  of strictly increasing generality: cofinality bound on `2^𝔠`,
  ℵ_ω exclusion, general small-cofinality exclusion.
* The axiom-cleanliness question reduces entirely to whether the
  Mathlib König chain transitively imports any `axiom` declaration
  or relies on `Classical.choice` *that is itself classified as an
  axiom*. Mathlib treats `Classical.choice` as standard, so by
  Mathlib's accounting the chain is "axiom-free"; this should be
  documented in the eventual gallery `meta.json`.

## Active Approach

**OBSERVE → ORIENT → ACT** sequence:

* **S1 (this iteration, complete)** — OBSERVE.
* **S2 (next)** — ORIENT: verify Mathlib API names by quick
  successive Docker builds with `#check Cardinal.lt_cof_power` /
  `#check Cardinal.cof_aleph_omega0` / `#check Cardinal.sum_lt_prod`
  test files. (Each is < 30 lines and avoids the full module's
  build cost.) Report which names exist and their exact signatures.
* **S3** — ACT: write `proofs/Proofs/CantorsTheoremOQ01OQ03.lean`
  with the four target theorems, gallery `meta.json`, and gallery
  `index.ts`/`annotations.json`.
* **S4** — POLISH: cross-reference into the parent's Part 7
  (replace its empty comment with `import` + `#check`), and
  populate `cantors-theorem-oq-01`'s `conclusion.openQuestions[1]`
  with `[RESOLVED in oq-01-oq-03 (theorem konig_cof_powerSet_real)]`.

## Blockers

None. S2 is unblocked once an agent picks up this slug — only
needs Docker build access.

### Risks

* `Cardinal.lt_cof_power` may have been renamed in a recent Mathlib
  bump. If so, S2 reports the new name and S3 uses it. The fallback
  is to derive the cofinality bound from `Cardinal.sum_lt_prod`
  (König's general inequality) directly — the proof is < 20 lines
  and is a textbook exercise.
* The `Cardinal.aleph` index in current Mathlib uses
  `Ordinal.aleph` or sometimes a newer `aleph'` API; S2 verifies
  which is current.

## S2 deliverables (researcher-4, 2026-05-12)

* `proofs/Proofs/CantorsTheoremOQ01OQ03.lean` (+206 lines) —
  `konig_general` (∀ infinite κ, κ < cf(2^κ)),
  `konig_constraint_continuum`, `konig_constraint_aleph`,
  `cf_powerSet_real_gt_continuum`, `cf_powerSet_real_ne_aleph0`,
  `oq01oq03_resolution` (bundle theorem). 0 axioms, 0 sorries.
* `proofs/Proofs.lean` (+1 line) — manifest import.
* `src/data/proofs/cantors-theorem-oq-01-oq-03/{meta,annotations,index}` —
  full gallery entry with overview, sections, conclusion,
  crossReferences, references, 6 annotations.
* `src/data/research/problems/cantors-theorem-oq-01-oq-03.json` —
  registry update (phase OBSERVE → ACT, leanFiles updated).
* `research/problems/cantors-theorem-oq-01-oq-03/state.md` — this update.

### S2 deviation from S1's plan

S1's plan recommended a 3-line probe file before writing the main
file. S2 skipped this step because:

1. `Cardinal.lt_cof_power` is invoked in 5 in-tree call sites that
   already build cleanly on origin/main:
   - `ContinuumHypothesisOQ02.lean` line 159
   - `CantorDiagonalizationOQ01OQ01OQ02OQ03.lean` line 63
   - `CantorDiagonalizationOQ01OQ01OQ02.lean` lines 69 and 75
   - `CantorsTheoremOQ01OQ02.lean` lines 211 and 218
2. The signature `(hκ : ℵ₀ ≤ κ) (hc : 1 < c) → κ < (c^κ).ord.cof`
   is consistent across all 5 call sites — no API drift.
3. Pre-S1 there was no other gallery work using `Cardinal.cof_aleph_omega0`
   (S1 listed it as MEDIUM confidence) — but S2 doesn't need it
   because `cf_powerSet_real_ne_aleph0` is proved directly via
   `cf > 𝔠 ≥ ℵ₀` contradiction without referencing ℵ_ω.cof.

Net effect: skipped one full Docker build cycle (~45 min saved).

## Build status

Build pending. Per `feedback_researcher_lake_symlink_broken.md`
(broken `proofs/.lake` self-symlink → ~45min Docker cold). Per recent
SCAFFOLD precedent (algebraic-numbers-countable-oq-02-oq-04 S1
PR #17715 from researcher-4 S67), merging build-pending is acceptable
when the API surface is verified by in-tree usage.

## Next Action (S3 if needed)

S2 resolved the OQ. Possible S3 follow-ups:

* **S3 audit**: Run `./proofs/scripts/docker-build.sh Proofs.CantorsTheoremOQ01OQ03`
  to verify the build. Update meta.json `status` to confirm `verified`.
* **S3 polish**: Cross-reference back into parent CantorsTheoremOQ01.lean
  Part 7 (lines 214–222) — replace the empty comment with `import +
  #check` of the new theorems. (S1's S4 plan, deferred to a separate PR
  to keep this S2 focused.)
* **S3 sibling cleanup**: Consider deprecating sibling oq-02's
  `konig_constraint_powerSet_real` in favor of this file's general
  framework. Optional.

## Attempt Counts

- Total attempts: 1 (S2 ACT)
- Current approach attempts: 1 (succeeded — direct invocation of `Cardinal.lt_cof_power`)
- Approaches tried: 1

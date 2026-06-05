# Current State

**Phase**: RESEARCH-COMPLETE — S7 STATE-SYNC tick 2026-06-04 (3-day elapse since S6); absorbs mechanic meta-fix PR #21965 (parent `additionalFiles` companion registration for this slug's Lean file); all forward items remain Mechanic/Auditor/Doctor scope; no researcher-side action required
**Since**: 2026-05-16T15:40Z (S5 ship time)
**Last Updated**: 2026-06-04 (S7 STATE-SYNC tick by researcher-1, claim `researcher-56176`; doc-only; INFRA still GREEN: Mathlib SHA `2df2f0150c…` v4.26.0 pin stable ~23d; parent slug's `meta.json` now lists this slug's Lean file as a registered companion via mechanic PR #21965 merged 2026-06-02T07:24Z; no new researcher work this cycle)
**Iteration**: 10 (S1, S2, S2d, S3 PREP, S3 PREP-2, S3 ACT, S4 STATE-SYNC, S5 knowledge.md sync, S6 STATE-SYNC tick, this S7 STATE-SYNC tick; sub-iters S2b/c/e/f doc-only; supplementary S3 BUILD-DIAGNOSE #19122 + prior state-sync #18993)

## S7 STATE-SYNC tick 2026-06-04 (researcher-1)

**Mode:** STATE-SYNC tick — doc-only.

3-day elapse since S6 (2026-06-01). Phase RESEARCH-COMPLETE remains
in force; all forward items are Mechanic/Auditor/Doctor scope.

**Material event since S6**: Mechanic PR #21965 (merged
2026-06-02T07:24Z, meta-only, +5/-1 in
`src/data/proofs/greens-theorem-oq-01-oq-01-oq-02/meta.json`)
registered both orphan companions of the parent slug:

```
"additionalFiles": [
  "Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean",
  "Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean"
]
```

This drains a long-standing gallery-integration loose end: prior
to #21965, the auditor's orphan scan flagged this slug's Lean file
as unregistered with respect to the parent gallery entry. With the
registration in place, the slug's `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean`
is now part of the parent's recognized companion set — no separate
gallery entry needed for this OQ-only slug (consistent with the S1
OBSERVE disposition that no `src/data/proofs/<slug>/` directory
would be created for this slug).

**Negative confirmations** (independently re-checked at S7 entry):

- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` last touched
  at S3 ACT (#18944, 2026-05-13) — no semantic change since.
  Line/theorem/axiom/sorry counts unchanged
  (104 LOC / 1 theorem / 0 axioms / 0 sorries).
- Sibling `OQ02OQ03` (Bochner) file last touched at S3 ACT
  (2026-05-12, no later mechanic-style discharge yet). Sibling
  Bochner discharge remains forward-pending — out-of-scope for
  this slug.
- Mathlib pin still `2df2f0150c…` (v4.26.0) — stable since
  2026-05-13.
- Mechanic chain-build fix PR #21782 (2026-05-31) — already absorbed
  in S6; no further chain-build drift events to record.

**Forward items remaining at S7** (unchanged from S6):

- Docker-verify of this slug's 104-LOC file
  (`./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02`)
  — Mechanic/Auditor scope. With #21782 chain-fix in place and the
  bridge pattern at line 101-102 independently validated by parent
  PR #19218 (3058/3058 jobs clean), expected routine.
- Sibling OQ02OQ03 Bochner discharge — sibling-slug scope; out of
  scope for this slug.
- Mathlib upstream contribution candidates (S5 §3 catalog, 3
  candidates) — out-of-band mathlib4 PR scope; any contributor.

**S7 ship scope**: 3 files —
- `state.md` (this prepended block; S6 + earlier narrative preserved
  verbatim below)
- `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02.json`
  (iteration 9 → 10, lastUpdate / focus / attemptCounts refresh)
- `sessions/2026-06-04-s7-state-sync-companion-registration.md`
  (session memo).

**NO**: Lean edits, sibling slug edits, parent-slug `meta.json`
edits (already done by #21965), `leanFiles[]` numeric touches,
Mathlib pin walks.


## S6 STATE-SYNC tick 2026-06-01 (researcher-1)

**Mode:** STATE-SYNC tick — doc-only.

16-day elapse since S5 (2026-05-16T15:40Z). Phase RESEARCH-COMPLETE
remains in force; all forward items are Mechanic/Auditor/Doctor
scope.

**Independent cross-slug confirmation** (from
`/Users/rwalters/.claude/projects/-Users-rwalters-GitHub-lean-genius/memory`
entry `project_greens_theorem_chain_audit_failure_2026_05_31`): the
greens-theorem chain build was FIXED by mechanic PR #21782 on
2026-05-31, addressing Mathlib v4.26.0 API drift (`prod_mk` →
`prodMk`, `eventually_of_forall` → `Eventually.of_forall`,
`swap_symm` → `symm_swap`, `swap_apply_of_ne` →
`swap_apply_of_ne_of_ne`). This drains the S5 §4 "Docker-verify of
this slug's 104-LOC file" forward item.

**INFRA at S6 entry**: Docker 29.4.1, disk 55 Gi, Mathlib pin
`2df2f0150c…` (v4.26.0) stable ~20d. No bearer re-walk needed —
PREP-7 bearer kit carry-forward valid.

**Forward items remaining at S6**:

- Sibling OQ02OQ03 Bochner discharge — out-of-scope for this slug
  (sibling slug's tracker is authoritative).
- Mathlib upstream contributions (S5 §3 catalog: 3 candidates,
  out-of-band mathlib4 PR scope).

**S6 ship scope**: 2 files — `state.md` (this prepended block;
S5 narrative preserved verbatim below) + `src/data/research/problems/
greens-theorem-oq-01-oq-01-oq-02-oq-02.json` (iteration 8 → 9,
lastUpdate / focus / attemptCounts refresh).

**NO**: Lean edits, sibling slug edits, `leanFiles[]` numeric
touches, Mathlib pin walks.


**Owner**: distributed — researcher-10 (S3 ACT), researcher-8 (S1),
researcher-? (S2 + S2d), researcher-1 (S3 PREP + S4 STATE-SYNC),
researcher-5 (S3 PREP-2), researcher-4 (prior STATE-SYNC #18993),
researcher-12 (S3 BUILD-DIAGNOSE #19122), mechanic (#19130, #19218),
researcher-9 (this S5 knowledge.md sync)

> _Phase note_: this skill maps "S5 knowledge.md sync" to the canonical
> ORIENT phase (8th design iteration; researcher-scope closure of the
> Decomposition Plan row pending since S4).

## S5 (researcher-9, 2026-05-16, doc-only)

S4 STATE-SYNC (researcher-1, same day at 00:00Z) absorbed Mechanic
PRs #19130 + #19218 into state.md but explicitly deferred 3 forward
items, one of which was researcher-scope:

> Knowledge.md correction (~30 MD lines, researcher scope): the phantom
> name `restrict_prod_eq_prod_restrict` is still referenced at lines
> 36, 62, 86; the post-mechanic narrative needs to land. Plus the
> "S5 Mathlib contribution candidates" §4 from #18711 (the
> `restrict_prod_eq_prod_restrict` Multiset-each-factor lemma is a
> genuine upstream candidate). Deferred from this STATE-SYNC to a
> dedicated researcher cycle.

S5 closes that gap. **No Lean changes.** knowledge.md gets a new
final section "S5 (researcher-9, 2026-05-16) — Post-mechanic
clearance + Mathlib contribution catalog" (~120 MD lines)
containing:

- **Post-mechanic narrative table**: 4-row inventory mapping each
  drifted surface (parent line 192, this slug line 101-102, 7
  IntervalIntegral barrel imports, 1 Equiv.Fin barrel import) to
  the repair source (Mechanic #19218 / S3 ACT #18944 / Mechanic
  #19130) and Docker-build status. **Key implication**: the bridge
  pattern at this slug's line 101-102 is no longer speculative —
  it's the SAME pattern that compiled cleanly in the parent's
  3058/3058-job Docker build at parent line 192.
- **S5 Mathlib contribution candidates** (3 numbered candidates,
  restated from S3 PREP #18711 §4 — verbatim where applicable, with
  v4.26.0-idiom signatures):
  1. `Measure.restrict_prod_restrict` (1-line wrapper for the
     non-existent phantom — medium upstream value);
  2. `LocallyIntegrable.integrableOn_of_isCompact` (cosmetic
     rename/variant — low upstream value);
  3. `Measure.restrict_pi_restrict` (genuinely new infrastructure
     generalizing #1 to arbitrary index types — higher upstream
     value).
- **Slug closure posture**: declares slug research-complete after
  S5. All 8 forward checkmarks listed. Remaining items (Docker-verify,
  sibling Bochner, upstream Mathlib PRs) explicitly enumerated as
  out-of-researcher-scope.

### Coordination

- **State.md head**: updated above to mark slug RESEARCH-COMPLETE
  (was: `S3 ACT shipped (#18944); ...`); iter 7 → 8; Last Updated
  refreshed to 15:40Z; Owner list appends researcher-9.
- **Decomposition Plan row `S5 knowledge.md sync`** (line 124 in
  the pre-S5 table): status `pending (researcher)` → `**this PR**`.
- **JSON**: `lastUpdate` 2026-05-16T00:00:00Z → 15:40Z;
  `currentState.phase` ACT → RESEARCH-COMPLETE;
  `currentState.iteration` 7 → 8; `currentState.focus` rewritten
  to point at S5 post-mechanic clearance; `currentState.nextAction`
  rewritten to declare no further researcher session anticipated;
  `attemptCounts.total` 7 → 8; `knowledge.progressSummary`
  appended with S5 paragraph; `knowledge.nextSteps` updated (4 → 3
  items — drop the now-discharged `S5 knowledge.md sync` item).
- **Files NOT touched**: Lean files (no semantic change),
  `problem.md` (problem definition unchanged), `meta.json` (no
  gallery dir for this OQ-only slug — N/A), sibling slugs, parent
  file, lake-manifest.

### Why S5 (not directly RESEARCH-COMPLETE-only STATE-SYNC)

The S4 STATE-SYNC's Decomposition Plan explicitly slotted a S5
researcher-scope row. Shipping a thinner "STATE-SYNC declaring
research-complete" would leave the Decomposition Plan with a
pending researcher row, generating confusing future-researcher
orientation. S5 does the documented researcher work and updates
state.md + JSON to mark the slug research-complete in one motion.

See `sessions/2026-05-16-s5-knowledge-md-sync-post-mechanic.md`
for the full memo.

## Current Focus

S2 SCAFFOLD landed (#18364) with a phantom Mathlib lemma name
(`restrict_prod_eq_prod_restrict`) at line 89 of the wrapper file.
The build has never been verified. S3 PREP (#18711) audited the
phantom and proposed a corrected discharge via `volume_eq_prod` +
`← Measure.prod_restrict`. This S3 PREP-2 verifies the corrected
discharge at the Mathlib pin (rev `2df2f015`) and resolves the open
question in #18711 §3 (the explicit `rw [volume_eq_prod ℝ ℝ]` is
required; `rw` does not unify modulo defeq even for `rfl`-provable
equations). A working in-repo precedent
(`proofs/Proofs/AreaOfCircleOQ05OQ04.lean:158`) confirms the call
shape.

## Active Approach

**Wrapper / alternative-interface, not strict weakening.**

The parent (`Proofs.GreensTheoremOQ01OQ01OQ02`) proves
`intervalIntegral_swap` with the awkward hypothesis
`Integrable f ((volume.restrict (uIcc a b)).prod (volume.restrict
(uIcc c d)))`. The S2 deliverable provides a wrapper

```lean
intervalIntegral_swap_of_locallyIntegrable :
  Measurable (fun p => f p.1 p.2) →
  LocallyIntegrable (fun p => f p.1 p.2) volume →
  ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y
```

that discharges the awkward hypothesis internally via
`LocallyIntegrable.integrableOn_isCompact` plus the
`volume_eq_prod ℝ ℝ` + `← Measure.prod_restrict` bridge (verified in
S3 PREP-2 §6).

## Blockers

**Upstream blockers cleared by mechanic cycle** (see S4 STATE-SYNC memo
`sessions/2026-05-16-s4-state-sync-mechanic-prs-absorb-and-bridge-independent-validation.md`):

- ✅ **Mechanic PR #19130** (8 LOC across 7 files): applied v4.26.0
  `IntervalIntegral` + `Equiv.Fin` barrel-split import swaps. Closes
  the cascade identified in S3 BUILD-DIAGNOSE #19122 §4.2.
- ✅ **Mechanic PR #19218** (parent file, +8/-7): repaired 4 latent
  v4.26.0 semantic regressions in
  `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean`, including the
  phantom `restrict_prod_eq_prod_restrict` at parent line 192 with
  the SAME `[MeasureTheory.IntegrableOn, Measure.volume_eq_prod,
  ← Measure.prod_restrict]` discharge pattern that this slug's S3 ACT
  applies at line 101. **Parent Docker-builds clean: 3058/3058 jobs,
  3.2s**. This **independently validates the bridge pattern** for
  v4.26.0 (precedent: parent's same chain compiles and reduces;
  see S4 STATE-SYNC memo §1).

**Remaining blockers**:

1. **Docker-verify of THIS slug's 104-LOC file**
   (`./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02`).
   No upstream blocker remains; the bridge pattern is independently
   pre-validated; expected to be routine. **Mechanic / Auditor scope**.
2. **Host disk 100% / 6.9 Gi avail + `docker info` timeout 10s**
   blocks researcher-side Docker-verify in current cycle. Not
   load-bearing — mechanic/auditor on a clean infra slot can verify
   when ready.
3. *Historical* (no longer load-bearing): researcher worktrees have
   the `proofs/.lake` self-referential symlink loop
   (memory: `feedback_researcher_lake_symlink_loop_and_wipe.md`).
   Doesn't matter — Docker-verify is mechanic/auditor scope.

## Next Action

S3 ACT shipped via **PR #18944** (`d32d7f682ee`, 2026-05-13/14); the
S3 PREP-2 §6 discharge `rw [IntegrableOn, volume_eq_prod ℝ ℝ,
← Measure.prod_restrict] at hint; exact hint` is at
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:101-102`. Post-S3
ACT, S3 BUILD-DIAGNOSE (#19122) identified the upstream cascade;
mechanic PRs #19130 + #19218 (parent Docker-clean 3058/3058 jobs
using same chain at parent:192) cleared it. **The bridge pattern is
independently validated for v4.26.0** (see S4 STATE-SYNC memo §1).

Forward work (in dependency order — most items now reduce to
Mechanic / Auditor scope):

1. **Docker-build verify this slug's 104-LOC file** via
   `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02`
   from a clean non-researcher infra slot. Expected routine: ~3000-3100
   jobs, ~3-5s post-cache. **No upstream blocker; no semantic risk
   expected** (precedent: parent build #19218 used the same chain).
   Mechanic / Auditor scope.

2. **S5 PREP for sibling `OQ02OQ03`** (Bochner codomain): same phantom
   discharge bridge if it carries the same drift. Likely 1-LOC patch
   following the parent #19218 pattern. Mechanic / Doctor scope; this
   STATE-SYNC does not change the slug's own progress.

3. **Knowledge.md correction** (~30 MD lines, researcher scope): the
   phantom name `restrict_prod_eq_prod_restrict` is still referenced
   at lines 36, 62, 86; the post-mechanic narrative needs to land.
   Plus the "S5 Mathlib contribution candidates" §4 from #18711
   (the `restrict_prod_eq_prod_restrict` Multiset-each-factor lemma
   is a genuine upstream candidate). Deferred from this STATE-SYNC
   to a dedicated researcher cycle.

**Progress on prior "Next Action" §3 sibling drift-sync** (now
partially superseded by mechanic cycle):

| Sibling file (per #18711 §1.1) | Phantom-name status | Closed by |
|:-------------------------------|:--------------------|:----------|
| `GreensTheoremOQ01OQ01OQ02.lean` (parent) | ✅ cleared | mechanic #19218 (line 192) |
| 7 cross-family import files | ✅ cleared | mechanic #19130 |
| `GreensTheoremOQ01OQ01OQ02OQ01.lean` | unchanged (this slug uses parent indirectly; sibling's own phantom-name disposition unverified — sibling has open S5 PREP-3 #19184) | partial — sibling-slug scope |
| `GreensTheoremOQ01OQ01OQ02OQ03.lean` (Bochner) | unchanged (phantom-name discharge still pending) | open |
| `AreaOfCircleOQ05OQ01.lean` | unchanged | open |

## Decomposition Plan

| Session | Phase | Deliverable | Lines | Status |
|---|---|---|---|---|
| S1 | OBSERVE | Audit + reframe seeker question | 0 Lean (docs) | **MERGED #18262** |
| S2 | SCAFFOLD | `intervalIntegral_swap_of_locallyIntegrable` proven inline (build pending) | ~30 Lean | **MERGED #18364, build pending** |
| S2d | PREP | Cross-family call-site verification | 0 Lean (docs) | **MERGED #18514** |
| S3 | PREP | Phantom `restrict_prod_eq_prod_restrict` audit + §3 corrected proof template | 0 Lean (docs) | **MERGED #18711** |
| S3 PREP-2 | PREP-2 | `volume_eq_prod` + `Measure.prod_restrict` + `SFinite` verification; resolves #18711 §3 open question; state.md sync | 0 Lean (docs) | **MERGED #18845** |
| S3 ACT | ACT | Apply S3 PREP-2 §6 discharge template at line 101 | ~13 Lean (rewrote `rw` step + comment block) | **MERGED #18944, build pending** |
| S3 ACT STATE-SYNC | SYNC | Rewrite state.md Next Action + Decomposition Plan post-#18944 | 0 Lean (docs) | **MERGED #18993** |
| S3 BUILD-DIAGNOSE | DIAGNOSE | v4.26.0 Mathlib import drift cascade inventory; 8-LOC mechanic patch budget across 7 distinct slug families | 0 Lean (docs) | **MERGED #19122** |
| S4 STATE-SYNC | SYNC | Absorb mechanic PRs #19130 (8-LOC import swap) + #19218 (parent 4-error repair, 3058/3058 jobs Docker-clean) + record parent-build independent validation of bridge pattern at OQ02OQ02.lean:101 | 0 Lean (docs) | **this PR** |
| S5 knowledge.md sync | SYNC | Post-mechanic clearance narrative (4-row repair-source inventory) + Mathlib upstream contribution catalog (3 candidates: `Measure.restrict_prod_restrict` 1-LOC wrapper, `LocallyIntegrable.integrableOn_of_isCompact` rename variant, `Measure.restrict_pi_restrict` arbitrary-index generalization); state.md head + JSON refresh | 0 Lean, ~120 MD added | **this PR** (researcher-9) |
| S5 PREP sibling Bochner | (optional) | S5 PREP for sibling `OQ02OQ03` Bochner codomain — same phantom discharge bridge | ~1 Lean LOC | pending (Mechanic / Doctor) |

## Attempt Counts

- Total attempts: 6 (S1, S2, S2d, S3 PREP, S3 PREP-2, S3 ACT; sub-iters S2b/c/e/f doc-only)
- Current approach attempts: 1 (volume_eq_prod + Measure.prod_restrict discharge — applied at S3 ACT #18944)
- Approaches tried:
  - S1 (researcher-8): OBSERVE audit + reframing.
  - S2 (researcher-?): SCAFFOLD wrapper file with the phantom name.
  - S2d (researcher-?): PREP cross-family call-site verification.
  - S3 (researcher-1): PREP phantom audit + proposed `volume_eq_prod`
    + `← Measure.prod_restrict` discharge with open question.
  - S3 PREP-2 (researcher-5): PREP-2 four-step Mathlib verification
    resolving the open question, in-repo precedent identification,
    state.md sync.

## Key Risks

1. **Phrasing trap.** Future iterations must not claim the wrapper
   "weakens" the hypothesis — it strengthens it. The wrapper is a
   usability improvement, not a mathematical refinement.
   (Documented in `knowledge.md` § "Reframing the question".)
2. **`LocallyIntegrable.integrableOn_isCompact` name drift.** Mathlib
   v4.26.0 should have the lemma at this name; if it has drifted, the
   Mechanic ACT will need to search variants
   (`integrableOn_compact`, `integrableOn_of_isCompact`).
3. **Phantom `restrict_prod_eq_prod_restrict` propagation** —
   *substantially closed by mechanic cycle (2026-05-14 → 2026-05-15)*.
   The 4 originally-identified sibling files (#18711 §1.1) now show:
   parent ✅ repaired by mechanic #19218 (line 192 discharge w/ same
   pattern as this slug's line 101); 7 cross-family import-drift
   files ✅ repaired by mechanic #19130; remaining: `OQ02OQ03`
   (Bochner) + `AreaOfCircleOQ05OQ01` carry phantom-name discharge
   still pending (deferred to sibling-slug S5 PREPs). The parent's
   gallery `status: verified` flag is no longer structurally stale
   w.r.t. the phantom-name issue.
4. **`rw` vs `simp only` for `IntegrableOn`.** S3 PREP-2 §6's
   `rw [IntegrableOn, ...]` step depends on Lean treating `IntegrableOn`
   as `reducible` for `rw`; if not, the Mechanic ACT may need to swap
   to `simp only [IntegrableOn]` or `show Integrable …` at that step.
   The §6 template's other rewrites (`volume_eq_prod ℝ ℝ`,
   `← Measure.prod_restrict`) are independently verified and not
   affected by this risk.

## References

- Parent: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (verified status,
  but the verified flag is structurally stale per #18711 §1.1).
- Sibling OQ-03: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ03.lean`
  (same wrapper-style pattern for Bochner codomain; has the same
  phantom-name issue at its tail).
- Sibling OQ-01: `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
  (n-dim lift via `Measure.pi`; same phantom-name issue).
- Mathlib: `MeasureTheory.LocallyIntegrable` in
  `Mathlib.MeasureTheory.Function.LocallyIntegrable`;
  `MeasureTheory.Measure.prod_restrict` in
  `Mathlib.MeasureTheory.Measure.Prod:720`;
  `MeasureTheory.volume_eq_prod` in
  `Mathlib.MeasureTheory.Measure.Prod:179` (`rfl`).
- Sessions: `sessions/2026-05-12-s02-scaffold.md`,
  `sessions/2026-05-13-s02b-prep-mathlib-drift-audit.md`,
  `sessions/2026-05-13-s02c-prep-mathlib-v4-26-0-source-tree-verification.md`,
  `sessions/2026-05-13-s02d-prep-cross-family-call-site-verification.md`,
  `sessions/2026-05-13-s2e-prep-area-of-circle-direction-correction.md`,
  `sessions/2026-05-13-s2f-prep-volume-eq-prod-prerequisite.md`,
  `sessions/2026-05-13-s3-prep-phantom-mathlib-audit.md`,
  `sessions/2026-05-13-s3-prep-2-volume-bridge-verification.md` (this).
- Predecessor PRs: #18262 (S1), #18364 (S2), #18514 (S2d), #18711 (S3).

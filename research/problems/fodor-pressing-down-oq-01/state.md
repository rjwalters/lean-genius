# Current State

**Phase**: ACT (S2 ACT shipped; S3/S4 PREP saturated; S3/S4 ACT pending)
**Since**: 2026-05-13T09:29:11Z (S4d PREP, latest merge)
**Iteration**: 7
**Last update**: 2026-05-13 (STATE-SYNC by researcher-10)

## Current Focus

The slug's S1 OBSERVE design lock (Ordinal namespace,
`proofs/Proofs/Club/Basic.lean` placement, structure-vs-Prop split)
was fully discharged at S2 ACT: `proofs/Proofs/Club/Basic.lean` is on
`origin/main` at 98 LOC, 4 defs + 1 structure + 5 theorems, 0 sorries,
0 axioms.

The four PREP iterations after S2 ACT (S3, S4, S4b, S4c, S4d) have
**fully saturated the parent-trim recipe** for the eventual S4 ACT
cut: a 649-LOC consumer audit + corrected re-anchoring plan + line-
drift audit + audit-correction. **The S3 and S4 ACT cuts have not
yet been executed**: parent `Proofs/FodorPressingDown.lean` retains
duplicate definitions (12 theorems, 4 defs/structs, 385 LOC).

### Per-stage status

| Stage | Type | Anchor PR | Status |
|---|---|---|---|
| S1 OBSERVE  | doc-only | #18280 | ✅ merged |
| S2 ACT      | Lean     | #18367 | ✅ merged (98 LOC, 0 sorries, 0 axioms, build pending) |
| S3 PREP     | doc-only | #18412 | ✅ merged |
| S3 ACT      | Lean     | —      | ⏳ pending (~28 LOC migration of `diagInter_isClosedBelow`) |
| S4 PREP     | doc-only | #18441 | ✅ merged |
| S4b PREP    | doc-only | #18519 | ✅ merged |
| S4c PREP    | doc-only | #18585 | ✅ merged |
| S4d PREP    | doc-only | #18733 | ✅ merged (audit-correction of S4c §2/§3/§7.1) |
| S4 ACT      | Lean     | —      | ⏳ pending (parent –150 LOC trim per S4c §12.2, corrected by S4d §9) |

## Active Approach

**Four-phase library refactor**, three PREP iterations into S4 saturation.

1. ✅ **S1 OBSERVE** — locked naming (`Ordinal` namespace), path
   (`Proofs/Club/Basic.lean`), structure-vs-Prop split, universe
   policy.
2. ✅ **S2 ACT** — shipped `Proofs/Club/Basic.lean` with 4 defs +
   1 structure (`IsUnboundedBelow`, `IsClubBelow`, `IsStationaryBelow`,
   `diagInter`, `IsRegressive`) + 5 mechanical theorems
   (`IsClubBelow.mem_lt`, `IsClubBelow.mem_of_isAcc`, `mem_diagInter`,
   `diagInter_subset_Iio`, `isClubBelow_Iio_of_isSuccLimit`). Module is
   strictly additive: parent untouched.
3. ⏳ **S3 ACT** — migrate `diagInter_isClosedBelow` from parent into
   the new module. Plan locked in S3 PREP (PR #18412); ~28 LOC,
   cofinality-free, no new Mathlib dependencies.
4. ⏳ **S4 ACT** — trim parent. Cut the five S2-duplicate definitions
   plus the moved `diagInter_isClosedBelow`. Update internal cite
   paths per S4c PREP (PR #18585) §12.2 cheat-sheet, with S4d PREP
   (PR #18733) §9 corrections folded in. Net parent delta ≈ −150 LOC;
   `meta.json` `lineCount`/`theoremCount` for the parent slug
   (`fodor-pressing-down`) and any downstream
   (`fodor-pressing-down-oq-04`) updated as a bookkeeping step.

The PREP saturation is intentional: the parent file is a Wiedijk-100
verified entry, so the S4 cut must not regress the build and must
not break annotation re-anchoring. The S4b/S4c/S4d sequence verified
all call-sites and gave the mechanic a verbatim drop-in.

## S1 historical context

The original S1 OBSERVE deliverable was three markdown files + one
JSON gallery entry, covering the formal signature targets,
acceptance criteria, related slugs, Mathlib alignment survey,
migration plan, risk register, and sister-slug compatibility design
(`fodor-pressing-down-oq-04` Solovay splitting). Those documents
remain authoritative for design intent; the per-stage table above
supersedes the original "S1 → S2 → S3 → S4 → S5" outline now that
two ACT and five PREP iterations have shipped.

## S1 Summary

### Locked design decisions

1. **Naming.** `Ordinal.IsUnboundedBelow`, `Ordinal.IsClubBelow`
   (structure with three fields), `Ordinal.IsStationaryBelow`,
   `Ordinal.diagInter`, `Ordinal.IsRegressive` — all in the `Ordinal`
   namespace, matching `Ordinal.IsAcc` (existing in Mathlib).
2. **File path.** `proofs/Proofs/Club/Basic.lean`. New directory
   `proofs/Proofs/Club/` introduced for future siblings
   (`DiagonalIntersection.lean`, `Galvin.lean`, etc.).
3. **Universe polymorphism.** Definitions stay universe-polymorphic
   in the new module; combinatorial lemmas (`diagInter_isClubBelow`,
   `fodor`) remain pinned at `Cardinal.{0}` until a downstream
   request appears.
4. **Structure vs Prop.** `IsClubBelow` is a `structure` (three
   fields), matching the local file. `IsUnboundedBelow`,
   `IsStationaryBelow`, `IsRegressive`, `diagInter` are
   `def`-bindings returning `Prop` / `Set Ordinal`.

### Migration plan (committed)

- **S2 ACT**: ship `proofs/Proofs/Club/Basic.lean` with the five
  definitions + three mechanical lemmas (~80 Lean LOC, 0 sorries).
  Add `import Proofs.Club.Basic` to `proofs/Proofs.lean`. Build-
  pending tolerable.
- **S3 ACT**: move `diagInter_isClosedBelow` from parent to new
  module (~28 LOC migration, parent decreases by 28).
- **S4 ACT**: trim `proofs/Proofs/FodorPressingDown.lean` — remove
  the five moved definitions and three moved lemmas; add `import
  Proofs.Club.Basic`. Update `meta.json` `lineCount` /
  `theoremCount` for `fodor-pressing-down-oq-04`. Net parent
  delta ≈ –150 LOC.
- **S5 (optional)**: doc-only update to `fodor-pressing-down-oq-04`'s
  `problem.md` recording the new dependency path.

### Mathlib alignment summary

- **In Mathlib already**: `IsClosedBelow`, `Ordinal.IsAcc`,
  `Cardinal.cof`, `Cardinal.IsRegular`, `Cardinal.IsRegular.aleph0_le_cof`.
- **New code required**: `IsUnboundedBelow`, `IsClubBelow`,
  `IsStationaryBelow`, `diagInter`, `IsRegressive` plus their
  mechanical and combinatorial supporting lemmas.

### Sister-slug compatibility

`fodor-pressing-down-oq-04` (Solovay splitting, NEW phase since
2026-05-12 14:35 UTC) is the primary downstream consumer. Its
eventual Lean file will start with `import Proofs.Club.Basic` and
use `Ordinal.IsStationaryBelow` directly. Without OQ-01 lifted,
OQ-04 either inlines duplicate predicates or depends on the entire
parent `FodorPressingDown.lean`. The plan unblocks OQ-04 once S4
lands.

## Blockers

None mathematical. The refactor is mechanical; remaining risk is the
S4 ACT parent-cut, mitigated by the S4c (PR #18585) verbatim
re-anchoring recipe and the S4d (PR #18733) audit-correction.

**Build verification pending** for S2 ACT (PR #18367). The PR shipped
build-pending because of the worktree `proofs/.lake` recursive
symlink trap; docker-build verification is deferred to the auditor /
mechanic. No build failure has been reported.

**Operational:** worktree `proofs/.lake` symlink is recursive
(`feedback_researcher_lake_symlink_broken.md`); local docker build is
~25–45 min. PREP iterations are doc-only and need no build.

## Next Action

**S3 ACT — any researcher.** Migrate `diagInter_isClosedBelow` from
`proofs/Proofs/FodorPressingDown.lean` (lines 102–124, ~23 LOC body)
into `proofs/Proofs/Club/Basic.lean` per the S3 PREP (PR #18412) plan.
After the move:

- Parent `FodorPressingDown.lean` decreases by ~28 LOC (the lemma plus
  its docstring); cite the lemma as `Ordinal.diagInter_isClosedBelow`.
- `Proofs/Club/Basic.lean` gains the lemma; net +28 LOC.
- `meta.json` `lineCount` / `theoremCount` for `fodor-pressing-down`
  parent decreases; for `fodor-pressing-down-oq-01` it stays at S2's
  Basic.lean count.
- Run `docker-build.sh Proofs.FodorPressingDown` and
  `docker-build.sh Proofs.Club.Basic` to verify.

**S4 ACT — any researcher (sequential after S3 ACT).** Trim parent
per the S4c PREP (PR #18585) §12.2 cheat-sheet, corrected by S4d PREP
(PR #18733) §9:

- Delete the five S2-duplicate definitions from
  `proofs/Proofs/FodorPressingDown.lean` (`IsUnboundedBelow`,
  `IsClubBelow`, `IsStationaryBelow`, `diagInter`, `IsRegressive`).
- Re-anchor downstream theorem signatures to use
  `Ordinal.IsClubBelow`, etc. (S4b PREP §3 verified
  `IsStationaryBelow.{nonempty,of_subset}` bodies stay sound under
  the rename; S4c PREP §7 verified annotation re-anchoring).
- Update `src/data/proofs/fodor-pressing-down/meta.json` and
  `annotations.json` per S4c §7 recipe (lineCount, theoremCount,
  annotation line offsets).
- Net parent delta ≈ −150 LOC; preserves Wiedijk-100 entry; build
  must remain green.

S5 (optional doc-only) once S4 ACT lands: update sister oq-04's
`problem.md` to point at the new Basic.lean dependency.

## Attempt Counts

- Total attempts: 7 (S1 OBSERVE, S2 ACT, S3 PREP, S4 PREP, S4b PREP,
  S4c PREP, S4d PREP — all merged).
- Current approach attempts: 7.
- Approaches tried: 1 (library refactor with `Ordinal`-namespace
  naming and `Proofs/Club/Basic.lean` placement, design decisions
  unchanged since S1).

## Sessions

- **S1 OBSERVE** (2026-05-12, researcher-1): doc-only — `problem.md`,
  `knowledge.md`, `state.md`, JSON entry. Locked design. PR #18280.
- **S2 ACT** (2026-05-12, researcher-?): ACT — shipped
  `Proofs/Club/Basic.lean` (98 LOC, 4 defs + 1 structure + 5 theorems,
  0 sorries, 0 axioms; build pending). PR #18367. See
  `sessions/2026-05-12-s02-act-club-basic.md`.
- **S3 PREP** (2026-05-12, researcher-?): doc-only — migration plan
  for `diagInter_isClosedBelow`. PR #18412. See
  `sessions/2026-05-12-s03-prep-diagInter-isClosedBelow-migration.md`.
- **S4 PREP** (2026-05-12, researcher-?): doc-only — parent-trim
  call-site audit. PR #18441. See
  `sessions/2026-05-12-s04-prep-parent-trim-audit.md`.
- **S4b PREP** (2026-05-13, researcher-?): doc-only — Route A body
  audit for `IsStationaryBelow.{nonempty,of_subset}` (+468 LOC).
  PR #18519. See
  `sessions/2026-05-13-s04b-prep-route-a-IsStationaryBelow-bodies.md`.
- **S4c PREP** (2026-05-13, researcher-?): doc-only — full consumer
  audit + annotation re-anchoring recipe (+649 LOC). PR #18585. See
  `sessions/2026-05-13-s04c-prep-full-consumer-audit-and-annotation-recipe.md`.
- **S4d PREP** (2026-05-13, researcher-?): doc-only — audit-correction
  of S4c §2/§3/§7.1 (IsRegressive parent-cite + LOC + count
  discrepancies). PR #18733. See
  `sessions/2026-05-13-s04d-prep-audit-correction-IsRegressive-and-definitionCount.md`.

## Open files

- `problem.md` — formal scope and signature targets (S1 OBSERVE).
- `knowledge.md` — Mathlib alignment survey and migration plan
  (S1 OBSERVE, supplemented by S3 PREP's migration detail).
- `state.md` (this file).
- `proofs/Proofs/Club/Basic.lean` — new module shipped at S2 ACT;
  awaits S3 ACT (gain `diagInter_isClosedBelow`).
- `proofs/Proofs/FodorPressingDown.lean` — parent file; **not yet
  touched** by any ACT after S2. Awaits S3 ACT (lose
  `diagInter_isClosedBelow`) then S4 ACT (lose five duplicates).

## Drift / parent state

- Parent `Proofs/FodorPressingDown.lean` is **verified** (Wiedijk #25)
  on `origin/main`: 12 theorems, 4 defs/structs, 385 LOC, 0 sorries,
  0 axioms. Retains DUPLICATE definitions (the same 5 names that S2
  ACT placed in `Proofs/Club/Basic.lean`); these duplicates stay
  until S4 ACT cuts them.
- `proofs/Proofs.lean` registers `Proofs.Club.Basic` from S2 ACT
  (verified in PR #18367).
- Parent `src/data/proofs/fodor-pressing-down/meta.json` reports
  `theoremCount=12`, `definitionCount=4`, matching the on-main parent
  file. Both will shift after S3 ACT (theoremCount → 11) and S4 ACT
  (definitionCount → 0 if duplicates fully cut, plus parent →LOC
  ~235).
- Sister slug `fodor-pressing-down-oq-04` (Solovay splitting) is
  the primary downstream consumer of `Proofs.Club.Basic`; it is
  expected to `import Proofs.Club.Basic` on its first commit.

## Race awareness

OQ-01 has six merged PRs (S1 OBSERVE through S4d PREP) and zero
open PRs at this STATE-SYNC's push time. The sister slug
`fodor-pressing-down-oq-04` was NEW at S1 OBSERVE and is expected
to enter ACT once S4 ACT lands. Re-entry risk for this STATE-SYNC
is low: any parallel researcher would observe the JSON OBSERVE/iter-1
drift before this PR merges, but the new branch off `origin/main`
ensures no PR scope contamination.

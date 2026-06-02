# Current State

**Phase**: ACT (S7 IsStationaryBelow companion lemmas lifted to Basic.lean; S4 ACT still pending)
**Since**: 2026-06-01 (S7 ACT this session — researcher-1)
**Iteration**: 11
**Last update**: 2026-06-01 (S7 ACT by researcher-1 — Basic.lean +29 LOC, 2 IsStationaryBelow companion lemmas lifted from parent §Part VI)

> **Phase note (skill-compliance footnote):** `STATE-SYNC` is a sub-phase
> within the broader research lifecycle (no `REFINE`-style ACT this round).
> Maps to skill-canonical `OBSERVE` for the next wake-up.

## Current Focus

The slug's S1 OBSERVE design lock (Ordinal namespace,
`proofs/Proofs/Club/Basic.lean` placement, structure-vs-Prop split)
was fully discharged at S2 ACT: `proofs/Proofs/Club/Basic.lean` is on
`origin/main` at 98 LOC, 4 defs + 1 structure + 5 theorems, 0 sorries,
0 axioms.

The five PREP iterations after S2 ACT (S3, S4, S4b, S4c, S4d) have
**fully saturated the parent-trim recipe** for the eventual S4 ACT
cut: a 649-LOC consumer audit + corrected re-anchoring plan + line-
drift audit + audit-correction. **S3 ACT (this session, researcher-12)
shipped** the verbatim migration of `diagInter_isClosedBelow` to
`Proofs/Club/Basic.lean` (98 → 119 LOC; +21 LOC; Docker-verified).
**S4 ACT (parent cut) remains pending**: parent
`Proofs/FodorPressingDown.lean` still retains the five S2-duplicate
definitions plus its local `diagInter_isClosedBelow` body (385 LOC).

### Per-stage status

| Stage | Type | Anchor PR | Status |
|---|---|---|---|
| S1 OBSERVE  | doc-only | #18280 | ✅ merged |
| S2 ACT      | Lean     | #18367 | ✅ merged (98 LOC, 0 sorries, 0 axioms, build pending at merge time → verified clean baseline this session) |
| S3 PREP     | doc-only | #18412 | ✅ merged |
| S3 ACT      | Lean     | (this session) | ✅ S3 ACT shipped this session — Basic.lean 98 → 119 LOC (+21), Docker-verified pre/post (3060 jobs each) |
| S4 PREP     | doc-only | #18441 | ✅ merged |
| S4b PREP    | doc-only | #18519 | ✅ merged |
| S4c PREP    | doc-only | #18585 | ✅ merged |
| S4d PREP    | doc-only | #18733 | ✅ merged (audit-correction of S4c §2/§3/§7.1) |
| S4 ACT      | Lean     | —      | ⏳ pending (parent –150 LOC trim per S4c §12.2, corrected by S4d §9) |
| S6 ACT      | Lean     | #21421 | ✅ merged — Basic.lean 119 → 154 LOC (+35), 4 `IsRegressive` companion lemmas (`empty`, `mono`, `inter_preimage`, `iff_forall_lt`), Docker-verified 3060 jobs |
| S7 ACT      | Lean     | (this session) | ✅ S7 ACT shipped this session — Basic.lean 154 → 183 LOC (+29), 2 `IsStationaryBelow` companion lemmas (`nonempty`, `of_subset`) **lifted** from parent §Part VI (lines 334–348), Docker-verified 3060 jobs |

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
3. ✅ **S3 ACT** — shipped this session (researcher-12). Migrated
   `diagInter_isClosedBelow` verbatim from parent
   (`FodorPressingDown.lean` lines 102–124) into `Proofs/Club/Basic.lean`
   under the `Ordinal` namespace. Body character-identical to parent;
   only namespace-resolution changes. Basic.lean grows 98 → 119 LOC
   (+21). Docker-verified twice: baseline build pre-patch =
   3060 jobs green (validates origin/main has no silent v4.26.0
   regression on `IsAcc.forall_lt` / `isAcc_iff` /
   `isClosedBelow_iff`); post-patch build = 3060 jobs green.
   Parent intentionally untouched — parent cut deferred to S4 ACT.
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

**S4 ACT — any researcher (S3 ACT shipped at PR #19009; S5 STATE-SYNC
shipped this session expands re-anchoring scope).** Trim parent per the
S4c PREP (PR #18585) §12.2 cheat-sheet, corrected by S4d PREP (PR #18733)
§9, **and additionally re-anchor 5 new theorems** added by sister-slug
oq-04 ACTs (see `sessions/2026-05-16-s05-...` §4):

- Delete the **four** S2-duplicate definitions from
  `proofs/Proofs/FodorPressingDown.lean` (`IsUnboundedBelow`,
  `IsClubBelow`, `IsStationaryBelow`, `diagInter` — note `IsRegressive`
  is NOT in parent; it lives in Basic.lean only)
  plus its now-redundant local copy of `diagInter_isClosedBelow`
  (parent body, migrated to `Proofs/Club/Basic.lean` at S3 ACT).
- Add `import Proofs.Club.Basic` to the parent.
- Re-anchor downstream theorem signatures to use
  `Ordinal.IsClubBelow`, etc. The list now spans **two cohorts**:
  - **Original-12 cohort (S4c PREP §7)**: theorems 7-12 in the parent
    inventory (`diagInter_isUnboundedBelow`, `diagInter_isClubBelow`,
    `fodor`, `fodor_aleph1`, `IsStationaryBelow.nonempty`,
    `IsStationaryBelow.of_subset`).
  - **NEW oq-04 cohort (S5 STATE-SYNC §4, this session)**: theorems 13-17
    (`isLimitOrdinals_isClubBelow`, `nonLimitOrdinals_not_isStationaryBelow`,
    `IsClubBelow.inter`, `IsStationaryBelow.inter_isClubBelow`,
    `IsStationaryBelow.inter_isLimitOrdinals`). Each consumes parent-local
    `IsClubBelow` / `IsStationaryBelow` / `diagInter` / `mem_diagInter` /
    `diagInter_isUnboundedBelow`; all need `Ordinal.` prefix or `open
    Ordinal` after the cut.
- Update `src/data/proofs/fodor-pressing-down/meta.json` and
  `annotations.json` per S4c §7 recipe (lineCount, theoremCount,
  annotation line offsets) — note meta.json `lineCount: 568,
  theoremCount: 17` from mechanic PR #19459 is the new pre-S4-ACT
  baseline; post-S4-ACT will subtract the 6 deleted theorems (5 dup
  defs cut nothing from theorem count, but `diagInter_isClosedBelow`
  removal subtracts 1) → projected `theoremCount: 16` post-cut.
- Net parent delta ≈ **−180 LOC** (180 = 5 defs + 1 dup theorem +
  surrounding `Part`/`Section` headers; revised from −150 LOC at S4c
  PREP estimate which assumed the original 385-LOC parent). Preserves
  Wiedijk-100 entry; build must remain green.

S6 (optional doc-only) once S4 ACT lands: update sister oq-04's
`problem.md` to point at the new Basic.lean dependency, and consider
moving `IsClubBelow.inter` / `IsStationaryBelow.inter_*` from parent →
Basic.lean as library-style lemmas (deferred; not blocking S4 ACT).

## Attempt Counts

- Total attempts: 11 (S1 OBSERVE, S2 ACT, S3 PREP, S4 PREP, S4b PREP,
  S4c PREP, S4d PREP, S3 ACT, S5 STATE-SYNC, S6 ACT, S7 ACT — all
  merged or pending merge of this PR).
- Current approach attempts: 11.
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
- **STATE-SYNC** (2026-05-13, researcher-10): doc-only — JSON phase
  + state.md refreshed to reflect S2 ACT shipped + S3/S4 PREP saturation.
  PR #18905.
- **S3 ACT** (2026-05-13, researcher-12): Lean +21 LOC — verbatim
  migration of `diagInter_isClosedBelow` from parent
  (`FodorPressingDown.lean` lines 102–124) into `Proofs/Club/Basic.lean`
  under `Ordinal` namespace. Docker-build verified twice (baseline
  3060 jobs + post-patch 3060 jobs, both green). 0 sorries, 0 axioms
  added. Parent intentionally untouched (S4 ACT scope). See
  `sessions/2026-05-13-s05-act-diagInter-isClosedBelow.md`. PR #19009.
- **S5 STATE-SYNC** (2026-05-16, researcher-5): doc-only — absorbed
  parent file growth (385 → 568 LOC, +183 LOC) driven by sister-slug
  `fodor-pressing-down-oq-04`'s S2-α ACT (#19052) +
  S2-β-α ACT (#19378). Expanded S4 ACT re-anchoring scope to cover 5
  new theorems (`isLimitOrdinals_isClubBelow`,
  `nonLimitOrdinals_not_isStationaryBelow`, `IsClubBelow.inter`,
  `IsStationaryBelow.inter_isClubBelow`,
  `IsStationaryBelow.inter_isLimitOrdinals`). Parent meta.json already
  synced by mechanic PR #19459 (no further meta edit). Iteration 8 → 9.
  See `sessions/2026-05-16-s05-state-sync-parent-growth-absorption-oq04-theorems.md`.
- **S6 ACT** (2026-05-31, researcher-1): Lean +35 LOC — four `IsRegressive`
  companion lemmas added to `Proofs/Club/Basic.lean` (119 → 154 LOC):
  `IsRegressive.empty`, `IsRegressive.mono`, `IsRegressive.inter_preimage`,
  `IsRegressive.iff_forall_lt`. Strictly additive; parent untouched.
  Also absorbs parent growth from sister-slug oq-04 S2-β-β ACT
  (PR #20621, 2026-05-25) which added `noncomputable def cofHead` plus
  3 theorems (`cofHead_lt`, `exists_cofHead_constant_stationary`,
  `exists_cofHead_constant_stationary_of_stationary`), bringing parent
  to 568 → 654 LOC (+86 LOC), 17 → 20 theorems, 4 → 4 defs (cofHead
  replaces an existing slot via meta convention). Expanded S4 ACT
  re-anchoring scope to 20 downstream theorems (17 from S5 STATE-SYNC
  + 3 cofHead-cohort). Iteration 9 → 10. See
  `sessions/2026-05-31-s06-act-IsRegressive-companion-lemmas.md`. PR #21421.
- **S7 ACT** (2026-06-01, researcher-1): Lean +29 LOC — two
  `IsStationaryBelow` companion lemmas **lifted** from parent §Part VI
  (`Proofs/FodorPressingDown.lean` lines 334–348) into
  `Proofs/Club/Basic.lean` under the `Ordinal` namespace
  (154 → 183 LOC): `IsStationaryBelow.nonempty` (witness:
  `isClubBelow_Iio_of_isSuccLimit`) and `IsStationaryBelow.of_subset`
  (stationarity descends along club-meet-preserving inclusions). Both
  signatures take bare `o : Ordinal` (not `Cardinal.{0}.ord`); proof
  bodies byte-identical to parent. Strictly additive; parent untouched.
  Docker-verified 3060/3060 jobs green. Expanded S4 ACT cut scope by
  15 LOC (parent lines 334–348 also delete-eligible now). Cohort A
  (universe-not-pinned) of parent's library lemmas now **exhausted**.
  Iteration 10 → 11. See
  `sessions/2026-06-01-s07-act-stationary-helpers.md`.

## Sibling-slug interaction (S5 STATE-SYNC, oq-04 S2-α + S2-β-α)

Sister slug `fodor-pressing-down-oq-04` (Solovay splitting) shipped 2
substantive ACTs that grew the parent file `FodorPressingDown.lean`
between this slug's S3 ACT (2026-05-14) and S5 STATE-SYNC (2026-05-16):

| Date | Slug | Event | PR | Parent Δ LOC |
|------|------|-------|----|----|
| 2026-05-14 | oq-04 | S2-α ACT — limit ordinals form a club | #19052 | +68 |
| 2026-05-15 | oq-04 | S2-β-α ACT — Club ∩ Club + Stationary ∩ Club | #19378 | +115 |

These 2 ACTs added **5 new theorems** (rows 13-17 in §3 audit table of the
S5 session memo), all of which consume parent-local predicates
`IsClubBelow` / `IsStationaryBelow` / `diagInter` / `mem_diagInter` /
`diagInter_isUnboundedBelow`. When this slug's S4 ACT cuts the parent
duplicates, all 5 new theorems need re-anchoring to `Ordinal.IsClubBelow`
(etc.) — mechanical `Ordinal.` prefix or `open Ordinal` insertion, no
semantic change.

**S6 (optional, post-S4 ACT)**: consider lifting `IsClubBelow.inter`,
`IsStationaryBelow.inter_isClubBelow`, `IsStationaryBelow.inter_isLimitOrdinals`
from parent → Basic.lean. These are *library-style* lemmas (binary club
intersection + stationary preservation under club intersection +
WLOG-stationary-to-limits reduction); they would broaden Basic.lean's
utility for any future client of club/stationary infrastructure. NOT
blocking S4 ACT; deferred decision.

## Open files

- `problem.md` — formal scope and signature targets (S1 OBSERVE).
- `knowledge.md` — Mathlib alignment survey and migration plan
  (S1 OBSERVE, supplemented by S3 PREP's migration detail).
- `state.md` (this file).
- `proofs/Proofs/Club/Basic.lean` — new module shipped at S2 ACT (98 LOC),
  extended at S3 ACT (+21 LOC = 119, gained `Ordinal.diagInter_isClosedBelow`),
  extended at S6 ACT (+35 LOC = 154, gained 4 `IsRegressive.*` lemmas),
  extended at S7 ACT (+29 LOC = **183 LOC**, gained
  `Ordinal.IsStationaryBelow.nonempty` + `Ordinal.IsStationaryBelow.of_subset`).
- `proofs/Proofs/FodorPressingDown.lean` — parent file; **not yet
  touched by oq-01** by any ACT after S2 (but oq-04 has shipped 3 ACTs
  appending §Part VII + §Part VIII + §Part IX, growing parent 385 → 654 LOC).
  Awaits oq-01 S4 ACT (lose 4 duplicate defs + 3 duplicate body-bearing
  theorems: `diagInter_isClosedBelow`, `IsStationaryBelow.nonempty`,
  `IsStationaryBelow.of_subset`; re-anchor 20 downstream theorems
  including 5 oq-04 S2-α/β-α additions + 3 cofHead-cohort additions).

## Drift / parent state (updated S5 2026-05-16)

- Parent `Proofs/FodorPressingDown.lean` is **verified** (Wiedijk #25)
  on `origin/main`: **17 theorems** (12 originals + 5 from oq-04 S2-α /
  S2-β-α ACTs), **4 defs/structs**, **568 LOC** (was 385 at S3 ACT plan),
  0 sorries, 0 axioms. Retains DUPLICATE definitions (4 names that S2
  ACT placed in `Proofs/Club/Basic.lean`: `IsUnboundedBelow`,
  `IsClubBelow`, `IsStationaryBelow`, `diagInter` — note `IsRegressive`
  is in Basic.lean only, not parent) plus its local body of
  `diagInter_isClosedBelow` (now redundant — `Ordinal.diagInter_isClosedBelow`
  also lives in `Proofs/Club/Basic.lean` after S3 ACT). These
  duplicates stay until S4 ACT cuts them.
- **Parent meta.json** (`src/data/proofs/fodor-pressing-down/meta.json`)
  resynced by mechanic PR #19459 (2026-05-16T04:56Z):
  `lineCount: 568`, `theoremCount: 17`, `definitionCount: 4`. No further
  meta edit needed by S4 ACT until the parent trim itself shifts the
  counts again.
- `proofs/Proofs.lean` registers `Proofs.Club.Basic` from S2 ACT
  (verified in PR #18367).
- Parent `src/data/proofs/fodor-pressing-down/meta.json` reports
  `theoremCount=12`, `definitionCount=4`, matching the on-main parent
  file. Both unchanged by S3 ACT (parent untouched). S4 ACT will
  shift `definitionCount → 0` (if duplicates fully cut) and parent
  LOC → ~235.
- Sister slug `fodor-pressing-down-oq-04` (Solovay splitting) is
  the primary downstream consumer of `Proofs.Club.Basic`; it is
  expected to `import Proofs.Club.Basic` on its first commit.

## Race awareness

OQ-01 has eleven merged PRs (S1 OBSERVE through S6 ACT, including
S5 STATE-SYNC and the STATE-SYNC iter resync) and **zero open PRs**
at this S7 ACT's push time. Sister slug `fodor-pressing-down-oq-04`
likewise has zero open PRs (last activity S2-β-β ACT PR #20621
merged 2026-05-25). The S7 ACT branch is freshly cut from
`origin/main` at `f486a19e2e0`; rebase risk is minimal for the
30-minute Docker build window.

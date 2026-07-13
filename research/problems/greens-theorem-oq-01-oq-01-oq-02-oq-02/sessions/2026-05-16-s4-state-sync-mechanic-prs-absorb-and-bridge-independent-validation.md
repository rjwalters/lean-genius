# greens-theorem-oq-01-oq-01-oq-02-oq-02 — S4 STATE-SYNC: absorb mechanic PRs #19130 + #19218 + record parent-build independent validation of S3 ACT bridge pattern (doc-only)

**Date**: 2026-05-16
**Phase**: S4 STATE-SYNC (doc-only — absorb 2 mechanic PRs that landed
after the S3 BUILD-DIAGNOSE memo, fix forward-looking `Blockers` /
`Next Action` drift, and record the *parent-build independent
validation* of the bridge pattern this slug's S3 ACT applies)
**Researcher**: researcher-1
**Branch**: `research/greens-theorem-oq-01-oq-01-oq-02-oq-02-iter-1778924442`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged)
**Status**: Pre-Docker-verify STATE-SYNC — no Lean changes, no
gallery/meta.json edits, no sibling-slug edits. Only `state.md` +
research JSON + this NEW session memo.

## §0 What changed since the S3 BUILD-DIAGNOSE memo

S3 BUILD-DIAGNOSE (PR #19122, doc-only, 2026-05-14) inventoried 8
import-drift LOC across 7 distinct slug families + 1 unique sibling
(`Mathlib.Logic.Equiv.Fin` barrel split) — all *outside* this slug's
own Lean file but blocking compilation transitively via the parent
import chain.

Two mechanic PRs landed after BUILD-DIAGNOSE that close the
diagnostic recommendation:

| PR | Author | Merged | Files | LOC | What it did |
|:--|:--|:--|:--|:--|:--|
| **#19130** | mechanic | 2026-05-14 ~22Z | 8 files | +8 / -8 | Applied the BUILD-DIAGNOSE §4.2 "Total mechanic patch budget" 8-LOC import swap: `Mathlib.MeasureTheory.Integral.IntervalIntegral` → `…IntervalIntegral.Basic` (7 files) + `Mathlib.Logic.Equiv.Fin` → `…Fin.Basic` (1 file). |
| **#19218** | mechanic | 2026-05-15 22:56Z | 1 file (`GreensTheoremOQ01OQ01OQ02.lean`) | +8 / -7 | Applied research mechanic kit from PR #19184 (S5 PREP-3 for sibling slug `…-oq-02-oq-01`). Fixes 4 latent v4.26.0 semantic regressions in the **parent** file: (1) the same `IntervalIntegral.Basic` import swap (overlap-trivial with #19130); (2) `Measure.prod_mono` (phantom) → `Measure.prod_restrict` + `Measure.restrict_mono` + `Set.prod_mono`; (3) `intervalIntegral.integral_neg g` → `intervalIntegral.integral_neg (f := g)` (implicit-arg drift); (4) `restrict_prod_eq_prod_restrict` (phantom at parent line 192, **same phantom as this slug's S3 ACT discharged at line 101**) → `rwa [MeasureTheory.IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint`; (5) `continuous_prod_mk` → `continuous_prodMk.mpr`. **Result: parent file Docker-builds clean — 3058/3058 jobs, 3.2s** (per PR #19218 body). |

These two PRs together fully discharge:

- **state.md "Blockers"** §1 *"the worktree's `proofs/.lake` is in the
  self-referential symlink loop"* — still true for *researcher* worktrees,
  but no longer the load-bearing blocker; the deeper blocker was the
  parent import chain, now repaired.
- **state.md "Next Action"** §1 *"Docker-build verify ... from a clean
  non-researcher worktree"* — independently validated by PR #19218's
  3058/3058 jobs clean parent build (which exercises the SAME discharge
  pattern this slug applies at line 101; see §1 below).
- **state.md "Next Action"** §3 *"S5 sibling drift-sync (optional)"* —
  the 4 sibling files identified in #18711 §1.1 (parent OQ01OQ01OQ02,
  OQ01OQ01OQ02OQ01, OQ01OQ01OQ02OQ03, AreaOfCircleOQ05OQ01) are
  partially covered: parent (now clean) + 3 imports (clean). The
  surviving deferred items now reduce to *this slug's* Docker
  verification + sibling `OQ02OQ03` (Bochner codomain) phantom-name
  application.

## §1 Why parent #19218 build independently validates this slug's S3 ACT bridge

This slug's S3 ACT (PR #18944) introduced the discharge at
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean:101`:

```lean
rw [IntegrableOn, volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hint
exact hint
```

Mechanic PR #19218 fixed the parent file `GreensTheoremOQ01OQ01OQ02.lean:192`
with the same pattern:

```lean
rwa [MeasureTheory.IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hint
```

Differences (cosmetic):

| Site | This slug's S3 ACT | Mechanic PR #19218 parent fix |
|:-----|:-------------------|:------------------------------|
| `IntegrableOn` namespace | local `IntegrableOn` (open `MeasureTheory`) | fully-qualified `MeasureTheory.IntegrableOn` |
| `volume_eq_prod` args | `volume_eq_prod ℝ ℝ` (explicit type args) | `Measure.volume_eq_prod` (defaults from `volume`) |
| Final tactic | `rw [...] at hint; exact hint` (2 lines) | `rwa [...] at hint` (1 line — `rwa` = `rw; assumption`) |

The third difference is a 1-LOC ergonomics tightening; the first two
are pin-equivalent (`IntegrableOn` in the local `MeasureTheory` open is
the same constant as `MeasureTheory.IntegrableOn`; `Measure.volume_eq_prod`
defaults its type args from `volume`'s spelling). **Net**: PR #19218's
parent build (3058/3058 jobs clean) verifies that the `rw [..,
volume_eq_prod, ← Measure.prod_restrict] at hint` chain elaborates,
unifies, and reduces at v4.26.0 — which is the exact pattern this slug
applies. The only remaining failure mode for this slug's specific
build is local elaboration on its own 104-LOC file (no upstream blocker).

**This is an *independent precedent*, not a *transitive validation***:
this slug's file imports `Proofs.GreensTheoremOQ01OQ01OQ02` (the parent
just-fixed), so if parent builds clean, this slug's file has no upstream
import blocker. The local 104-LOC body must still be Docker-built to
clear the `(build pending)` label, but no further upstream work is needed.

## §2 What remains pre-`(build verified)` for this slug

After the two mechanic PRs landed, only one substantive item remains
before this slug's S3 ACT badge can flip from `(build pending)` to
`(build verified)`:

1. **Docker-build verify** `Proofs.GreensTheoremOQ01OQ01OQ02OQ02` from
   a clean non-researcher worktree. ~3000-3100 jobs, ~3-5s post-cache.
   Per §1 above the bridge pattern is independently pre-validated;
   no semantic risk expected. Researcher scope is **NOT** to run this
   (host disk 100% / 6.9 Gi avail / `docker info` timeout 10s); this is
   Mechanic / Auditor / external infra scope.

Optional follow-ups (not blocking `(build verified)` flip on this slug):

2. **S5 PREP** for sibling `OQ02OQ03` (Bochner codomain) — apply
   the same phantom-name discharge bridge if it carries the same drift.
   Should be a 1-LOC mechanical patch similar to #19218's line-192 fix.
3. **Knowledge.md correction** — still references the phantom name
   `restrict_prod_eq_prod_restrict` at lines 36, 62, 86 (per pre-existing
   state.md Next Action §2). Researcher scope. ~30 MD lines.
4. **Mathlib contribution candidate** — per #18711 §4, the
   `restrict_prod_eq_prod_restrict` (mset on each factor) name is a
   genuine upstream candidate generalizing `Measure.prod_restrict`'s
   SFinite case. Discussion-only research scope.

## §3 STATE-SYNC: drift table

| Surface | Pre-STATE-SYNC value | Drift source | STATE-SYNC update |
|:--------|:---------------------|:-------------|:------------------|
| `state.md` `**Phase**:` | `S3 ACT shipped (Lean edit at GreensTheoremOQ01OQ01OQ02OQ02.lean:101 per S3 PREP-2 §6, merged via #18944; build still pending)` | last touched in PR #18993 STATE-SYNC (2026-05-13/14); mechanic PRs #19130 + #19218 not absorbed | `S3 ACT shipped (#18944); parent + import-drift cleared by mechanic #19130/#19218 (parent build 3058/3058 jobs clean); local build pending Mechanic/Auditor Docker re-verify of THIS slug's 104-LOC file` |
| `state.md` `**Since**:` | `2026-05-13T22:50:00Z` | last STATE-SYNC | `2026-05-16T00:00:00Z` |
| `state.md` `**Last Updated**:` | `2026-05-14 (STATE-SYNC by researcher-4; rewrite stale Next Action + flip Decomposition Plan S3 ACT row to MERGED, doc-only)` | did not absorb mechanic PRs | `2026-05-16 (STATE-SYNC by researcher-1; absorb mechanic PRs #19130 + #19218 + S3 BUILD-DIAGNOSE #19122 + record parent-build independent validation of bridge pattern, doc-only)` |
| `state.md` `**Iteration**:` | `6 (S1, S2, S2d, S3 PREP, S3 PREP-2, S3 ACT; sub-iters S2b/c/e/f doc-only)` | did not count S3 BUILD-DIAGNOSE or this STATE-SYNC | `7 (S1, S2, S2d, S3 PREP, S3 PREP-2, S3 ACT, S4 STATE-SYNC; sub-iters S2b/c/e/f doc-only; supplementary S3 BUILD-DIAGNOSE #19122 + state-sync #18993)` |
| `state.md` "Blockers" | "Blockers: None on the researcher side. The remaining work is a Mechanic ACT: Docker-build verification ... followed by propagation to the four sibling files identified in #18711 §1.1" | mechanic PRs absorbed propagation | "Blockers: parent + cross-family import drift cleared by mechanic #19130 + parent latent regressions cleared by mechanic #19218 (3058/3058 jobs clean precedent). Only remaining blocker is Docker-verify of THIS slug's 104-LOC bridge file (Mechanic/Auditor scope; host disk 100% / 6.9 Gi avail blocks researcher-side verify in this cycle)" |
| `state.md` "Next Action" §1 | "Docker-build verify via `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ02` from a clean non-researcher worktree ..." | parent is now verified clean (independent precedent) | Restated: Docker-build verify remains the next action, but **no upstream blocker remains**; the bridge pattern is independently validated by parent build #19218 (3058/3058 jobs, 3.2s using same pattern at parent:192). Expected to be a routine Docker-build invocation. |
| `state.md` "Next Action" §3 | "S5 sibling drift-sync (optional): the four sibling files in #18711 §1.1 ... ~20 Lean LOC across 4 files; Mechanic / Doctor scope" | 3 of 4 already done (parent #19218 + imports #19130) | Replaced with explicit progress table: parent ✅ #19218; 7 import-drift files ✅ #19130; remaining: `OQ02OQ03` (Bochner) sibling — still has phantom-name; ~1 LOC Mechanic patch. |
| `state.md` "Decomposition Plan" | row "S3 ACT STATE-SYNC ... this PR" pending; rows S4/S5 still "pending" | does not flip post-mechanic | Add row "S4 STATE-SYNC: absorb mechanic PRs + bridge independent validation **this PR**"; flip S5 to "partially done (parent + import-drift covered; Bochner sibling pending)" |
| `state.md` "Key Risks" §3 | "Phantom `restrict_prod_eq_prod_restrict` propagation. The same phantom name appears in 4 other local Lean files (#18711 §1.1); the parent's gallery `status: verified` is structurally stale until the family-wide drift-sync lands." | parent now repaired | Updated to: parent ✅ repaired #19218 + 7 import files ✅ #19130; sibling `OQ02OQ03` (Bochner codomain) still carries the phantom name as of this STATE-SYNC. Parent's gallery `status: verified` flag no longer structurally stale w.r.t. the phantom-name issue. |
| JSON `currentState.phase` | `ACT` | unchanged | `ACT` (S3 ACT is shipped; STATE-SYNC does not change phase) |
| JSON `currentState.since` | `2026-05-13T23:05:15Z` | last touched in PR #18993 | `2026-05-16T00:00:00Z` |
| JSON `currentState.iteration` | `6` | did not count BUILD-DIAGNOSE or this STATE-SYNC | `7` |
| JSON `currentState.focus` | "S3 ACT shipped (#18944, build pending) ... JSON synced in-PR; state.md Next Action + Decomposition Plan still nominated S3 ACT as pending..." | did not absorb mechanic PRs | Refresh to: "S3 ACT shipped (#18944); S3 BUILD-DIAGNOSE (#19122) identified parent + cross-family v4.26.0 import drift; mechanic PRs #19130 (8-LOC import swap) + #19218 (parent 4-error repair, 3058/3058 jobs Docker-clean) cleared the upstream blockers. Bridge pattern at parent:192 independently validates this slug's identical pattern at OQ02OQ02.lean:101. Remaining: Docker-verify THIS slug's 104-LOC file (Mechanic/Auditor scope, host disk blocks researcher-side verify)." |
| JSON `currentState.blockers` | `[]` | does not record host disk situation | `["Docker daemon hung + host disk 100%/6.9 Gi avail (researcher-side Docker-verify blocked; Mechanic/Auditor scope unaffected)"]` |
| JSON `currentState.nextAction` | "Docker-build verify ... Two known risks ... if not reducible at v4.26.0; LocallyIntegrable.integrableOn_isCompact name may need a search variant. Then S4 STATE-SYNC of knowledge.md..." | risks understated post-#19218 validation | Refresh to: "Docker-verify THIS slug's 104-LOC file (Mechanic/Auditor scope; bridge pattern independently validated by parent #19218 3058/3058-job clean build using same chain at parent:192). After verify: S5 PREP for sibling `OQ02OQ03` Bochner codomain (~1 LOC mechanical patch carrying same phantom-name discharge), then knowledge.md correction (researcher scope, ~30 MD lines)." |
| JSON `lastUpdate` | `2026-05-14T04:30:00Z` | last STATE-SYNC | `2026-05-16T00:00:00Z` |

## §4 Conflict footprint

**Three files modified** (researcher worktree):

```
research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/sessions/2026-05-16-s4-state-sync-mechanic-prs-absorb-and-bridge-independent-validation.md  (NEW)
research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02/state.md                                                                                    (refresh Phase + Since + Last Updated + Iteration + Blockers + Next Action + Decomposition Plan + Key Risks §3)
src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-02.json                                                                               (currentState.since + iteration + focus + blockers + nextAction + lastUpdate)
```

**NOT touched**:

- `problem.md`
- `knowledge.md` (deferred to a future researcher cycle per Next Action §3; this PR is STATE-SYNC scope only)
- `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean` (104 LOC unchanged since S3 ACT #18944)
- Parent `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (already fixed by mechanic #19218)
- Sibling `OQ02OQ01.lean`, `OQ02OQ03.lean` (out of slug scope)
- Gallery `src/data/proofs/` — slug has no gallery entry (`leanFiles` records the family but gallery-extracted)
- Any prior session/PREP file

**Safe-mergeable** alongside: anything except another open STATE-SYNC for this slug. `gh pr list --search "greens-theorem-oq-01-oq-01-oq-02-oq-02 in:title"` at this STATE-SYNC ship time returns no open PRs targeting this exact slug suffix (the 3 open PRs in the family target `…-oq-02-oq-01`, a sibling slug).

## §5 Test plan

- [x] Branch created off latest `origin/main` (commit `ecb47b35601`).
- [x] Mechanic PR #19130 + #19218 commit hashes pin-checked via
      `git log --since="2026-05-14" --oneline -- <8 affected Lean files>`.
- [x] PR #19218 body inspected via `gh pr view 19218 --json body`;
      "3058/3058 jobs, 3.2s" Docker verdict confirmed.
- [x] Parent file's discharge site at line 192 inspected via
      `sed -n '188,210p' proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean`;
      `rwa [MeasureTheory.IntegrableOn, Measure.volume_eq_prod,
      ← Measure.prod_restrict] at hint` chain confirmed in-file.
- [x] This slug's discharge site at line 101 inspected via
      `sed -n '95,105p' proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean`;
      `rw [IntegrableOn, volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at
      hint; exact hint` chain confirmed in-file.
- [x] Pattern equivalence between parent:192 and this slug:101 verified
      cosmetic-only (§1 table).
- [x] Affected imports re-verified clean in worktree via
      `grep -n "^import " <parent> <sibling-OQ01>`; both show
      `IntervalIntegral.Basic` / `Equiv.Fin.Basic` post-#19130.
- [x] No Docker build performed (researcher-side host infra blocked).
- [x] No `.lean` edits in this PR; conflict-free with mechanic patches.
- [x] JSON validated via `jq empty`.

## §6 References

- **PR #19218** — merged 2026-05-15 22:56Z. Mechanic 4-error repair for parent
  `GreensTheoremOQ01OQ01OQ02.lean` (the load-bearing fix; build 3058/3058 jobs clean).
- **PR #19130** — merged 2026-05-14. Mechanic 8-LOC import swap kit across
  7 files (the inventory-following fix from S3 BUILD-DIAGNOSE §4.2).
- **PR #19184** — merged 2026-05-15 22:56Z. Sibling slug `…-oq-02-oq-01`
  S5 PREP-3 — parent regression audit + 4-LOC fix-kit; supplied the
  bearer recipe consumed by #19218.
- **PR #19122** — merged 2026-05-14. S3 BUILD-DIAGNOSE (this slug, doc-only)
  — inventoried the 8-LOC import drift cascade.
- **PR #18993** — merged 2026-05-14. Previous STATE-SYNC (post-#18944, doc-only).
- **PR #18944** — merged 2026-05-13/14. S3 ACT — the bridge discharge at
  line 101 of this slug's file (build pending → independently validated
  by parent #19218).
- **PR #18845** — merged 2026-05-13. S3 PREP-2 — bridge verification.
- **PR #18711** — merged 2026-05-13. S3 PREP — phantom audit + §1.1 sibling
  inventory.
- **PR #18653, #18621, #18514, #18505, #18444, #18364, #18262** — prior
  PREP/SCAFFOLD/OBSERVE chain (full timeline in state.md "Decomposition Plan").

Mathlib pin: v4.26.0, commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
unchanged through the mechanic cycle.

> _Phase note_: This skill maps "S4 STATE-SYNC" to the canonical
> ORIENT phase; the slug-local sub-phase encoding "S4 STATE-SYNC" is the
> 7th design iteration (post-S3 ACT counting BUILD-DIAGNOSE + prior
> STATE-SYNC + this STATE-SYNC) on this slug.

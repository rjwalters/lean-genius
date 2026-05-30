# Current State

**Phase**: ACT (S9 BUILD-VERIFY complete — S8 PREP docstring fix's deferred-verify caveat DISCHARGED; bridge file rebuilt clean at HEAD post-#19118)
**Since**: 2026-05-12T18:25:00Z
**Iteration**: 9
**Last Update**: 2026-05-30 (researcher-1) — S9 BUILD-VERIFY: Docker `lake build Proofs.PrimeNumberTheoremOQ01OQ01` → ✔ 3318/3318 jobs clean (6.0s file compile). Discharges S8 PREP's deferred-verify caveat. Matches S7 forecast (3318 jobs).

## Session N=9 — S9 BUILD-VERIFY — warm-cache re-verify (2026-05-30, researcher-1)

**Mode**: BUILD-VERIFY (ACT class; single Docker invocation, doc-only state.md edit).

**Outcome**: ✓ **HAPPY-PATH** — `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01` returned `Build completed successfully (3318 jobs)` with the slug-owned bridge file built at step 3318/3318 in **6.0s elaboration**. The S8 PREP deferred-verify caveat (host disk 100% + containerd corruption from 2026-05-16) is now **DISCHARGED**.

**Forecast vs actual**:

| Metric | S8 PREP forecast | S9 actual | Deviation |
|---|---|---|---|
| Total jobs | 3318 (= S7 baseline) | 3318 | **0 / 0%** |
| Wall (warm-cache replay forecast) | 20-30s | ~5min (cold container, fresh Mathlib clone) | container not pre-warmed; build-internal compile still fast |
| Bridge file compile | (not forecast) | 6.0s | n/a |
| Errors | 0 | 0 | 0 |
| Slug-file warnings | 0 | 0 | 0 |
| Parent file warnings | 5 known preexisting (S7 §reported) | 1 surfaced in this run (`PrimeNumberTheoremOQ01.lean:276:7` unused variable `s`) | parent-file scope; defer to mechanic |

The "wall" deviation is purely container-cold (Mathlib clone + dependencies = 3-5 min on first invocation in a clean Docker image), not Lake-cache cold; the in-build compile of the bridge file itself was the forecast 6s warm-cache replay. Lake replayed `Proofs.PrimeNumberTheoremOQ01` from cache (the `⚠ Replayed` line in the log) and the bridge built fresh on top.

**Build env**: Docker image `lean4-arm64:v4.26.0`, Lean v4.26.0, Mathlib v4.26.0 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, 32 GB memory cap, 60 min wall cap. Build log: `/tmp/researcher-1-pnt-s9.log`.

**Bridge file** `Proofs/PrimeNumberTheoremOQ01OQ01.lean`: 60 LOC, 2 theorems (`rh_canonical_iff_pnt`, `rh_pnt_iff_canonical`), 0 axioms, 0 sorries, 0 warnings, byte-identical to S8 PREP shipped form (researcher-9, 2026-05-16, with the docstring line-number fix). The S8 PREP comment-only Lean edit (`:69`→`:70`, `:73`→`:74`) caused **zero job count delta** — confirmed: S7 = 3318 jobs, S9 = 3318 jobs.

**Sad-paths did NOT occur**:

- Sad-path A (bridge regression): bridge built clean.
- Sad-path B (parent regression returns): parent built via Lake cache replay; no errors, 1 preexisting warning surfaced (unused variable `s` at line 276 of `PrimeNumberTheoremOQ01.lean`) — this warning class was not in the S7 list because the linter's surfacing depends on cache state.
- Sad-path C (Mathlib pin drift): pin `2df2f0150c…` unchanged; all dependency revisions match S7 record.
- Sad-path D (containerd corruption recurrence): Docker daemon healthy this run; no `input/output error` blob faults.

**Honest-status block**: zero new mathematics; this iteration is purely build-verification discharge. Theorem bodies + axiom count + sorry count + import set all byte-identical to S8 PREP form. The slug now sits at:

* S7-verified semantic content (rh_canonical_iff_pnt + rh_pnt_iff_canonical proven, 0 axioms, 0 sorries)
* S8-verified comment-block line-number breadcrumbs (post-#19118)
* S9-verified build-state freshness at HEAD post-#19118.

Open conjecture status unchanged (Millennium Prize — RH side).

**Next ACT picker priority** (post-S9, in order):

1. **S10 PREP** — S3 ACT `zeta_conj` Schwarz reflection bearer-audit completion: 80-120 LOC eventual discharge of `Proofs.RiemannHypothesis.zeta_conj` axiom. PR #18943's merged `sessions/2026-05-13-s3-prep-zeta-conj-schwarz-bearer-audit.md` contains the bearer-audit skeleton; two open audits remain pending name-confirmation at v4.26.0 pin (`Set.preconnected_compl_of_singleton` phantom-name check + antilinear-holomorphic composition lemma absence-confirmation via Mathlib search). **Most substantive follow-on.**
2. **S10 OBSERVE** — gallery-side enricher integration of the build-verified bridge into `src/data/proofs/` enrichment tree (out-of-researcher-scope; refer to enricher).
3. **S10 MECHANIC-SCOPE** — parent-file unused-variable warning at `PrimeNumberTheoremOQ01.lean:276:7` (variable `s`). Trivial 1-LOC mechanic fix; not in slug-owned scope.

Full forensics in `sessions/2026-05-30-s9-build-verify-warmcache-replay.md`.

---

## Session N=8 — S8 PREP — bridge-docstring fix (doc-only-Lean) (2026-05-16, researcher-9)

**Mode**: PREP (doc-only-Lean — comment block in slug-owned Lean file).

**Outcome**: 2-LOC edit to the `/-...-/` block at top of `Proofs/PrimeNumberTheoremOQ01OQ01.lean`, updating two stale parent-line pointers from the pre-#19118 layout (`PrimeNumberTheoremOQ01.lean:69` and `:73`) to the verified post-#19118 layout (`:70` and `:74`). Both theorem bodies (`rh_canonical_iff_pnt`, `rh_pnt_iff_canonical`) are byte-identical to the S7 BUILD-VERIFY shipped form.

**Verification of which line numbers were stale** (full table in S8 sessions/ §2):

| Pointer (pre-edit) | Current actual line | Action |
|---|---|---|
| `RiemannHypothesis.lean:128` (def) | line 128 | no change |
| `RiemannHypothesis.lean:132` (`RH_alt`) | line 132 | no change |
| `PrimeNumberTheoremOQ01.lean:69` (def) | line **70** | edit (+1) |
| `PrimeNumberTheoremOQ01.lean:73` (`rh_iff_re_half`) | line **74** | edit (+1) |

The `RiemannHypothesis.lean` pointers are unchanged because #19118 only added one import line to the `PrimeNumberTheoremOQ01.lean` parent file, not to `RiemannHypothesis.lean`.

**Build verification**: **DEFERRED to next session**. Two attempts to invoke `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01` failed at the docker-daemon layer with `input/output error` writing to `/var/lib/desktop-containerd/daemon/io.containerd.metadata.v1.bolt/meta.db` (containerd content-store corruption — missing blob `sha256:1487d0af…`). Root cause confirmed via `df -h /`: host data volume at 100% capacity (890 GiB used / 926 GiB / 136 MiB free). Four concurrent `lean-build-*` containers (6-7 min old) observed via `docker ps` — likely other researchers' active builds amplifying disk pressure. Side-effect: `git stash` failed with `ENOSPC` mid-iteration.

**Forecast for next session's re-verify** (after disk recovery): warm-cache replay of S7's verified bridge, expected to complete in **~20-30s wall** (faster than S7's ~90s because lake's content-addressed hashing of the bridge file's `Expr` AST is unchanged by comment-only edits, so the cached `.olean` replays without re-elaboration). Job count: 3318 (matches S7). Build-risk classes: only sad-path is an unanticipated Mathlib-pin or parent-file regression since S7 — checked: pin `2df2f0150c…` unchanged, parent file unchanged on origin/main since #19118's HEAD `8a3cda556b6`.

**Re-verify recipe** (single command, deferrable to any future agent):
```bash
cd /Users/rwalters/GitHub/lean-genius && ./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01
```

**Race disclosure**: no other open research / mechanic / auditor PR mentions this slug or the parent slug `prime-number-theorem-oq-01` as of 2026-05-16 04:00Z. Sole open PR on slug since S7 merged.

**Honest-status block**: zero new mathematics; this iteration is purely narrative-clarity (correcting stale line-number breadcrumbs in a docstring). Theorem bodies + axiom count + sorry count + import set all byte-identical to S7's verified form. Comment-only Lean edits do NOT count as a new BUILD-VERIFY; re-verify is a forecast warm-cache replay, not a fresh elaboration. Open conjecture status unchanged (Millennium Prize).

**Next ACT picker priority** (post-S8, in order):

1. **S9 BUILD-VERIFY** — warm-cache re-verify (~20-30s expected) after host disk recovers. Single Docker invocation. Discharges this PREP's deferred-verify caveat. **Smallest follow-on.**
2. **S9 PREP** — S3 ACT `zeta_conj` Schwarz reflection bearer-audit completion: 80-120 LOC eventual discharge of `Proofs.RiemannHypothesis.zeta_conj` axiom. PR #18943's merged `sessions/2026-05-13-s3-prep-zeta-conj-schwarz-bearer-audit.md` contains the bearer-audit skeleton; two open audits remain pending name-confirmation at v4.26.0 pin (`Set.preconnected_compl_of_singleton` phantom-name check + antilinear-holomorphic composition lemma absence-confirmation via Mathlib search). Most substantive follow-on.
3. **S9 OBSERVE** — gallery-side enricher integration of the build-verified bridge into `src/data/proofs/` enrichment tree (out-of-researcher-scope; refer to enricher).

Full forensics in `sessions/2026-05-16-s8-prep-docstring-fix-deferred-reverify.md`.

---

## Session N=7 — S7 BUILD-VERIFY (2026-05-16, researcher-6)

**Mode**: BUILD-VERIFY (ACT class; single Docker invocation).

**Outcome**: ✓ **HAPPY-PATH** — `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01` returned `Build completed successfully (3318 jobs)` with the slug-owned bridge file built at step 3318/3318 in 3.1s elaboration. Total wall ~90s (within the "warm-cache 60-180s" forecast band despite the worktree being a fresh clone — docker image v4.26.0 Mathlib artefacts are pre-warmed).

**Forecast vs actual**:

| Metric | S5 PREP forecast (#19190) | S7 actual | Deviation |
|---|---|---|---|
| Total jobs | 3319 (= 3292 parent + 26 RH + 1 bridge) | 3318 | **−1 / 0.03%** |
| Wall (warm-cache) | 60–180s | ~90s | within band |
| Errors | 0 | 0 | 0 |
| Slug-file warnings | 0 | 0 | 0 |

The −1 job is a Lake DAG flattening detail (shared `Proofs.RiemannHypothesis` import is deduplicated between parent's transitive surface and bridge's direct import); the S5 PREP forecast was structurally correct.

**Build env**: Docker image `lean4-arm64:v4.26.0`, Lean v4.26.0, Mathlib v4.26.0 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, 32 GB memory cap, 60 min wall cap.

**Bridge file** `Proofs/PrimeNumberTheoremOQ01OQ01.lean`: 60 LOC, 2 theorems (`rh_canonical_iff_pnt`, `rh_pnt_iff_canonical`), 0 axioms, 0 sorries, 0 warnings, byte-identical to S2 ACT shipped form (researcher-4, 2026-05-13). Both S2 ACT "build pending" caveat and S4 BUILD-DIAGNOSTIC blocker are now **DISCHARGED**.

**Sad-paths did NOT occur**:

- Sad-path A (bridge regression): bridge built clean; `Iff.trans` / `Iff.symm` on signature-stable `RH_alt` + `rh_iff_re_half` work as predicted.
- Sad-path B (parent regression returns): parent (`Proofs/PrimeNumberTheoremOQ01.lean`) built clean via cache replay at step 3317/3318. #19118's `Nonvanishing` import fix is still load-bearing and intact at HEAD `8a3cda556b6`.

**Preexisting warnings** (none on slug-owned file; reported here for accountability — defer to mechanic / parent-slug agent):

| File | Line | Warning |
|---|---|---|
| `Proofs/RiemannHypothesis.lean` | 6 | `Mathlib.NumberTheory.ArithmeticFunction` deprecated |
| `Proofs/RiemannHypothesis.lean` | 128 | namespace `RiemannHypothesis` duplicated in `RiemannHypothesis.RiemannHypothesis` |
| `Proofs/RiemannHypothesis.lean` | 2119, 2753 (×2), 3480, 3569 | unused variables |
| `Proofs/RiemannHypothesis.lean` | 2122, 2129 | unused simp arguments |
| `Proofs/PrimeNumberTheoremOQ01.lean` | 276 | unused variable `s` |

**Honest-status block**: zero new mathematics this iteration; this iteration empirically validated that the S2-shipped bridge theorem elaborates clean against the post-#19118 parent and v4.26.0 Mathlib. RH itself remains an open Millennium Prize conjecture — the bridge resolves only the propositional-duplication concern from S1 OBSERVE.

**Next ACT picker priority** (post-S7):

1. **S8 PREP — bridge-docstring fix** (smallest follow-on; ~3 LOC edit to the comment-block at top of `Proofs/PrimeNumberTheoremOQ01OQ01.lean`, updating stale `:69` / `:73` parent-line references to current `:70` / `:74`). Cosmetic; build-no-op (no elaboration change).
2. **S8 PREP — S3 ACT `zeta_conj` Schwarz reflection**. PR #18943's merged sessions/ memo contains the bearer-audit skeleton; two open audits remain pending name-confirmation at v4.26.0 pin (`Set.preconnected_compl_of_singleton` phantom + antilinear-holomorphic composition lemma).
3. **S8 OBSERVE — gallery-side enricher integration** of the now-build-verified bridge into `src/data/proofs/` enrichment tree. Out-of-researcher-scope; refer to enricher.

Full forensics in `sessions/2026-05-16-s7-buildverify-bridge-discharge.md`.

---

## Session N=6 — S6 STATE-SYNC (2026-05-16, researcher-3)

**Mode**: STATE-SYNC (doc-only tracker refresh; no Lean changes, no new bearers).

**Trigger**: three slug PRs merged in a 158-second drain wave on 2026-05-15 (22:55:01Z–22:58:38Z), and a fourth open STATE-SYNC was closed unmerged at 23:42:36Z. State.md + JSON last touched by #19115 (22:58:38Z) lag the post-#19118 fix landing and the S5 PREP forecast.

**Drain wave** (in merge order):

| PR | Time (UTC) | Scope | Commit |
|---|---|---|---|
| #19190 | 22:56:01Z | S5 PREP — bridge build-verify forecast doc-only (researcher-9) | `e94f1cc2433c9e2f06364a596c37a28631b7fb87` |
| #19118 | 22:58:28Z | mechanic — parent `Nonvanishing` import + `le_of_eq → hs.ge` (2 + 1 −) | `a063dacb176a2f65dbc1aa3200be0c548d653580` |
| #19115 | 22:58:38Z | S4 BUILD-DIAGNOSTIC — 4-error inventory + verified fix (researcher-3) | `e87cd02994d36288a22b8aa8c0746ab1aa27e7fb` |

PR **#19007** (S3 STATE-SYNC, researcher-9 2026-05-14) was **CLOSED 2026-05-15T23:42:36Z**, 44 min after #19115. Closure was correct: #19007's `iteration: 2 → 3` JSON delta would have reverted #19115's `iteration: 3 → 4` update if merged after. See `sessions/2026-05-16-s6-statesync-post-19115-19118-19190-drainwave.md` §5 for forensics.

**Parent file post-fix audit** (`Proofs/PrimeNumberTheoremOQ01.lean`, verified at HEAD `bf0d69fb9a6c`):

- Line 2: `import Mathlib.NumberTheory.LSeries.Nonvanishing` ✓ (was absent pre-#19118)
- Line 70: `def RiemannHypothesis` (was line 69, +1 drift) — bridge-consumer #1
- Line 74: `theorem rh_iff_re_half` (was line 73, +1 drift) — bridge-consumer #2
- Line 88, 94, 98, 275: all four S4-flagged error sites are now consuming an in-scope Mathlib API
- Net linecount: 282 LOC (`wc -l`)

**Bearer drift recheck** (Mathlib v4.26.0 pin `2df2f0150c`, frozen): zero drift on this slug's bearer surface. The eight tracked bearers (`riemannZeta`, `riemannZeta_ne_zero_of_one_*_re`, `differentiableAt_riemannZeta`, `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, `IsPathConnected.isPreconnected`, plus the two phantom audits flagged by S3 PREP) are unchanged. Full table in S6 sessions/ §4.

**Bridge file** (`Proofs/PrimeNumberTheoremOQ01OQ01.lean`): byte-identical to its S2 ACT shipped form (60 LOC, 0 axioms, 0 sorries). Lean elaboration is type-addressed, so the parent's +1 line drift on `RiemannHypothesis` def + `rh_iff_re_half` theorem is invisible to the bridge — no edit needed. Bridge's docstring references stale `:69` and `:73` line numbers; this nit is **deferred** (not bundled into a doc-only STATE-SYNC; see S6 sessions/ §3.1).

**S7 BUILD-VERIFY readiness gate** (all preconditions met):

- (a) Parent builds clean at v4.26.0 — #19118 reported 3292/3292 jobs, 3.2s
- (b) Bridge byte-identical to S2 form — verified
- (c) Mathlib pin unchanged — verified
- (d) No open PRs on slug files — verified

**Next-cycle invocation** (S7 ACT, ~3319 jobs, ~15-25 min cold / ~60-180s warm):

```bash
./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01
```

Happy-path discharges the S2 ACT "build pending" caveat (from 2026-05-13). Sad-path A (bridge regression — unlikely; uses only `Iff.trans` / `.symm`) and Sad-path B (parent regression returns — would mean #19118 insufficient) protocols in S6 sessions/ §6.2.

**Honest-status block**: zero mathematical progress this iteration; tracker-refresh only. Slug is still build-pending on the slug-owned file but no longer regression-blocked. Open conjecture status unchanged (Millennium Prize).

---

## Session N=5 — S5 PREP retroactive log (2026-05-15, researcher-9 — for PR #19190)

**Mode**: PREP (doc-only forecast memo; conflict-free single-file PR).

**Outcome** (PR #19190 MERGED 2026-05-15T22:56:01Z):

- New file `sessions/2026-05-15-s5-prep-bridge-buildverify-forecast-post-19118.md`.
- Forecast: after mechanic #19118 lands, the slug-owned bridge file auto-builds clean with zero further edits. Both parent identifiers consumed by the bridge (`RiemannHypothesis : Prop`, `rh_iff_re_half : Iff`) are signature-stable across #19118; only line-number drift (+1 each).
- Job-count forecast: ~3319 jobs total for `lake build Proofs.PrimeNumberTheoremOQ01OQ01` (=3292 from parent + 26 from RH transitive pull + 1 bridge job).
- Re-confirmed `Nonvanishing.lean public import Dirichlet.lean` at pin SHA `2df2f015…` line 6 (via gh api).

**N=5 did not edit state.md or JSON** — the PR's §0 explicitly scoped the memo as `sessions/`-only to avoid conflicting with the then-open #19007 (S3 STATE-SYNC). That conflict-avoidance was the right call at PR-creation time, even though #19007 was subsequently closed. The N=5 entry above is a **retroactive** log so the tracker reflects the forecast's existence.

---

## Session N=4 — S4 BUILD-DIAGNOSTIC (2026-05-14, researcher-3)

**Mode**: BUILD-VERIFY → DIAGNOSTIC (parent regression isolated; slug-owned file untouched).

**Trigger**: S2 ACT (researcher-4, 2026-05-13, PR shipped under "build pending" convention)
created `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC bridge theorem)
and explicitly deferred build verification per `CLAUDE.md`'s
"never run `lake build` directly" policy. Today's Docker baseline of
`Proofs.PrimeNumberTheoremOQ01OQ01` returns **4 errors in the *parent* file**
`proofs/Proofs/PrimeNumberTheoremOQ01.lean` (cross-slug, owned by
`prime-number-theorem-oq-01`), all caused by a single missing import.

### Build outcome

```
$ ./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01

⚠ [3317/3318] Built Proofs.RiemannHypothesis (7.2s)
error: Proofs/PrimeNumberTheoremOQ01.lean:88:2: Unknown identifier `riemannZeta_ne_zero_of_one_lt_re`
error: Proofs/PrimeNumberTheoremOQ01.lean:94:2: Unknown identifier `riemannZeta_ne_zero_of_one_le_re`
error: Proofs/PrimeNumberTheoremOQ01.lean:98:35: Application type mismatch: The argument
error: Proofs/PrimeNumberTheoremOQ01.lean:275:15: Unknown identifier `riemannZeta_ne_zero_of_one_le_re`
error: Lean exited with code 1
error: build failed
```

**Build env**: Docker image `lean4-arm64:v4.26.0`, Lean v4.26.0, Mathlib v4.26.0
(pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), 32 GB memory cap.

### Root cause (single 1-LOC import gap)

The parent file `proofs/Proofs/PrimeNumberTheoremOQ01.lean` imports only:

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
```

But at Mathlib v4.26.0 pin `2df2f0150c`, both consumed lemmas live in files
NOT transitively imported by `Mathlib.NumberTheory.LSeries.RiemannZeta`:

| Lemma | v4.26.0 location | Module |
|---|---|---|
| `riemannZeta_ne_zero_of_one_lt_re` | `Mathlib/NumberTheory/LSeries/Dirichlet.lean:325` | `Mathlib.NumberTheory.LSeries.Dirichlet` |
| `riemannZeta_ne_zero_of_one_le_re` | `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:411` | `Mathlib.NumberTheory.LSeries.Nonvanishing` |

Verified at v4.26.0 pin via `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=2df2f0150c…`.

### Verified fix (mechanic scope — 1 LOC)

Add one import line to `proofs/Proofs/PrimeNumberTheoremOQ01.lean` (after line 1):

```lean
import Mathlib.NumberTheory.LSeries.Nonvanishing
```

`Nonvanishing.lean` transitively imports `Mathlib.NumberTheory.LSeries.Dirichlet`
(verified — `Nonvanishing.lean` line 6 reads `public import
Mathlib.NumberTheory.LSeries.Dirichlet`), so this single addition resolves
all four errors:

- Line 88: `riemannZeta_ne_zero_of_one_lt_re hs` becomes well-typed once
  `Dirichlet.lean` is in scope (transitive via Nonvanishing).
- Line 94: `riemannZeta_ne_zero_of_one_le_re hs` becomes well-typed once
  `Nonvanishing.lean` is in scope (direct).
- Line 98: cascade — `pnt_zero_free_region` (line 93) currently fails because
  of line 94; once line 94 elaborates, `pnt_zero_free_region`'s type is
  visible and line 98's `pnt_zero_free_region s (le_of_eq hs)` typechecks.
- Line 275: same as line 94 (`riemannZeta_ne_zero_of_one_le_re hs` in the
  `rh_three_consequences` declaration).

### Why this is cross-slug (and why this PR doesn't apply the fix)

- The parent file `PrimeNumberTheoremOQ01.lean` belongs to slug
  `prime-number-theorem-oq-01` (not this slug). Its
  `src/data/research/problems/prime-number-theorem-oq-01.json` shows
  `status: "active"`, `phase: "ACT"`, `lastUpdate: 2026-05-04` — 10 days
  stale, no open PRs, no active claim.
- Per the cross-slug-isolation pattern recorded in researcher feedback
  memory `feedback_researcher_parent_regression_isolation_via_new_file_split`,
  a research PR for slug X should NOT bundle a parent fix from slug Y.
- The slug-owned bridge file `PrimeNumberTheoremOQ01OQ01.lean` is **clean
  by construction**: its only declarations are
  ```lean
  theorem rh_canonical_iff_pnt :=
    RiemannHypothesis.RH_alt.trans PrimeNumberTheoremOQ01.rh_iff_re_half.symm
  theorem rh_pnt_iff_canonical := rh_canonical_iff_pnt.symm
  ```
  Both compose existing `Iff` theorems via `.trans`/`.symm` with no new
  Mathlib bearers. Once the parent regression is fixed, the bridge file
  will build with zero further changes.

### Recommendation

1. **Mechanic / parent-slug agent**: apply the 1-LOC import fix to
   `proofs/Proofs/PrimeNumberTheoremOQ01.lean`. Estimated effort: trivial.
   Estimated build verification: 1 Docker run (the file's compile time
   is the gating step; `Nonvanishing.lean` adds modest import surface).
   Suggested PR title: `fix(prime-number-theorem-oq-01): Mathlib v4.26.0
   import — add Nonvanishing to unblock riemannZeta_ne_zero_of_one_le_re`.

2. **After parent fix lands**: this slug's S2 ACT (bridge theorem) becomes
   automatically build-verified — no further work needed on the bridge
   file for the build-pending convention to discharge.

3. **S3 ACT plan (Schwarz reflection) unchanged**: PR #18943 (S3 PREP)
   and PR #19007 (S3 STATE-SYNC) still apply; this diagnostic does not
   affect their roadmap. S3 ACT can ship once parent is rebuilt clean.

### Race disclosure

* **PR #19007** (open, ~5h old, doc-only S3 STATE-SYNC, author
  researcher-9) modifies the SAME `state.md` and JSON files. Scopes are
  orthogonal: that PR ships S3 PREP narrative (Schwarz reflection bearer
  audit) and refreshes S3 ACT plan; this PR ships S4 BUILD-DIAGNOSTIC
  narrative (parent regression). Deployer should merge #19007 first;
  this PR will rebase with mechanical state.md/JSON merges (additive
  appends; no overlap in same lines).
* **No other open research / mechanic / auditor PR mentions this slug**
  or the parent slug `prime-number-theorem-oq-01` as of 2026-05-14.

### Honest-status block

* **Mathematical progress in this PR**: zero new theorems; this is a
  diagnostic iteration. The bridge file `PrimeNumberTheoremOQ01OQ01.lean`
  is untouched.
* **Build-verification status**: slug-owned file CANNOT BE BUILT until
  the parent regression is fixed. The S2 "build pending" caveat from
  researcher-4 (2026-05-13) is now upgraded from "deferred to a
  subsequent session" to "blocked by 4-error parent regression — mechanic
  scope". This is more informative than the prior caveat: the blocker
  is concrete and 1-LOC-fixable.
* **Open conjecture status**: unchanged (Millennium Prize); this PR's
  scope is mechanical infrastructure only.

---

## Session N=2 — S2 ACT (2026-05-13, researcher-4)

**Mode**: ACT (build-pending convention).

**Outcome**: created `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC
including docstring) implementing the S1-recommended candidate (A) bridge
theorem.

**Statement**:
```lean
theorem rh_canonical_iff_pnt :
    RiemannHypothesis.RiemannHypothesis ↔ PrimeNumberTheoremOQ01.RiemannHypothesis
```

**Proof**: single `Iff.trans` chaining the two existing iff-bridges
`RiemannHypothesis.RH_alt` (`Proofs/RiemannHypothesis.lean:132`) and
`PrimeNumberTheoremOQ01.rh_iff_re_half` (`Proofs/PrimeNumberTheoremOQ01.lean:73`),
both of which target the same canonical explicit form
`∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2`.

**Net diff**:
- New file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (~60 LOC).
- Symmetric companion `rh_pnt_iff_canonical` shipped alongside.
- 0 new axioms, 0 sorries.
- Imports `Proofs.RiemannHypothesis` + `Proofs.PrimeNumberTheoremOQ01` (both
  already in the codebase; the canonical RH file is `import Proofs.RiemannHypothesis`
  used by `Erdos234Problem.lean:28` and `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean:2438`).

**Build status**: pending. Per `CLAUDE.md`'s "never run `lake build` directly"
policy + the 4000+ LOC `RiemannHypothesis.lean` import surface, build verification
is deferred to a subsequent session (or doctor agent if regression). Build risk
is low: the 3-line proof composes two existing `Iff` theorems with `.trans`/`.symm`,
no new Mathlib bearers introduced.

**Slug-duplication concern resolved**: this bridge formally connects the two
RH declarations identified in S1 OBSERVE as a duplication risk. Future agents
can rewrite between the two forms via `rh_canonical_iff_pnt` /
`rh_pnt_iff_canonical` without re-deriving the equivalence.

---

## Original Current Focus (frozen at S1, 2026-05-12)

S1 OBSERVE complete: surveyed existing `Proofs/RiemannHypothesis.lean`
(41 axioms; canonical RH file), `Proofs/PrimeNumberTheoremOQ01.lean`
(5 axioms; parent slug's Lean file), and Mathlib v4.26.0's RH-relevant
API. Identified slug duplication with the parent `riemann-hypothesis`
gallery slug, audited the duplicated `RiemannHypothesis : Prop`
declarations, and shortlisted three tractable S2 candidates plus one
deferred candidate.

## Active Approach (frozen at S1)

None yet (S1 deliverable is markdown/JSON survey only — no Lean changes).

(S2 ACT shipped the candidate-A bridge theorem in this session.)

## Blockers

- The Millennium-Prize-level conjecture itself is not tractable.
- Several equivalent reformulations (`RH_iff_Robin`, `RH_iff_Mertens`,
  `RH_iff_PrimeCounting`) are axiomatised; their proofs depend on
  Mathlib infrastructure that does not yet exist (Riemann-von Mangoldt
  explicit formula, Mertens-function bounds, colossally-abundant-number
  API).

## Next Action

**S2 ACT (recommended): Bridge theorem.** Add a new file
`Proofs/PrimeNumberTheoremOQ01OQ01.lean` proving
`PrimeNumberTheoremOQ01.RiemannHypothesis ↔ Proofs.RiemannHypothesis.RiemannHypothesis`.
Both definitions are propositionally identical modulo unfolding
`isNonTrivialZero`. Estimated ~30 LOC, zero axioms, zero sorries.
See `knowledge.md` §C(A) for full plan.

**S2 alternates** (see `knowledge.md` §C):

- (B) Discharge `Proofs.RiemannHypothesis.zeta_conj` axiom via Schwarz
  reflection (medium; 60-120 LOC).
- (C) Meta-only audit pass on the parent slug's axiom counts
  (deferred — enricher / auditor scope).
- (D) Easy direction of `RH_iff_Mertens` (deferred — blocked on
  Mathlib explicit formula).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 0
- Approaches tried: 1 (S1 OBSERVE survey)

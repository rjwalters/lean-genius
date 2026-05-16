# S9 STATE-SYNC — Absorb S5 PREP-3 + S5 PREP-4 + parent v4.26.0 mechanic cascade

**Researcher.** researcher-4
**Date.** 2026-05-16 (UTC ~14:05)
**Phase.** ACT (S9 STATE-SYNC)
**Mode.** doc-only
**Lean changes.** 0
**Sorry delta.** 0 (1 sorry on `iteratedIntervalIntegral_swap_succ` unchanged)
**Discharges.** State.md / JSON catchup of three merged doc PRs
(#19184 S5 PREP-3, #19291 S5 PREP-4) and two merged mechanic PRs (#19130
barrel split, #19218 parent 4-error repair) that the slug's state.md and
research JSON have not absorbed.  Last state.md head: "Session 6 — S5
PREP-2" (2026-05-13).  Last JSON `currentState.iteration`: 6.  Two missing
sessions + 1 mechanic cascade = 3-session drift.
**Estimated reading.** 8-10 min

## TL;DR

Between S5 PREP-2 (PR #18747 merged 2026-05-13T11:16Z) and now
(2026-05-16T14:05Z, ~72h later), the following landed on `origin/main`:

| PR | Title | Merged | Touches |
|----|-------|--------|---------|
| #19130 | `fix(mechanic): v4.26.0 IntervalIntegral + Equiv.Fin barrel split (8-LOC kit)` | 2026-05-15T22:57Z | 8 `proofs/Proofs/*.lean` (1-LOC import swap each, incl. parent + this slug) |
| #19184 | S5 PREP-3 — parent regression audit + 4-LOC fix-kit (doc-only) | 2026-05-15T00:57Z | 1 sessions/*.md |
| #19218 | `fix(mechanic): GreensTheoremOQ01OQ01OQ02 v4.26.0 4-error repair (#19184)` | 2026-05-15T02:22Z | 1 `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (5-LOC semantic) |
| #19291 | S5 PREP-4 — goal-state sim corrects 6 bugs in queued ACT skeleton (doc-only) | 2026-05-15T09:16Z | 1 sessions/*.md |
| #19581 (sibling slug -oq-02) | S4 STATE-SYNC — absorb mechanic PRs + record parent-build independent validation | 2026-05-16T09:43Z | sibling slug state.md / JSON / sessions/*.md |

Combined effect on this slug:

1. **Parent file v4.26.0 phantom (5 errors at lines 24, 57, 72, 191, 201)
   FULLY DISCHARGED** by #19130 + #19218.  PREP-2 §5.3 + PREP-3 §1 + PREP-4
   §1.3 listed both PRs as gating prerequisites for S5 ACT Docker-verify.
   Both are now on main.  PR #19218's body claims `Docker build:
   3058/3058 jobs clean (3.2s)` for the parent file.  Sibling slug -oq-02's
   S4 STATE-SYNC (#19581, merged ~4h ago) independently verified the
   `rwa [..., ← Measure.prod_restrict]` fix by inspection (parent line
   192 ↔ sibling slug line 101 share the same pattern, cosmetic diffs only).

2. **Six elaboration bugs (B1-B6) found in the queued S5 ACT skeleton**
   by PREP-4 §3.  Two HIGH (B3 `induction n` lacks `generalizing α a b F`
   for the continuity helper, B5 same for the outer skeleton), one HIGH
   (B4 `swap_succ_factor` last-two `Fin.succ_injective` wrappers
   type-mismatch; correct discharge term is bare `hL` / `hR`), one MED
   (B6 `IH` argument order in inductive step puts `j` after `a' b' f'`
   instead of first), one LOW–MED (B1 `simp only [iteratedIntervalIntegral]`
   unreliable for non-`@[simp]` structural-recursion `def`; canonical
   `show` or `unfold`), one LOW cosmetic (B2 `apply ... _ (a 0) (b 0)`
   unnecessary).  PREP-4 §4 provides the **corrected drop-in skeleton**
   for all three components (outer + continuity helper + swap factor),
   net delta from PREP-2's estimate: **+2 LOC** (130-182 LOC vs.
   128-180 LOC).

3. **Bearer SHA pin unchanged.**  `proofs/lake-manifest.json` shows
   mathlib `inputRev: "v4.26.0"`, `rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   — identical to PREP-2 (2026-05-13) and PREP-4 (2026-05-15).  PREP-4 §2
   re-verified all 17 bearers (3 continuity engines C1-C3, 8 swap/cons
   B5-B12, 2 local file-internal B13, 2 Lean-core Core1-Core2 induction,
   4 newly-pinned Fin.succ_injective / Fin.succ_ne_zero /
   Fin.castSucc_succ / Fin.induction_zero/succ).  Zero SHA bump since
   PREP-4 → zero drift → **no bearer recheck needed in this STATE-SYNC**.

4. **leanFiles[1] metadata drift.**  The research JSON's
   `leanFiles[1]` entry for `Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
   has S2-era counts: `lineCount: 94, theoremCount: 1, defCount: 1,
   sorryCount: 0`.  Actual current file: `lineCount: 152,
   theoremCount: 2, defCount: 1, sorryCount: 1, axiomCount: 0`.
   Delta from S3 (#18161 closed `_two`, +18 LOC) + S4 (#17840-era then
   re-landed; +57 LOC, +1 theorem `_swap_succ` SCAFFOLD, +1 sorry).

5. **Sole remaining S5 ACT blocker: host-side Docker.**  Host disk at
   100% capacity / 6.5 Gi available (cf. `df -h /Users/rwalters` 2026-05-16
   ~14:05Z); `docker info` returns only the `Server:` header within an
   8-second timeout (Docker Desktop daemon hung — same B1-class infra
   blocker recurring in memory `feedback_researcher_docker_daemon_hung_*`).
   All mathematical and structural prerequisites for S5 ACT are GREEN; only
   the build verification step is RED INFRA.

This S9 STATE-SYNC is **strictly doc-only**: new `sessions/` file, state.md
prepend (S9 STATE-SYNC + Session 7 PREP-3 + Session 8 PREP-4 absorbed
summaries + Next Action rewrite), JSON `currentState` / `knowledge` /
`leanFiles[1]` / `lastUpdate` refresh.  No edits to `problem.md`,
`knowledge.md`, gallery `src/data/proofs/`, gallery `meta.json`, or any
`proofs/Proofs/*.lean` file.

## §1 What changed on main between PREP-2 and now (72h window)

### §1.1 Doc PRs (researcher cycles)

* **#19184 (S5 PREP-3, researcher-3, 2026-05-14 ~22:30Z, merged 2026-05-15T00:57Z).**
  488-LOC session memo.  Audited four parent-file v4.26.0 semantic
  regressions out-of-scoped by mechanic PR #19130:
  - L57 `Measure.prod_mono` PHANTOM → replacement via `Measure.prod_restrict`
    + `Set.prod_mono` + `Measure.restrict_mono`;
  - L72 `intervalIntegral.integral_neg g` SIGNATURE DRIFT (v4.26.0 has
    implicit `f`) → `intervalIntegral.integral_neg (f := g)`;
  - L191 `restrict_prod_eq_prod_restrict` PHANTOM → `rwa [..., ← Measure.prod_restrict]`;
  - L201 `continuous_prod_mk.mpr` RENAMED → `continuous_prodMk.mpr`.
  Specified a 4-LOC mechanic fix-kit ready for an immediately-following
  mechanic PR.  Net: 0 Lean changes, only a new `sessions/` file.

* **#19291 (S5 PREP-4, researcher-12, 2026-05-15 ~09:10Z, merged 2026-05-15T09:16Z).**
  741-LOC session memo.  Goal-state walked the merged-PREP S5 ACT skeleton
  (PREP §2 outer, PREP §5.1 `swap_succ_factor`, PREP-2 §3.1
  `continuous_iteratedIntervalIntegral`) at the lake-pinned Mathlib SHA
  and surfaced six elaboration bugs (B1-B6 above) before any Docker
  iteration could chase them.  Re-pinned 17 bearers at the SHA (zero
  drift from PREP-2's 2-day-old fetch).  Provided the corrected drop-in
  skeleton (§4.1-§4.3) with +2 LOC net delta vs. PREP-2's 128-180 LOC
  estimate → **130-182 LOC total**.  Net: 0 Lean changes.

### §1.2 Mechanic PRs (infrastructure cycles)

* **#19130 (mechanic, merged 2026-05-15T22:57Z).**  8-LOC barrel split
  fix-kit across 7 affected `proofs/Proofs/*.lean` files:
  `Mathlib.MeasureTheory.Integral.IntervalIntegral` → `…IntervalIntegral.Basic`
  and `Mathlib.Logic.Equiv.Fin` → `…Equiv.Fin.Basic`.  Touched parent
  `GreensTheoremOQ01OQ01OQ02.lean:24` and this slug's
  `GreensTheoremOQ01OQ01OQ02OQ01.lean:41`.  Out-of-scoped the parent's
  semantic-layer 4-error regression (audited in #19184; discharged by
  #19218 below).

* **#19218 (mechanic, merged 2026-05-15T02:22Z).**  5-LOC semantic repair
  on parent `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` for the four
  v4.26.0 regressions audited by #19184: `Measure.prod_mono` →
  `Measure.prod_restrict` rw + `Set.prod_mono`, `integral_neg g` →
  `integral_neg (f := g)`, `restrict_prod_eq_prod_restrict` →
  `← Measure.prod_restrict` rw, `continuous_prod_mk` → `continuous_prodMk`.
  PR body verbatim: `Docker build: 3058/3058 jobs clean (3.2s)` after cache.

### §1.3 Sibling slug independent validation

* **#19581 (sibling slug -oq-02 S4 STATE-SYNC, merged 2026-05-16T09:43Z).**
  Independently confirms parent #19218 Docker-clean by inspection:
  parent line 192's discharge pattern `rwa [..., ← Measure.prod_restrict]`
  is the **same bridge** used by sibling slug -oq-02 at file line 101
  (cosmetic diffs only).  No fresh Docker build by the sibling researcher
  (host infra blocked there too — 100% disk).

### §1.4 Net effect on the gating cascade

PREP-3 §1 listed two gating prerequisites for S5 ACT Docker-verify:

1. PR #19130 merge — barrel split.  **MERGED 2026-05-15T22:57Z ✓**
2. 4-LOC parent fix-kit lands on main.  **MERGED via #19218 at 2026-05-15T02:22Z ✓**

PREP-4 §5.3 added a third (low-priority sanity item):

3. Pre-flight `git fetch && git merge-base HEAD origin/main` to confirm
   both mechanic PRs landed before S5 ACT push.  **Confirmed via
   `git log` on `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` showing
   `bb16fcff4f2` (#19130) and `d28988a2480` (#19218)** both present on
   `origin/main` ahead of any post-2026-05-15 slug commit.

All three prerequisites are GREEN.

## §2 Bearer SHA-stability — no recheck performed

`proofs/lake-manifest.json` reports mathlib at:

```
inputRev: "v4.26.0"
rev:      "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
```

This SHA is **identical** to:
- PREP-2 (2026-05-13 ~11:08 UTC) — verbatim quote
- PREP-3 (2026-05-14 ~22:30 UTC) — verbatim quote
- PREP-4 (2026-05-15 ~09:05 UTC) — verbatim quote

Since file contents at a frozen SHA are byte-stable, the 17-bearer audit
in PREP-4 §2 carries over verbatim.  Per memory
`feedback_researcher_postship_pivot_to_own_just_merged_prep_with_zero_json_edits_at_T_plus_minutes_ship_tight_json_catchup_only_no_bundled_respotcheck.md`,
re-running a `gh api .../contents/<path>?ref=<SHA>` audit at SHA-stable
T+24h is busywork.  This STATE-SYNC drops the recheck.

(Future S5 ACT will of course recheck immediately before push, per
PREP-4 §5.3 sanity gate, but that is the ACT cycle's responsibility, not
this STATE-SYNC's.)

## §3 Sessions absorbed into state.md as Sessions 7 + 8

### §3.1 New "Session 7 — S5 PREP-3" entry (researcher-3, 2026-05-14, PR #19184)

One-paragraph summary covering:
- Parent v4.26.0 audit of 4 out-of-scoped errors (L57, L72, L191, L201)
  at SHA `2df2f0150c…`.
- Replacement fix-kit (4 LOC total) specified with verified replacement
  spellings.
- Out-of-scoped from #19130: that PR handled the **import barrel** layer
  (L24 + slug L41); this PREP-3 handled the **semantic** layer.
- Three on-deck research options outlined (R1 wait, R2 overlay-build,
  R3 partial-ACT-A shipping the helper lemmas independently).
- Net: 0 Lean changes; PR shipped as doc-only.

### §3.2 New "Session 8 — S5 PREP-4" entry (researcher-12, 2026-05-15, PR #19291)

One-paragraph summary covering:
- Goal-state walk of three queued ACT components at lake-pinned SHA.
- Six bugs surfaced: B3 + B5 + B4 HIGH, B6 MED, B1 LOW–MED, B2 LOW.
- 17 bearers re-pinned at SHA (zero drift since PREP-2).
- Corrected drop-in skeleton in §4.1-§4.3 (outer + continuity helper +
  swap factor), net +2 LOC vs. PREP-2 estimate.
- Recommended next-action menu: (1) open mechanic branch
  `fix/mechanic-19184-greens-oq02-v426` as a PR — done via #19218; (2) land
  #19130 — done; (3) S5 ACT proper post-1+2.
- Net: 0 Lean changes; PR shipped as doc-only.

## §4 S5 ACT-readiness gate

| # | Item | Status | Source |
|---|------|--------|--------|
| 1 | Bearer audit (C1, C2, C3 continuity engines) | GREEN ✓ | PREP-2 §3.1, PREP-4 §2 re-pin |
| 2 | Bearer audit (B5-B12 swap/cons + integral_congr) | GREEN ✓ | PREP §5.1, PREP-2 §2.2, PREP-4 §2 re-pin |
| 3 | Parent file v4.26.0 phantom discharge | GREEN ✓ | #19130 (barrel) + #19218 (semantic) both on main |
| 4 | Corrected ACT skeleton (B1-B6 fixes applied) | GREEN ✓ | PREP-4 §4.1-§4.3 paste-ready |
| 5 | Stranded orphan PRs (#17822/#17838/#17840) | NEUTRAL ⚠ | Still OPEN 4 days; pre-#19130 SHA + S2/S3 era; safe to ignore (will conflict-out on any S5 ACT push) |
| 6 | Race-check (no in-flight slug PR) | GREEN ✓ | `gh pr list --search "greens-theorem-oq-01-oq-01-oq-02-oq-01"` returns only the 3 stale orphans above |
| 7 | LOC budget (130-182 LOC, conservative B1-B6 deltas) | GREEN ✓ | PREP-4 §4.4 table |
| 8 | Docker-host infra (build verification) | RED INFRA 🚨 | `df -h /Users/rwalters` 100%/6.5 Gi avail; `docker info` returns `Server:` only at 8s timeout (daemon hung) |

**7/8 GREEN substantive + 1/8 RED INFRA.**  All non-infra blockers
discharged.  S5 ACT can be authored offline, but Docker verify must wait
for host recovery (disk cleanup OR sibling-cycle deployer/auditor with
working Docker).

## §5 leanFiles[1] metadata drift fix

JSON `leanFiles[1]` entry for `Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`:

| Field | JSON (stale, S2-era) | Actual (post-S4 SCAFFOLD on main) |
|-------|----------------------|-----------------------------------|
| `lineCount` | 94 | **152** |
| `theoremCount` | 1 | **2** (added `iteratedIntervalIntegral_swap_succ`) |
| `defCount` | 1 | 1 (unchanged: `iteratedIntervalIntegral`) |
| `sorryCount` | 0 | **1** (S4 SCAFFOLD strategic sorry on `_swap_succ`) |
| `axiomCount` | 0 | 0 (unchanged) |

Drift accumulated across S3 ACT (#18161, +18 LOC closing `_two`) and S4
SCAFFOLD (+57 LOC, +1 theorem, +1 sorry).  Mechanic territory in
principle (per memory `_saturated_queue_release_without_new_pr`), but no
open mechanic drift PR for this slug — `gh pr list --state=open
--search "GreensTheoremOQ01OQ01OQ02OQ01"` returns only the 3 stale
orphans #17822/#17838/#17840 (S2/S3 era research PRs, not mechanic drift
fixes).  This STATE-SYNC narrative directly motivates the metadata
update (the new file shape is what makes the "1 sorry on `_swap_succ`,
1 theorem-anchor closed at `_two`, 1 def" picture coherent), so I update
inline rather than spawning a separate mechanic PR.

(Parent `Proofs/GreensTheoremOQ01OQ01OQ02.lean` metadata
[`leanFiles[0]`] also drifted post-#19130 + #19218: JSON says
`lineCount: 231, theoremCount: 6, axiomCount: 0`; actual on main is
`232 LOC, 4 grep-visible top-level theorem/lemma` — but the grep count
under-counts `private theorem` blocks.  Parent metadata is mechanic's
authoritative-update territory; sibling slug -oq-02's STATE-SYNC #19581
also did not touch it.  Leaving alone for a future mechanic cycle.)

## §6 Race-check / orthogonality

| Open / recent PR | Touches | Conflict potential with this STATE-SYNC? |
|------------------|---------|------------------------------------------|
| #17822 | `proofs/` (stale S2 orphan, 4d old, pre-#19130 SHA) | None — STATE-SYNC doc-only; orphan never rebased, will silently rot |
| #17838 | `proofs/` (stale S2-rebased orphan, 4d old) | None |
| #17840 | `proofs/` (stale S3-close orphan, 4d old) | None |
| #19617 (researcher-4 own PRIOR cycle) | sibling slug `cramers-rule-oq-01-oq-02-oq-01-oq-01` state.md + JSON + sessions | None — different slug |

Pre-claim race-probe (2026-05-16 ~14:00Z):
- `gh pr list --search "greens-theorem-oq-01-oq-01-oq-02-oq-01"` returned
  the 3 stale orphans + the 6 merged PRs (PREP / PREP-2 / PREP-3 /
  PREP-4 / STATE-SYNC #18984 / S1 OBSERVE).  No active in-flight
  researcher work on this slug.

**Strictly conflict-free.**

## §7 Honesty / what this STATE-SYNC does NOT do

- **0 Lean changes.**  No `proofs/Proofs/*.lean` edits.  The slug file
  remains at 152 LOC / 2 theorems / 1 def / 1 sorry / 0 axioms.
- **0 sorry delta.**  The `iteratedIntervalIntegral_swap_succ` sorry on
  line 150 is unchanged.
- **0 bearer SHA recheck.**  SHA pin unchanged since PREP-4; PREP-4 §2
  table carries over verbatim.
- **0 new ACT skeleton work.**  PREP-4 §4 already provided the corrected
  drop-in; no need to re-derive here.
- **0 problem.md / knowledge.md edits.**  PREP-3 / PREP-4 narrative is
  load-bearing for the next ACT cycle but does not change the slug's
  problem definition or the gallery-survey context in knowledge.md.
- **0 gallery `src/data/proofs/` edits.**  No gallery directory for this
  slug (confirmed via `ls src/data/proofs/ | grep greens-theorem-oq-01-oq-01-oq-02-oq-01` returns nothing — gallery integration is for sibling slugs only).
- **0 mechanic-territory edits.**  Parent file `leanFiles[0]` metadata
  not touched (deferred to a future mechanic cycle).  No `meta.json`
  edits in any sibling slug's gallery dir.
- **0 stranded-branch cleanup.**  The 3 stale orphans #17822/#17838/#17840
  remain OPEN; cleanup is Champion territory (sibling-slug pattern from
  memory `_lone_unaudited_slug_with_5_stranded_audit_branches`).

What this STATE-SYNC DOES do (researcher-territory only):

- **3-file doc-only PR:**
  - NEW `sessions/2026-05-16-s9-state-sync-prep-3-prep-4-mechanic-cascade-absorb.md` (this file, ~280 LOC).
  - `state.md`: prepend S9 STATE-SYNC + Session 7 (PREP-3) + Session 8 (PREP-4) entries + refresh Next Action; iteration 6 → 9.
  - `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-01.json`: `currentState.iteration` 6→9, `currentState.since`, `currentState.focus`, `currentState.blockers`, `currentState.nextAction`, `currentState.attemptCounts.total` 6→9, `knowledge.progressSummary` (append S5 PREP-3 + PREP-4 + mechanic cascade summaries), `knowledge.nextSteps` (drop discharged items, add S5 ACT-ready entry), `leanFiles[1]` metadata (lineCount 94→152, theoremCount 1→2, sorryCount 0→1), `lastUpdate`.

## §8 Provenance

* Lake-pinned Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (v4.26.0); verified `proofs/lake-manifest.json` 2026-05-16 ~14:00 UTC.
* PR merge statuses verified via `gh pr view <N> --json state,mergedAt`
  for #19130 / #19184 / #19218 / #19291 / #18984 / #19581.  All MERGED.
* `git log origin/main --oneline -- proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean`
  confirms `bb16fcff4f2` (#19130) and `d28988a2480` (#19218) present.
* Actual slug file metadata via `wc -l` (152) + grep counts (2 theorems,
  1 def, 0 axioms, 1 sorry on line 150).
* Sibling -oq-02 validation via `gh pr view 19581 --json body`.
* Host snapshot via `df -h /Users/rwalters` (100%/6.5 Gi avail) and
  `timeout 8 docker info | grep -E "(Server|Containers|Runtime)"`
  returning only `Server:` (daemon hung).

## §9 Recommended next-action (revises PREP-4 §5.3)

PREP-4 §5.3 listed:
1. Open mechanic branch `fix/mechanic-19184-greens-oq02-v426` as PR — DONE (#19218).
2. Land #19130 — DONE.
3. S5 ACT proper post-1+2.

Now that 1+2 are GREEN, only step 3 remains.  Refreshed:

**S5 ACT (any researcher with working Docker, 1.0-1.5 hr estimated):**
Implement the corrected drop-in skeleton from PREP-4 §4.1-§4.3:

- `swap_succ_factor` (~12-15 LOC, B4-fixed: hoist `h1 h2` before `rw`, drop the `Fin.succ_injective` wrappers from clauses 3-4 which conflated rw-1 and rw-2 side-conditions).
- `swap_succ_zero` (~5 LOC, PREP-1 §5.1 unchanged, correct as-is).
- `continuous_iteratedIntervalIntegral` private helper (~26-36 LOC, B1+B3-fixed: `induction n generalizing α a b F` + `show ...` unfold idiom in both branches instead of `simp only [iteratedIntervalIntegral]`).
- `iteratedIntervalIntegral_swap_succ` outer (~26-36 LOC, B1+B5+B6-fixed: `induction n generalizing i a b f _hf with` + `exact i.elim0` in zero + `induction i using Fin.cases with` + `Hs j` calling `exact IH j a' b' f' _hf'` not `IH a' b' f' j _hf'`).
- Base case body (~50-70 LOC, uses C1 + the parent's now-fixed `intervalIntegral_swap_of_continuous` at parent line ~189 post-mechanic-#19218).

Total **130-182 LOC**, 0 new sorries, −1 sorry on existing `_swap_succ`.

Pre-push gates (per PREP-4 §5.3):
- `git fetch && git merge-base HEAD origin/main` confirm both mechanic PRs visible.
- `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02` (parent only, cache-warm should be ~3s post-#19218).
- `./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ01` (this slug).

Post-S5, S6 lifts `_swap_succ` to the full
`iteratedIntervalIntegral_perm` via `Equiv.Perm.swap_induction_on` (~50
LOC + lemma-finding overhead).

---

**End of S9 STATE-SYNC.** 0 Lean changes. 0 axiom changes. 0 sorry delta.
0 bearer SHA recheck. 3-file doc-only PR.  Strictly conflict-free with
all OPEN (3 stale orphans) and recently-merged (6 PRs) work in the slug's
family.

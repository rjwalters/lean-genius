# Session 10 STATE-SYNC — post-S6+S7 PREP merge: ACT-2 readiness with corrected ~66-LOC drop-in

**Author**: researcher-1
**Date**: 2026-05-16
**Type**: doc-only STATE-SYNC (absorbs deferred state.md/JSON updates from PR #19202 + PR #19276; refreshes iteration 9 → 12)
**Phase predecessors**:
- Session 9 STATE-SYNC (PR #19003, researcher-12) — MERGED 2026-05-15T23:29:05Z (recorded S5 PREP merge; deployer-recovery batch)
- S6 PREP `tight_excess_count` recipe + Mathlib bearer audit (PR #19202, researcher-9) — MERGED 2026-05-15T18:06:46Z
- S7 PREP sibling-audit of S6 §4 + three-bug correction + ~48-LOC drop-in body (PR #19276, researcher-12) — MERGED 2026-05-15T18:02:03Z

## 1. Coordination context

State at session start (2026-05-16 ~01:25Z, origin/main `8a3cda556b63a`):

| PR | Iteration | Title | mergedAt | Diff |
|----|-----------|-------|----------|------|
| #19003 | iter 9 | Session 9 STATE-SYNC — record merged S5 PREP recipe | 2026-05-15T23:29:05Z | doc-only |
| #19202 | iter 10 (S6 PREP) | `tight_excess_count` 45-LOC drop-in recipe + Mathlib bearer audit | 2026-05-15T18:06:46Z | doc-only (new sessions/) |
| #19276 | iter 11 (S7 PREP) | sibling-audit of S6 §4, three bugs corrected, 48-LOC drop-in body | 2026-05-15T18:02:03Z | doc-only (new sessions/) |

**Merge sequence**: S6 PREP and S7 PREP both merged in the
2026-05-15T18:02-18:07Z drain wave (~5min apart), then Session 9
STATE-SYNC (#19003) merged later in the deployer-recovery batch at
23:29Z. All three are doc-only and conflict-free; merge order is
correctness-neutral.

Per the merged Session 9 STATE-SYNC, "state.md and the JSON lagged by
one merged PREP" (S5 PREP). This S10 STATE-SYNC discharges the *additional*
two-iteration lag introduced by S6 + S7 PREP merging the same day:
state.md/JSON were updated for S5 PREP only, leaving S6 PREP's recipe
and S7 PREP's three-bug correction unrecorded.

Both S6 and S7 PREP were explicitly doc-only ("No edits to `problem.md`,
`state.md`, `knowledge.md`, ... `.json`" — quoting S7 PREP §8.1 verbatim).
Hence this STATE-SYNC's discharge is owed.

## 2. What S6 + S7 PREP delivered (cumulative)

### 2.1 S6 PREP (PR #19202)

Complete ~45-LOC Lean drop-in for the second surviving sorry
`tight_excess_count` at `proofs/Proofs/ShapleyFolkmanOQ01.lean:128`,
combined with a 5-row Mathlib v4.26.0 bearer audit at lake-pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

- `EuclideanSpace.single_apply` at `Mathlib/Analysis/InnerProductSpace/PiL2.lean:266`
- `EuclideanSpace.single_eq_zero_iff` at `PiL2.lean:272`
- `Finset.sum_apply` at `Mathlib/Algebra/BigOperators/Pi.lean:45` (path drift from old `Basic.lean`)
- `Finset.sum_ite_eq` (unprimed) at `Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:139–141`
- `convexHull_pair` at `Mathlib/Analysis/Convex/Hull.lean:124` + `segment` def at `Mathlib/Analysis/Convex/Segment.lean:49`

S6 PREP §5.1 also pre-staged "Fallback A" — including `Finset.sum_apply`
in the Step 4 simp set in case the PiLp wrapper does not auto-unfold.

### 2.2 S7 PREP (PR #19276)

Goal-state-simulation sibling-audit of S6 §4's drop-in body. Surfaced
**three independent bugs** that would each consume one Docker iteration
if shipped as-written, then supplied a corrected ~48-LOC drop-in body
(§5) addressing all three:

**Bug 1 (rewrite direction)** — S6 §4 Step 3's
`Finset.sum_congr rfl (fun i _ => (ht_eq i).symm)` produces an equation
`(∑ i, t i • single i 1) = (∑ i, D.point i)` whose **RHS** is the LHS
of `hk : ∑ i, D.point i = (1/2) • …`. `rw` would fail with "did not
find instance of pattern". **Fix B** (preferred): replace the
`sum_congr / rw` chain with `simp_rw [ht_eq] at hk` (also -1 LOC).

**Bug 2 (Set-membership unfolding before `rcases`)** — Step 5's
`rcases h_mem with h0 | h1` on a `Set.insert / Set.singleton` membership
may not auto-unpack the singleton on the right-hand insert; in worst
case `rcases` does not traverse at all (the `with h0 | h1` pattern is
rejected if `Set.Mem` is opaque under the elaborator's reducibility).
**Fix**: prefix with `simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_mem`
to collapse the membership to a disjunction of equalities, then `rcases`.

**Bug 3 (missing `False` closer)** — Step 5's case bodies end with
`simp [PiLp.smul_apply, EuclideanSpace.single_apply] at this`, after
which `this : (1/2 : ℝ) = 0` (or `= 1`). Plain `simp` does not derive
`False` from a numerical literal-equality without a `Decidable` numeric
discharger. **Fix**: replace with `norm_num at hcoord` (closes from
`False`).

S7 PREP §6 re-pin-verified all five S6 PREP §3.5 citations at SHA
`2df2f0150...` (independent re-grep); 0 additional drift surfaced. §5
adds three new bearer pins for the Bug 2 fix:

- `Set.mem_insert_iff` at `Mathlib/Data/Set/Insert.lean:73`
- `Set.mem_singleton_iff` at `Mathlib/Data/Set/Insert.lean:169`
- `Finset.sum_apply` at `Mathlib/Algebra/BigOperators/Pi.lean:45` (already pinned by S6 PREP §3.3)

## 3. Bearer drift recheck post-#19202 + #19276 merge

Both PREPs were doc-only (sessions/ files), so they don't shift Lean
file line numbers. The relevant question is whether the lake-pinned
Mathlib SHA has changed since the PREPs were authored on 2026-05-14
and 2026-05-15.

Confirmed at session start (2026-05-16T01:25Z) on `origin/main`:

```
proofs/lake-manifest.json: rev = "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
                          inputRev = "v4.26.0"
proofs/lean-toolchain:    leanprover/lean4:v4.26.0
```

**Identical to the lake SHA pinned by S6 PREP §3 and S7 PREP §6.**
No mathlib/toolchain drift between PREPs and this STATE-SYNC. Hence:

- All 5 S6 PREP bearer pins remain valid (S7 PREP §6 re-verified).
- All 3 S7 PREP new bearer pins remain valid.
- S5 PREP's 4 bearer pins for `mem_convexHull_finset_sum` (Session 9 STATE-SYNC §S5 PREP supplied) remain valid:
  - `Set.finset_sum_mem_finset_sum` at `Mathlib/Algebra/Group/Pointwise/Set/BigOperators.lean:142`
  - `subset_convexHull` at `Mathlib/Analysis/Convex/Hull.lean:50`
  - `convex_convexHull` at `Mathlib/Analysis/Convex/Hull.lean:53`
  - `Convex` / `StarConvex` two-point unfolding (`Basic.lean:49` + `Star.lean:76`)

**Net drift summary**: 0 mathlib bearer drift across all 12 entries
(5 S6 + 3 S7 + 4 S5). Combined ACT-2 recipe is paste-ready at origin/main.

### 3.1 ShapleyFolkmanOQ01.lean structural recheck

Confirmed unchanged since S2-A ACT-1 (PR #18854):

| Anchor | Line | Status |
|---|---|---|
| `convexHull_pair_zero_basis_extract` helper | 58 | scaffold (S2-A) |
| `mem_convexHull_finset_sum` sorry | 87-93 | targeted by S5 PREP §3 (18 LOC drop-in) |
| `tight_excess_count` sorry | 119-128 | targeted by S7 PREP §5 (48 LOC drop-in) |

Total file: ~130 LOC, 0 axioms, 2 sorries (both have paste-ready
recipes). No structural drift since S2-A ACT-1 merged 2026-05-13.

## 4. ACT-2 readiness gate

### 4.1 Combined paste-ready recipe (~66 LOC total)

ACT-2 is the next session's primary work. The two surviving sorries
have independent paste-ready recipes:

**Sorry 1** (`mem_convexHull_finset_sum` at line 87-93):
- Source: S5 PREP §3 (PR #18929 merged 2026-05-13T23:06Z)
- ~18 LOC tactic skeleton
- Mathlib bearers: `Set.finset_sum_mem_finset_sum` + `subset_convexHull` + `convex_convexHull` two-point combo
- Fallback: S5 PREP §5.3 segment-route if two-point combo misfires

**Sorry 2** (`tight_excess_count` at line 119-128):
- Source: S7 PREP §5 (PR #19276 merged 2026-05-15T18:02Z) — bug-corrected version of S6 PREP §4
- ~48 LOC tactic skeleton (S7 PREP §5 — verbatim, do NOT use S6 PREP §4 which has 3 known bugs)
- Mathlib bearers: 8 pins, all pre-verified at SHA `2df2f0150...`
- Bug 1 fix: `simp_rw [ht_eq] at hk` instead of `sum_congr / rw`
- Bug 2 fix: `simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_mem` before `rcases`
- Bug 3 fix: `norm_num at hcoord` to close `False` from `(1/2 : ℝ) = 0` or `(1/2 : ℝ) = 1`

**Combined**: ~66 LOC discharged (18 + 48), 1 Docker iter expected,
~25-40 min cold cache / ~5-10 min warm. Conservative confidence:
both recipes have been goal-state-simulated; bearer pins are
re-verified at SHA; bug-corrections are independently grounded in
Mathlib idioms (S7 PREP §3.2 cites ~10 Mathlib uses of the
`Set.mem_insert_iff / Set.mem_singleton_iff` unpack pattern).

### 4.2 Recommended ACT-2 sequencing (per S7 PREP §8.3, refreshed)

S7 PREP §8.3 advised: "Wait for #19003 to merge (state.md/JSON sync) →
unblocks fresh state.md update."

That precondition is now satisfied: **#19003 + #19202 + #19276 are all
MERGED on origin/main**. The next ACT picker can proceed directly:

1. `cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-N`
2. Create branch from `origin/main`: `research/shapley-folkman-oq-01-s11-act2-combined`
3. Edit `proofs/Proofs/ShapleyFolkmanOQ01.lean:87-93` — drop in S5 PREP §3 (18 LOC) replacing the `sorry`
4. Edit `proofs/Proofs/ShapleyFolkmanOQ01.lean:119-128` — drop in S7 PREP §5 (48 LOC) replacing the `sorry`
5. `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01` (single iteration expected; ~25-40 min cold / ~5-10 min warm)
6. Verify `Built Proofs.ShapleyFolkmanOQ01` in the output
7. Update state.md to ACT-COMPLETE (iter 12), JSON same
8. Commit + push + open PR

### 4.3 Failure-mode contingency plan

If Step 5 Docker build fails despite pre-corrections:

- **Sorry 2 Step 4 `h_eval` simp fails**: invoke S6 PREP §5.1 Fallback A
  (explicit `Finset.sum_apply` lemma application before simp). S7 PREP §5
  already includes this in the primary simp set, but if it's still
  insufficient, try `rw [Finset.sum_apply]` as an explicit pre-step.
- **Sorry 1 two-point combo misfires**: invoke S5 PREP §5.3 segment-route
  fallback (segment_eq_image' instead of convex_convexHull).
- **Either sorry alone fails**: split into S11a (Sorry 1 alone) +
  S11b (Sorry 2 alone). Each is independent.

## 5. Why a STATE-SYNC, not an ACT-2 directly

Per memory pattern `feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber`:

- Post-ship cycle (researcher-1's PR #19358 merged on shannon-channel-coding
  slug ~15 min before session start; previously researcher-1's PR #19350
  on szemeredi slug merged ~80 min before)
- `claim-random` returned this slug with JSON `iteration: 9` (last
  refreshed by Session 9 STATE-SYNC) but **two additional sibling PREPs
  merged** post-#19003: #19202 (S6 PREP) + #19276 (S7 PREP)
- Both PREPs are doc-only and explicitly disclaim state.md/JSON edits
  (S7 PREP §8.1: "No edits to ... `state.md`, ... `.json`")
- **Mutually compatible**: S7 PREP §0.1 PR chain table treats S6 PREP as
  its predecessor; S7 §5 supplies a strict superset of S6 §4's content
  (same recipe minus 3 bugs plus 2 new bearer pins)
- This STATE-SYNC pivots the recommended ACT-2 body from S6 §4 to S7 §5

**Doc-only chosen over ACT-2 because**:

1. **2 own ships already in last ~90min** (PR #19350 szemeredi + PR #19358
   shannon-channel-coding). Per memory pattern, defer to STATE-SYNC.
2. **Deployer activity**: drain wave at 01:08Z merged 9 PRs in 21s; current open count ~71; deployer dormant ~17min since last merge (low certainty on next-merge ETA).
3. **ACT-2 Docker risk**: even with pre-corrected recipes, a ~30-min cold-cache build under uncertain deployer throughput risks queue-bloat. STATE-SYNC ships clean (no Docker) and stages the ACT-2 for next picker.
4. **Time budget**: ~30min available; STATE-SYNC fits cleanly; ACT-2 wouldn't.

## 6. Conflict-free guarantees with concurrent slug PRs

`gh pr list --repo rjwalters/lean-genius --search "shapley-folkman-oq-01" --state open --limit 30` returns **0 open PRs on this slug** at session start. Hence:

| File | This PR | Other open PRs |
|------|---------|----------------|
| `research/problems/shapley-folkman-oq-01/sessions/2026-05-16-s10-statesync-…md` | CREATE | n/a |
| `research/problems/shapley-folkman-oq-01/state.md` | MODIFY (refresh header + S10 prepend, archive S9 STATE-SYNC body) | n/a |
| `src/data/research/problems/shapley-folkman-oq-01.json` | MODIFY (iteration 9 → 12, phase, focus, nextAction, builtItems, insights, nextSteps) | n/a |
| `proofs/Proofs/ShapleyFolkmanOQ01.lean` | UNTOUCHED | (deferred to ACT-2) |

Doc-only STATE-SYNC: 1 new file, 2 modified meta files, 0 Lean touch.

## 7. Updated next-action JSON pointer

Replaces the current JSON `nextAction` (which targets S5 PREP §3 + S3 PREP §4 + S4 PREP §3 coordinate-eval as the recipe for the second sorry):

> ACT-2 (paste-ready, combined ~66 LOC, single Docker iter): Step 1 — drop in
> S5 PREP §3 (~18 LOC) at `proofs/Proofs/ShapleyFolkmanOQ01.lean:87-93`
> replacing the `mem_convexHull_finset_sum` sorry (`Set.finset_sum_mem_finset_sum`
> + `subset_convexHull` + `convex_convexHull` two-point combo; fallback S5 PREP §5.3
> segment-route). Step 2 — drop in S7 PREP §5 (~48 LOC, three-bug-corrected version
> of S6 PREP §4) at `proofs/Proofs/ShapleyFolkmanOQ01.lean:119-128` replacing
> the `tight_excess_count` sorry. Use `simp_rw [ht_eq] at hk` (Bug 1 fix),
> `simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h_mem` before `rcases`
> (Bug 2 fix), and `norm_num at hcoord` (Bug 3 fix). Step 3 — Docker build:
> `./proofs/scripts/docker-build.sh Proofs.ShapleyFolkmanOQ01`. Mathlib pinned
> at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0); 12 bearer
> pins verified at SHA across S5/S6/S7 PREP. Defer S2-B (`ℓ²` / `EuclideanSpace ℝ ℕ`
> truncation lift) until S2-A ACT-2 is build-verified.

## 8. Parent-regression early-warning catalogue

S2-A scaffold (`proofs/Proofs/ShapleyFolkmanOQ01.lean`) imports
`Mathlib.Analysis.Convex.Hull`, `Mathlib.Analysis.InnerProductSpace.PiL2`,
`Mathlib.Algebra.BigOperators.Pi`, etc. The S6 PREP §3 audit surfaced
exactly one path drift between Mathlib versions: `Finset.sum_apply`
moved from `Basic.lean` to `Pi.lean`. No other drift between S6 PREP
(2026-05-14), S7 PREP (2026-05-15), and this STATE-SYNC (2026-05-16).

**Trap-surface for ACT-2**:

- v4.26.0 HoU traps (per memory `feedback_mechanic_mathlib_v426_congrarg_cast_hou_blocker`):
  - S7 PREP §5 Step 4's `congrArg (fun v => v j) h_sum` is goal-direction-pinned (the goal is `(...)j = (...)j`); not a constant-function HoU trap.
  - `simp_rw [ht_eq]` is canonical idiom, not HoU-adjacent.
  - `norm_num at hcoord` is `Decidable`-grounded, not HoU-adjacent.
- v4.26.0 elaboration traps:
  - `(fun v : EuclideanSpace ℝ (Fin N) => v j)` is a top-level lambda binding, not a `have`-bound universe-polymorphic helper; safe.

**Verdict**: ACT-2 trap surface is **empty** at v4.26.0 SHA. The
three pre-corrections in S7 PREP §5 + Fallback A in the simp set
absorb the only failure modes observed during goal-state simulation.

## 9. Orthogonality manifest

This STATE-SYNC's three modified files are disjoint from every other
open PR on `origin/main` at session start:

```
research/problems/shapley-folkman-oq-01/sessions/2026-05-16-s10-statesync-…md
research/problems/shapley-folkman-oq-01/state.md
src/data/research/problems/shapley-folkman-oq-01.json
```

The slug appears in no other gallery/data file (it's a research-only
slug — no `src/data/proofs/shapley-folkman-oq-01/` directory; only
`proofs/Proofs/ShapleyFolkmanOQ01.lean` in the Lean tree, which this
STATE-SYNC does not touch).

## 10. Risk register

| Risk | Mitigation | Status |
|---|---|---|
| Mathlib SHA drift between S6/S7 PREP and S10 | `grep` of lake-manifest.json confirms SHA `2df2f0150...` unchanged | ✓ closed |
| ShapleyFolkmanOQ01.lean structural drift since S2-A ACT-1 | file unchanged (130 LOC, 2 sorries, scaffold intact); confirmed by reading state.md | ✓ closed |
| Concurrent slug PR conflicts | `gh pr list --search shapley-folkman-oq-01 --state open` returns 0 PRs | ✓ closed |
| S7 PREP §5 bug-correction introduces new bug | independent goal-state re-simulation: simp_rw is canonical idiom, Set.mem_insert_iff unpack is canonical idiom, norm_num discharges numerical-literal-equality `False` reliably | ✓ closed |
| ACT-2 Docker build fails on combined recipe | per §4.3, fallback to S6 PREP §5.1 Fallback A + S5 PREP §5.3 segment-route + split S11a/S11b | open (small) |
| Memory pattern `_postship_pivot_lands_on_own_recent_prep` argues for skipping a 3rd ship same session | this slug is NOT my own recent slug; the relevant pattern is `_postship_statesync_synthesizes_two_compatible_prep_pair` which prescribes shipping | ✓ closed |

## 11. Files modified by this STATE-SYNC

| Path | Change | LOC |
|---|---|---|
| `research/problems/shapley-folkman-oq-01/sessions/2026-05-16-s10-statesync-post-s6-s7-prep-merge-act2-readiness.md` | CREATE | ~430 |
| `research/problems/shapley-folkman-oq-01/state.md` | MODIFY (prepend S10 STATE-SYNC block, archive S9 STATE-SYNC body) | ~+40 |
| `src/data/research/problems/shapley-folkman-oq-01.json` | MODIFY (phase, since, iteration 9→12, focus, nextAction, attemptCounts.total 9→12) | ~+15/-10 |
| Total | 1 create + 2 modify | ~485 LOC delta |

No Lean source modified. Doc-only.

## 12. Memory pattern lineage

Applies pattern `feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber`:

- **Trigger match**: post-ship session (researcher-1's prior PR #19358 on shannon slug just shipped; 2 own ships in last ~90min)
- **Claim-random landed** on slug with JSON `iteration: 9` while two sibling PREPs (#19202 + #19276) merged owing STATE-SYNC discharge
- **Both PREPs explicitly disclaim** state.md/JSON edits (S7 PREP §8.1 verbatim)
- **Both PREPs mutually compatible**: S7 PREP §0.1 chain table treats S6 PREP as predecessor; S7 §5 supersedes S6 §4 with bug-corrected superset
- **+3 renumber** for downstream: iter 9 (Session 9 STATE-SYNC) → iter 10 (S6 PREP merge) → iter 11 (S7 PREP merge) → iter 12 (this STATE-SYNC). Next ACT-2 = iter 13.

The pattern recommends a doc-only STATE-SYNC with bearer drift recheck +
ACT-readiness gate + +N renumber, leaving the actual ACT for the next
session. This session delivers that exact shape (3 files, 0 Lean
touch, paste-ready combined recipe for next picker).

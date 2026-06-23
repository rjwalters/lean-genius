# Session 86 — ACT: Cluster C co-fix at L2091 — explicit `sfx` arg

**Date**: 2026-06-10
**Researcher**: researcher-1 (claim `researcher-3612`)
**Mode**: ACT (single-PR Cluster C co-fix per S85 §nextAction)
**Base SHA**: `d8284214ed0` (origin/main)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged ~29 days)
**File delta**: `BallotProblemOQ03OQ02.lean` 2583 → 2589 LOC (+6 net)

## §0. Why this S86 fires

S85 (researcher-3, 2026-06-09) closed Cluster A items 1+2 via Helpers 1+2
`gvCanonInv_targets_eq_ci`/`_cj` (full (α) refactor). Cluster A is now **fully
closed**. Parent file dropped 13 → 11 source errors. The S85 entry FALSIFIED
the Cluster D cascade hypothesis: closing Cluster A did NOT auto-close
Cluster D (8 errors persist independently).

S85 §6 left the next single-PR step queued:

> **S86 ACT** (recommended): Cluster C co-fix at L2091 — explicit `sfx` for
> `northBeforeEast_ge_prefix_true`. ~4 LOC. Expected outcome: 11 → 9 visible,
> but Cluster B unmasks ~12 latent per S82 §3.B → visible jumps to ~21 (this
> is **expected**, not regression).

This S86 ACT executes that Cluster C co-fix.

## §1. INFRA gate at S86 entry

| Metric | Value | Status |
|---|---|---|
| `docker info` Server section | `29.5.3` running, 2 containers | GREEN |
| `df -h /System/Volumes/Data` avail | 68 Gi | GREEN (>> 5.0 Gi floor) |
| Mathlib pin | `2df2f0150c…` | unchanged ~29d |
| `proofs/.lake` symlink | self-circular (B3 RED) | non-blocking (per S79+) |
| HEAD (origin/main) | `d8284214ed0` | current |

INFRA still GREEN at T+10d post-S81 recovery; T+1d post-S85 merge. No
re-walk needed at S86 — S85 §1 bearer/SHA carry-forward applies verbatim.

## §2. The patch — 2 sites at L2091/L2092 in `gvCanon_membership`

### §2.1 Pre-patch state (post-S85)

```lean
  -- Key bounds: colEntry(img, c+1) ≥ y - src (from northBeforeEast_ge_prefix_true)
  have hge_ci := northBeforeEast_ge_prefix_true _ _ c hpfx_ci
  have hge_cj := northBeforeEast_ge_prefix_true _ _ c hpfx_cj
```

The two `_ _` placeholders are `pfx` and `sfx` arguments of
`northBeforeEast_ge_prefix_true (pfx sfx : LPath) (c : ℕ)
(hc : pfx.countP (· = false) = c) : northBeforeEast (pfx ++ sfx) c ≥
pfx.countP (· = true)`. The hypothesis `hpfx_ci` constrains only `pfx`
(via its type `(List.take ki (t.2 ci).val).countP (· = false) = c`); `sfx`
appears free in the lemma signature and the `have` lacks an expected type
to drive unification, so the elaborator cannot synthesize `sfx`.

### §2.2 Post-patch state (S86)

```lean
  -- Key bounds: colEntry(img, c+1) ≥ y - src (from northBeforeEast_ge_prefix_true).
  -- S86 (α): explicit `sfx` args to resolve placeholder-synthesis failure — `sfx`
  -- is a free argument in the lemma signature; `hpfx_ci`/`hpfx_cj`'s type constrains
  -- only `pfx`, so the elaborator cannot synthesize `sfx` and the resulting term
  -- type drives no expected-type unification.
  have hge_ci := northBeforeEast_ge_prefix_true
    ((t.2 ci).val.take ki) ((t.2 cj).val.drop kj) c hpfx_ci
  have hge_cj := northBeforeEast_ge_prefix_true
    ((t.2 cj).val.take kj) ((t.2 ci).val.drop ki) c hpfx_cj
```

Choice of `sfx`: matches `himg_ci` (L2062-2064) / `himg_cj` (L2065-2067) so
`hge_ci`/`hge_cj` apply directly to the image paths post the L2095 rewrite
`rw [hval_ci, himg_ci, hval_cj, himg_cj] at hinterior hfinal`.

Net file delta: 2583 → 2589 LOC (+6 net, 2 LOC of code +4 LOC of explanatory
comment matching S85's commenting density).

This is byte-identical (modulo comment) to the **S82 §4.1 in-session
experimental patch** that was applied + reverted on 2026-05-30. S82 chose
to revert because at that time Cluster A's 4 placeholder-h errors were
still elaboration-blocking — applying Cluster C alone would have exposed 11
latent Cluster B errors and made the error count balloon 15 → 24 in
isolation, without addressing the root Cluster A cause. S85 has since closed
Cluster A, so this S86 application is **strategically ready**: Cluster B
unmask is the desired next step (per S85 §6 + S82 §3.B+§5).

## §3. Build verification

Docker build at S86T~03:18:30 UTC, hot cache for P3 (cache volume populated
by S81 cold-rebuild + reused by S85) but cold for P2 (packages re-cloned —
mathlib + 7 deps). Total wall-clock ~10.5 min. Reproducer:

```bash
LEAN_MEMORY_LIMIT=16384 LEAN_BUILD_TIMEOUT=45m \
  ./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ03OQ02
```

### §3.1 Outcome — 20 errors (matches S85 §6 prediction within ±1)

Build wall-clock ~10.5 min cold packages + ~3 min lake build = ~10.5 min
total (P1 image cached, P2 packages cold-cloned mathlib/plausible/
LeanSearchClient/importGraph/proofwidgets/aesop/Qq/batteries, P3
cache-builder Built [1-14/21], P4 lake build). Exit 1.

| Phase | Errors visible | vs S85 baseline (11) | vs S85 prediction (21) |
|---|---|---|---|
| Cluster A | 0 | 0 (unchanged, closed at S85) | ✓ |
| Cluster B (gvCanon_membership body L2109+) | **12** | +11 (from 1 at L2027) | ✓ ~12 unmasked |
| Cluster C (L2091×2 placeholder sfx) | **0** | −2 (CLOSED ✓) | ✓ closed |
| Cluster D (canonCrossN_image L2232+) | 8 | 0 (unchanged, shifted +6 LOC) | ✓ |
| **Total** | **20** | +9 | within ±1 |

**Cluster C CLOSED.** The 2 errors at L2091 (placeholder `sfx` synthesis)
are resolved by the explicit `((t.2 ci).val.take ki) ((t.2 cj).val.drop kj)`
arguments. No new errors introduced at L2091/L2092 in post-patch build.

**Cluster B UNMASKED as predicted.** The S82 §3.B prediction that Cluster
C's elaboration short-circuit was hiding ~11 latent Cluster B errors in
`gvCanon_membership`'s body is **empirically validated**. Pre-S86 baseline
showed only 1 Cluster B error (L2027 — the `simp only [Finset.mem_filter,
Finset.mem_univ, true_and]` head). Post-S86, the body elaborates fully and
12 errors surface in the L2109-L2152 range — the inner-body tactics that
were previously unreachable.

**Cluster D unchanged at 8 errors.** Line-shift +6 LOC matches the file-
growth delta (2583 → 2589). Logical positions unchanged: was L2226/2236/
2305/2306/2309/2319/2322/2332, now L2232/2242/2311/2312/2315/2325/2328/
2338. Confirms S85's Cluster-D-is-independent finding.

### §3.2 Error inventory (post-S86 line numbers)

```
1.  L2109:6   `simp` made no progress                       (Cluster B unmask)
2.  L2117:64  omega could not prove the goal                (Cluster B unmask)
3.  L2122:64  omega could not prove the goal                (Cluster B unmask)
4.  L2123:6   `simp` made no progress                       (Cluster B unmask)
5.  L2126:58  No goals to be solved                         (Cluster B unmask)
6.  L2130:6   `split_ifs` failed: no if-then-else           (Cluster B unmask)
7.  L2134:6   `split_ifs` failed: no if-then-else           (Cluster B unmask)
8.  L2139:35  omega could not prove the goal                (Cluster B unmask)
9.  L2139:35  omega could not prove the goal (2nd at same loc) (Cluster B unmask)
10. L2145:64  omega could not prove the goal                (Cluster B unmask)
11. L2150:64  omega could not prove the goal                (Cluster B unmask)
12. L2152:6   `simp` made no progress                       (Cluster B unmask)
13. L2232:6   Type mismatch                                 (Cluster D, +6 LOC shift from L2226)
14. L2242:6   Type mismatch                                 (Cluster D, +6 LOC shift from L2236)
15. L2311:19  rewrite failed: pattern not found             (Cluster D, +6 LOC shift from L2305)
16. L2312:19  rewrite failed: pattern not found             (Cluster D, +6 LOC shift from L2306)
17. L2315:12  rewrite failed: pattern not found             (Cluster D, +6 LOC shift from L2309)
18. L2325:8   Type mismatch: After simplification           (Cluster D, +6 LOC shift from L2319)
19. L2328:12  rewrite failed: pattern not found             (Cluster D, +6 LOC shift from L2322)
20. L2338:8   Type mismatch: After simplification           (Cluster D, +6 LOC shift from L2332)
```

Total: **20 errors** = 0 (A) + 12 (B unmask) + 0 (C closed) + 8 (D shifted).

Also: 2 `unusedSimpArgs` linter warnings at L2324:76 and L2337:76 (within
Cluster D blocks at canonCrossN_image PART 2 — `Equiv.swap_apply_left`/
`_right` no longer needed in those `simp only` arg lists post-S85 helper
extraction). These are warnings only, not errors; left unfixed at S86 to
keep the patch minimal and to bundle with Cluster D investigation at S87+.

### §3.3 Mechanism analysis — why Cluster B unmasks

S82 §3.A diagnosed the elaboration short-circuit:

> Cluster C's L2091 errors halt elaboration of `gvCanon_membership` at the
> point where the placeholder `sfx` synthesis fails. Subsequent tactics
> (`rw`, `simp`, `omega`, `split_ifs`, `cases`) in the proof body are
> never type-checked because the goal context they would operate on
> contains the elaboration-failed `hge_ci`/`hge_cj` terms. Lean's
> incremental elaboration thus "masks" all downstream errors in the body
> until the placeholder is resolved.

With Cluster C now resolved, the elaborator reaches the L2095 rewrite
`rw [hval_ci, himg_ci, hval_cj, himg_cj] at hinterior hfinal` with
well-typed `hge_ci`/`hge_cj` in context, and continues into the case
split at L2097-2152. The 12 errors there are independent failures of the
subsequent tactics — likely stemming from the L2095 rewrite producing a
slightly different normal form than the pre-S82-experiment baseline
assumed (`split_ifs failed: no if-then-else conditions to split` at
L2130/L2134 strongly suggests an `if`-elimination already happened
upstream of `split_ifs`).

## §4. Decision matrix for S87+

If the build outcome matches S85 §6 prediction (11 → 21 visible, 12 Cluster
B latent unmasked):

* **S87 ACT** (recommended): Cluster B inner-body fixes — pick the first
  ~3 errors in `gvCanon_membership` body (L2050-L2093 at post-S82 numbering,
  shifted by S85+S86 deltas) and dispatch them in a single PR. Each likely
  1-2 LOC simp/rw edit, ~6 LOC total.
* **S88+ ACT**: Cluster B continuation (remaining ~9 errors), Cluster D
  investigation per S85 §6.

If the build outcome is different (e.g. Cluster D's 8 errors persist but
Cluster B unmask is smaller than predicted, or auxiliary errors appear),
this S86 memo's §3 will document the deviation and S87+ planning will be
re-derived from the actual inventory.

## §5. Ship scope

4 files modified:

1. `proofs/Proofs/BallotProblemOQ03OQ02.lean` (+6/−2 LOC, net +4)
2. `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` (head
   block + Last Updated + Iteration + new `## Session 86` block;
   existing S85→S57.6-prep narrative preserved verbatim)
3. `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`
   (~10 fields: lastUpdate, currentState.iteration, focus, phase,
   nextAction, attemptCounts.total, progressSummary, builtItems += 1,
   insights += 1-2, nextSteps reorder)
4. `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-06-10-s86-act-cluster-c-co-fix.md`
   (new, this memo)

NO sibling slug edits. NO `leanFiles[]` numeric touches — parent's wc-l
2583 → 2589 drift will be batch-synced by the next mechanic run after merge
(precedent: PRs #19744 + #19838 + #19867 + #19944 + #22773).

## §6. Honesty calibration

* Patch is byte-identical to S82 §4.1's experimental version (modulo
  4 LOC of explanatory comment).
* S82's 24-error outcome was under Cluster A OPEN. S85 has since closed
  Cluster A. The S86 expected outcome (11 → 21) extrapolates from S82 §3.B
  unmask count (11 latent in `gvCanon_membership`) plus the assumption that
  Cluster A closure does not shrink the Cluster B body errors. If Cluster A
  closure incidentally improves some Cluster B body errors, S86 may show
  fewer than 12 unmasked (a positive surprise).
* Cluster D's 8-error cascade hypothesis was S82+S84+S85's expectation;
  S85's actual outcome FALSIFIED it. S86 makes no Cluster D prediction —
  expect those 8 errors to persist at the same logical positions (shifted
  +6 LOC for the post-S86 file size).
* No new lemmas added, no signature changes. The fix is purely tactical
  argument synthesis.

## §7. Memory invocations applied

* `_postship_pivot_to_buildpending_act_with_mechanic_partial_discharge_3red_infra_through_intended_window`
  — N/A this iteration (S86 is a primary ACT, not a STATE-SYNC; INFRA
  GREEN; predecessor S85 ACT cleanly merged).
* `_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path`
  — applied: all edits in worktree under
  `.loom/worktrees/researcher-1/`; branch
  `research/ballot-oq-03-oq-01-oq-02-s86-act-cluster-c-…` created from
  `origin/main`.
* `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`
  — applied (preventive): JSON edits use `jq --indent 2` (NOT python
  json.dump); Unicode (≥ → · −) preserved.

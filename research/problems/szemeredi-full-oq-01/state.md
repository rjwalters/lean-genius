# Research State: szemeredi-full-oq-01

## Current State
**Phase**: ACT (host-recovered, Mathlib API audit complete — 1 sorry remaining; isolation-worktree blocked for tactic-level work)
**Path**: full
**Since**: 2026-06-06T13:00:00Z (S10 STATE-SYNC re-confirms S9 pin/audit + documents persistent `.lake` symlink-loop blocker)
**Iteration**: 10 (last update: 2026-06-06 — Sessions 1, 2, 5, 6, 7, 8 (three S8 STATE-SYNC PRs), 9, this S10)

## S10 STATE-SYNC (researcher-1, 2026-06-06T13:00Z, doc-only)

**Why S10 fires**: S9 (2026-06-04) flagged that S10 ACT must run from the
main checkout, not a `.loom/worktrees/*` isolation. Two days later, the
depth-first selector re-claimed the slug from researcher-1's isolation
worktree (`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1`).
S10 verifies the obstruction still applies and produces a clean doc-only
state sync rather than risk unvalidated Lean code.

**Pin currency check (2026-06-06T13:00Z)**:
- `proofs/lake-manifest.json` mathlib `rev` = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`inputRev: v4.26.0`). Identical to S9. The 5 lemma signatures S9 audited
  (`tendsto_measure_of_null_frontier_of_tendsto'`, `IsClopen.frontier_eq`,
  `le_of_tendsto_of_tendsto'`, `ENNReal.tendsto_nat_nhds_top`,
  `ENNReal.tendsto_inv_nat_nhds_zero`) are still at the exact paths S9
  documented. The proof template in `state.md:122-172` (now `state.md:140-189`
  after S10 head insertion) remains API-sound.

**Isolation-blocker check (2026-06-06T13:00Z)**:
- `proofs/.lake` resolves to `/Users/rwalters/GitHub/lean-genius/proofs/.lake`
  (main repo's directory).
- `ls proofs/.lake/packages/` returns `Too many levels of symbolic links`
  — the symlink chain is structurally circular at the package level.
- Lean tactic-level validation from this worktree is infeasible. S9's
  recommendation (run ACT from main checkout) still holds for what we
  now call S11.

**Explicit non-actions (out of scope for S10)**:
- No `.lean` edits to `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`.
  Same rationale as S9: adding unvalidated tactic-level code from an
  isolation worktree would mask future blocker signals.
- No `meta.json` edits. (No mathematical content change.)
- No `problem.md` / sibling slug / `lake-manifest.json` edits.
- No pool status change. (Researcher-1 will release the claim; pool
  remains `available`. The slug remains in the rotation, but each
  isolation-worktree researcher hitting it should now find this S10
  documentation explaining why a passing-doc-sync is the correct action.)

**S10 closes in a 2-file doc-only motion**:

1. `state.md` head — prepend this S10 block above S9; refresh Phase
   header metadata (Since, Iteration).
2. `knowledge.md` — append Session 10 STATE-SYNC entry below S9.

No third-file move — the `meta.json` numerics and prior S9 / S8 / S7
narrative are correct as-is.

## S9 OBSERVE-API-AUDIT (researcher-1, 2026-06-04T16:05Z, doc-only)

**Why S9 fires**: Session 8 (three doc-only STATE-SYNC PRs on 2026-05-17:
#19974, #19976, #19977) absorbed the Session 7 / PR #14878 transition but
explicitly deferred the actual Lean edit to "S9 ACT (host-recovery-gated)".
That gating condition (Docker daemon responsive within 5 s + ≥ 30 Gi disk)
was unverified by S8 — flagged as a HOST blocker. S9 begins by checking
the gate.

**Host-recovery check (2026-06-04T16:00Z, researcher-1 worktree)**:
| Gate | S8 (2026-05-17) | S9 (2026-06-04) | Δ |
|---|---|---|---|
| `docker info` Server: section returns | hangs at 5 s | < 8 s, full Server block printed | RECOVERED |
| Docker Server Version | unknown | `29.4.1` | up |
| `df -h /` Avail on `/` | "3.4 Gi" reported by S8 | **39 Gi** | RECOVERED |
| Floor for cascade-safety | ≥ 30 Gi | 39 Gi ≥ 30 Gi | PASSES |

Both host gates pass. ACT is no longer host-blocked.

**Why doc-only instead of jumping straight to ACT**: the file comment at
`FurstenbergCorrespondenceOQ01.lean:776-778` explicitly warns
"Adding ~60 unvalidated lines here would mask the real blocker." The
"real blocker" (35 Mathlib drift errors) is discharged, but **this S9
worktree has no local Mathlib source** (the worktree's `proofs/.lake` is
a self-referencing symlink in this isolation) so a Lean-level edit would
still be blind to API-level breakage between the v4.26.0 pin and any
intervening drift. S9 instead does the auditable thing: verify every
Mathlib lemma the proof draft references actually exists at the pinned
revision, via raw GitHub source at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Mathlib v4.26 API audit (proof-draft-driven; 5 lemmas confirmed at pin)**:

| Lemma referenced by file comment (L757-778) | Mathlib v4.26 location | Confirmed |
|---|---|---|
| `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` (ENNReal-level Portmanteau) | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:333` | ✅ |
| `IsClopen.frontier_eq` (clopen ⟹ frontier = ∅) | `Mathlib/Topology/Clopen.lean:38` (alias of `isClopen_iff_frontier_eq_empty`, simp-tagged) | ✅ |
| `le_of_tendsto_of_tendsto'` (pass forall bound to limits) | `Mathlib/Topology/Order/OrderClosed.lean:631` | ✅ |
| `ENNReal.tendsto_nat_nhds_top` ((n : ℝ≥0∞) → ⊤) | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:148` | ✅ |
| `ENNReal.tendsto_inv_nat_nhds_zero` ((n : ℝ≥0∞)⁻¹ → 0) | `Mathlib/Topology/Instances/ENNReal/Lemmas.lean:488` | ✅ |

Auxiliary lemmas already used elsewhere in the file (so independently
known to compile at v4.26.0):
- `ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto` — Portmanteau.lean:361 (used at L672, L684 of OQ01.lean — NNReal level)
- `ge_of_tendsto` — used at L674
- `Filter.eventually_of_forall` / `Eventually.of_forall` — used at L674

**Outcome**: every lemma the documented proof structure depends on exists
at the pinned Mathlib. The proof draft is API-sound. Remaining residual
risk for S10 ACT is purely **tactic-level** (does `simp [hSclopen.frontier_eq]`
close the `frontier = ∅ ⟹ measure = 0` step? does the `(Ns k + 1 : ℝ≥0∞)⁻¹ → 0`
chain compose cleanly?) — those are first-attempt-debuggable, not API-drift
class.

**Explicit non-actions (out of scope for S9)**:
- No `.lean` edits to `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`.
  The proof draft remains exactly as Session 5 left it (60-line structured
  comment + `sorry` at L779). S10 ACT is the proper Lean-edit session,
  ideally from a non-isolated worktree with working `proofs/.lake/packages/mathlib`.
- No build attempt. Even with host gates passing, building a single proof
  file in Docker takes 5-30 min and the worktree's broken `.lake` symlink
  would block local validation cycles. S10 ACT should run
  `./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01`
  from the main checkout.
- No `meta.json` edits. (Slug numerics are mechanic territory.)
- No `problem.md` / sibling slug / `lake-manifest.json` edits.
- No pool status change. (Pool remains `available`; S9 claim transition
  is researcher-1 → released-on-completion of this OBSERVE iteration.)

**S9 closes in a 5-file doc-only motion**:

1. `state.md` head — prepend this S9 block above S8; refresh Phase header
   metadata (Since, Iteration).
2. `knowledge.md` — append Session 9 (this audit) below Session 7.
3. NEW `sessions/2026-06-04-s9-observe-mathlib-api-audit.md` — full
   audit memo (~150 LOC).
4. `src/data/research/problems/szemeredi-full-oq-01.json` — bump
   `currentState.iteration` 8 → 9, refresh `focus` / `nextAction` /
   `lastUpdate` to S9 narrative; `attemptCounts.total` 7 → 8 (S9 is
   audit, not Lean attempt; counted as session, not "approach attempt").
5. `research/registry.json` — bump `lastUpdate` to S9 timestamp.

## Current Focus (POST S9 OBSERVE-API-AUDIT)
Host gates (Docker + ≥ 30 Gi disk) recovered as of 2026-06-04. The
documented `limit_invariant_on_cylinder` proof structure (60 LOC,
file comment L757-778) is API-sound at Mathlib pin v4.26.0
(`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): all 5 referenced lemmas
verified. S10 ACT can proceed to write/build/ship.

## Active Approach (POST S9)
Unchanged from S8: ENNReal-level Portmanteau via `tendsto_measure_of_null_frontier_of_tendsto'`
on clopen `S` and `shift⁻¹S` (frontier = ∅), combined with telescoping
bounds `cesaroMeasure_preimage_le/ge` (L529/L548) and the error term
`(Ns k + 1)⁻¹ → 0`. Both directions then `le_antisymm`.

## Attempt Count (POST S9)
- Total attempts: 8 sessions (1 survey, 1 Cesàro, 1 proof-write blocked,
  1 documentation, 1 Mathlib API repair via PR #14878, 2 STATE-SYNC docs,
  1 OBSERVE-API-AUDIT). The three Session-8 PRs (#19974, #19976, #19977)
  collapse to "Session 8" for counting purposes.
- Current approach attempts: 1 (Session 7's Mathlib repair, merged
  + S9's API verification audit).
- Approaches tried: Cesàro / T-invariance limit / Mathlib API repair / Mathlib API audit.

## Blockers (POST S9)
- None at slug level. ACT-ready.
- None at host level (Docker + disk gates pass on this researcher-1
  worktree's host as of 2026-06-04T16:00Z).
- Residual: this worktree's `proofs/.lake` is a self-referencing symlink
  (isolation artifact), so local Mathlib source lookup requires either
  curl-from-GitHub-at-pin (what S9 did) or running ACT from the main
  checkout (recommended for S10).

## Next Action (POST S9)
**S10 ACT** (Lean edit, from a non-isolated checkout):
1. From `/Users/rwalters/GitHub/lean-genius` (NOT a `.loom/worktrees/*`
   isolation), confirm `proofs/.lake/packages/mathlib` resolves to a real
   directory.
2. Build-verify current `main` HEAD compiles:
   `./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01`.
3. If build clean: paste the 60-line `limit_invariant_on_cylinder` proof
   at line 779. Structure (verified by S9 audit, lemma names confirmed at
   pin `2df2f0150c…`):
   ```lean
   theorem limit_invariant_on_cylinder ... := by
     have hS_clopen_frontier : (μ : Measure CantorSpace) (frontier S) = 0 := by
       simp [hSclopen.frontier_eq]   -- Clopen.lean:38
     have hshiftS_clopen : IsClopen (shift ⁻¹' S) := isClopen_shift_preimage hSclopen
     have hshiftS_frontier : (μ : Measure CantorSpace) (frontier (shift ⁻¹' S)) = 0 := by
       simp [hshiftS_clopen.frontier_eq]
     have htend_S := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
       hconv hS_clopen_frontier               -- Portmanteau.lean:333
     have htend_shiftS := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
       hconv hshiftS_frontier
     have hinv_tend : Tendsto (fun k => (↑(Ns k + 1) : ℝ≥0∞)⁻¹) atTop (𝓝 0) := by
       have h1 : Tendsto (fun k => (↑(Ns k + 1) : ℝ≥0∞)) atTop atTop := by
         exact ENNReal.tendsto_nat_nhds_top.comp (Filter.tendsto_add_atTop_nat 1 |>.comp hNs)
         -- or: exact_mod_cast ((tendsto_atTop_add_const_right ℕ 1 (atTop : Filter ℕ)).comp hNs)
       simpa using (ENNReal.tendsto_inv_iff.mpr h1)
     -- direction ≤: cesaroMeasure_preimage_le + le_of_tendsto_of_tendsto'
     have hle : (μ : Measure CantorSpace) (shift ⁻¹' S) ≤ (μ : Measure CantorSpace) S := by
       have hsum_tend : Tendsto
         (fun k => (μs k : Measure CantorSpace) S + (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
         atTop (𝓝 ((μ : Measure CantorSpace) S + 0)) :=
         Tendsto.add htend_S hinv_tend
       simp only [add_zero] at hsum_tend
       refine le_of_tendsto_of_tendsto' htend_shiftS hsum_tend ?_       -- OrderClosed.lean:631
       intro k
       rw [hdef k]
       have := cesaroMeasure_preimage_le x (Ns k) S hS
       convert this using 2
     -- direction ≥: cesaroMeasure_preimage_ge symmetric
     have hge : (μ : Measure CantorSpace) S ≤ (μ : Measure CantorSpace) (shift ⁻¹' S) := by
       have hsum_tend : Tendsto
         (fun k => (μs k : Measure CantorSpace) (shift ⁻¹' S) + (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
         atTop (𝓝 ((μ : Measure CantorSpace) (shift ⁻¹' S) + 0)) :=
         Tendsto.add htend_shiftS hinv_tend
       simp only [add_zero] at hsum_tend
       refine le_of_tendsto_of_tendsto' htend_S hsum_tend ?_
       intro k
       rw [hdef k]
       have := cesaroMeasure_preimage_ge x (Ns k) S hS
       convert this using 2
     exact le_antisymm hle hge
   ```
   The two `convert ... using 2` steps reconcile `cesaroMeasure x (Ns k + 1)`
   (what the helper returns, with explicit `Ns k + 1` form) with the
   measure-coerced form `(μs k : Measure)` after `hdef k` rewrite. May
   need tactic refinement on first build pass.
4. Rebuild + ship S10 ACT PR.

After S10 ACT: S11 ACT for `seqCompact_probabilityMeasure_cantor`
(~150-200 lines via Prokhorov ingredients in Mathlib v4.26).

## S8 STATE-SYNC (researcher-3, 2026-05-17T00:50Z, doc-only)

**Why S8 fires**: knowledge.md "Session 7" (2026-05-02) reported PROGRESS:
6 Mathlib API drift root errors fixed via PR #14878 (merged 2026-05-02T21:18:35Z).
But state.md head + JSON `currentState.phase` / `iteration` / `lastUpdate` /
`focus` / `nextAction` / `blockers` + registry `phase` / `lastUpdate` were
NEVER updated post-Session 7. The slug carried `Phase: BLOCKED` for 14 days
past its un-blocking, mis-signaling to the pool / claim-rotation / Judge /
Auditor that the slug was still pre-Mathlib-fix.

Additionally, the pool entry `status: "available"` was set by some operator
(not Session 7's author) between 2026-04-27 and 2026-05-17, putting the slug
back into the claim rotation despite state.md still flagged BLOCKED. The
re-claim cycle that Session 6 explicitly wanted to stop has resumed.

**Pre-S8 drift inventory** (8 items):

| # | Surface | Pre-S8 | Should be | Severity |
|---|---|---|---|---|
| 1 | `state.md` Phase | `BLOCKED` | `ACT` (post-Session 7) | **HIGH** |
| 2 | `state.md` Iteration | `4 (last update: 2026-04-27 Session 6)` | `8` | HIGH |
| 3 | `state.md` Current Focus | `BLOCKED on Mathlib API drift ... 35 errors` | post-fix narrative | HIGH |
| 4 | `state.md` Active Approach | `None. File cannot build` | `limit_invariant_on_cylinder` proof | HIGH |
| 5 | `state.md` Blockers | `35 Mathlib API drift errors` | discharged via PR #14878 | HIGH |
| 6 | JSON `currentState.phase` | `BLOCKED` | `ACT` | HIGH |
| 7 | JSON `currentState.{focus, nextAction, iteration, blockers, attemptCounts}` | pre-Session-7 | Session-7-aware | HIGH |
| 8 | JSON `lastUpdate` + registry `phase` / `lastUpdate` | 2026-04-27 / OBSERVE / 2026-04-24 | 2026-05-17 / ACT / 2026-05-17 | MED |
| (bonus) | `sessions/` dir | ABSENT | bootstrap with S8 memo | LOW |

**S8 closes all drifts in a 4-file doc-only motion**:

1. `state.md` head — Phase BLOCKED → ACT; Iteration 4 → 8; Since refresh;
   prepend this S8 block above the historical sections (preserved verbatim
   below as "Current Focus (HISTORICAL — pre-Session 7)"); rewrite
   "Current Focus" / "Active Approach" / "Blockers" / "Next Action" to
   post-Session-7 state.
2. `src/data/research/problems/szemeredi-full-oq-01.json` — 7 edits:
   - `currentState.phase` BLOCKED → ACT
   - `currentState.focus` rewrite (Session 7 fixes + 1 sorry remaining)
   - `currentState.nextAction` rewrite (limit_invariant_on_cylinder next)
   - `currentState.iteration` 4 → 8
   - `currentState.attemptCounts` { total: 0, 0, 0 } → { 7, 1, 3 } (schema
     was zero'd; corrected per session history)
   - `currentState.blockers` 2-entry → [] (Mathlib drift discharged)
   - `lastUpdate` 2026-04-27 → 2026-05-17T00:50:00Z
3. `research/registry.json` — `phase` OBSERVE → ACT (Session 7 fixed errors,
   active development resumed); `lastUpdate` 2026-04-24 → 2026-05-17T00:50:00Z.
4. NEW `sessions/2026-05-17-s8-statesync-post-session7-mathlib-fixed-bootstrap.md`
   (~200 LOC, 9 sections).

**Explicit non-actions** (out of scope for S8 STATE-SYNC):
- No `.lean` edits. (Session 7 already shipped PR #14878 with the fixes;
  next Lean work is `limit_invariant_on_cylinder` activation at line 779,
  which is S9 ACT — needs Docker recovery + careful Prokhorov ingredient
  audit per knowledge.md Session 7 Next Steps.)
- No build verification. (Docker `info` hangs in 5 s; Session 7's "file
  should now be buildable" assertion is unverified by S8 — flagged in
  honesty calibration §7 of the S8 sessions memo.)
- No `knowledge.md` body edits. (Session 7 epilogue is the canonical
  Session 7 record; S8 is a state-syncing wrapper, not a new substantive
  session.)
- No `meta.json` edits. (Slug `szemeredi-full-oq-01` has gallery dir
  `src/data/proofs/szemeredi-full-oq-01/` but the numerics are mechanic
  territory; this S8 doesn't refresh them.)
- No `problem.md` / sibling slug / `lake-manifest.json` edits.
- No pool status change. (Pool was `available` pre-claim; was `in-progress`
  during my claim; will be `in-progress` post-this-PR-merge until Session 9
  validates the build; S8 author chooses NOT to invoke
  `FORCE_COMPLETE=1 update`. Per knowledge.md Session 7 step 4 the intended
  transition is "→ available once build confirmed", which S8 cannot
  perform without Docker.)

## Current Focus (POST Session 7 + S8 STATE-SYNC)
PR #14878 (merged 2026-05-02) fixed 6 Mathlib API drift root errors
(cascading to ~35 build failures) in `FurstenbergCorrespondenceOQ01.lean`.
File is presumed buildable at pin `2df2f0150c…` (v4.26.0) per Session 7's
assertion, but NOT yet Docker-verified in S8 (Docker `info` hangs;
host-cron territory).

**Remaining work** (1 real sorry):
- `limit_invariant_on_cylinder` at line 779 of
  `proofs/Proofs/FurstenbergCorrespondenceOQ01.lean`. The 60-line proof
  structure is documented in the file comment at line ~760. Once Docker
  recovers, S9 ACT can paste the proof and verify build.

## Active Approach (POST Session 7)
T-invariance limit proof via Prokhorov ingredients in Mathlib v4.26.
Cesàro infrastructure (Session 2) and `shift_iterate` / `cylinder_isClopen`
/ indicator / Boolean compact-space repairs (Session 7) all GREEN.

## Attempt Count (POST Session 7)
- Total attempts: 7 sessions (1 survey, 1 Cesàro, 1 proof-write blocked,
  1 documentation, 1 Mathlib API repair via PR #14878, 2 documentation).
  Plus S8 this STATE-SYNC.
- Current approach attempts: 1 (Session 7's Mathlib repair, merged)
- Approaches tried: Cesàro / T-invariance limit / Mathlib API repair

## Blockers (POST Session 7 + S8)
- None at the slug level. Slug is in an ACT-ready state for `limit_invariant_on_cylinder`.
- Host-side: Docker `info` hangs (5 s no Server: section) and disk 3.4 Gi
  avail (< 30 Gi cascade-safety floor). These are HOST blockers, not
  slug-content blockers. S9 ACT requires host recovery.

## Next Action (POST Session 7 + S8)
**S9 ACT** (Lean edit, host-recovery-gated):
1. Recover Docker daemon + free ≥ 30 Gi host disk.
2. `docker info` returns < 5 s + `df -h /` shows ≥ 30 Gi avail.
3. Build-verify current `main` HEAD compiles: `./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01`.
4. If build clean: paste the 60-line `limit_invariant_on_cylinder` proof at
   line 779 (structure documented in file comment line ~760).
5. Rebuild + ship S9 ACT PR.

After S9 ACT: S10 ACT for `seqCompact_probabilityMeasure_cantor`
(~150-200 lines via Prokhorov ingredients in Mathlib v4.26).

## Current Focus (HISTORICAL — pre-Session 7, frozen)
BLOCKED on Mathlib API drift in `FurstenbergCorrespondenceOQ01.lean`
(35 errors). Pool status set to `blocked` to stop the re-claim cycle.

## Active Approach (HISTORICAL — pre-Session 7)
None. File cannot build at current Mathlib pin (v4.26.0,
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67).

## Attempt Count (HISTORICAL — pre-Session 7)
- Total attempts: 4 sessions (1 survey, 1 build, 2 documentation/blocker)
- Current approach attempts: 0 (paused pending upgrade)
- Approaches tried: Cesàro infrastructure (success), T-invariance limit (proof
  written but unvalidated due to file-wide build blocker)

## Blockers (HISTORICAL — pre-Session 7)
- 35 Mathlib API drift errors in `FurstenbergCorrespondenceOQ01.lean`.
- No Lean build CI workflow to detect upstream rot on PRs.

## Next Action (HISTORICAL — pre-Session 7)
Operator must:
1. Upgrade `proofs/lake-manifest.json` Mathlib pin to a recent version, then
2. Repair the 35 errors (categories: renamed lemma, removed instance, tactic
   semantics, simp reduction — see knowledge.md Session 6 inventory), then
3. Update pool entry status from `blocked` back to `available` so the problem
   re-enters the depth-first claim rotation.

**Note**: items 1+2 were DISCHARGED by Session 7 / PR #14878 (2026-05-02).
Item 3 was performed by an unidentified operator some time between
2026-04-27 and 2026-05-17. S8 STATE-SYNC absorbs all three transitions
into the canonical surfaces.

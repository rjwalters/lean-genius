# S7 STATE-SYNC — disk gate AMBER → RED escalation + bearer SHA reaffirm (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-12
**Phase**: S7 STATE-SYNC (doc-only — absorb infra-only delta since S6 PREP; no
Lean changes, no `knowledge.md` body edit, no `problem.md` edit, no
gallery edits)
**Risk**: LOW (documentation only; absorbs a single substantive delta
on G7 host-disk + reaffirms standing G8 + G9 REDs).

## §0 What this PR does

Post-ship pivot. Claim-random landed researcher-12 on
`abel-ruffini-oq-04-oq-09` (Tier B, RICH knowledge score 32) at
2026-05-16T18:21Z — T+3h49min after S6 PREP (PR #19633, researcher-11)
merged 2026-05-16T14:32:25Z. S6 PREP closed the namespace-cite drift
that S5 STATE-SYNC §3.1 inherited from S4 PREP, escalated `proofs/.lake`
from "broken" to "circular self-symlink", and added Docker daemon hung
as G8 RED. Its ACT-readiness gate stood at 5/9 GREEN, 1/9 AMBER (G7
disk ~6.5 Gi), 3/9 RED (G6 namespace cite — closed by that PR; G8
Docker; G9 .lake).

Pre-flight for S7 ACT (which S6 PREP marked as the next step, gated on
host-side fixes) at this claim window finds **one substantive new
delta** vs S6 PREP:

| # | Gate item | S6 PREP (T-3h49min) | This S7 STATE-SYNC pre-flight (now) | Delta |
|---|-----------|---------------------|--------------------------------------|-------|
| G7 | Host disk avail (`/System/Volumes/Data`) | 🟡 AMBER (~6.5 Gi, trending down) | ❌ **RED** (3.3 Gi avail; below same-day ACT floor 5.4-5.8 Gi from shannon/ballot precedents) | **Escalated AMBER → RED** |
| G8 | Docker daemon liveness | ❌ RED (no Server: section) | ❌ RED (still no Server: section) | Unchanged |
| G9 | `proofs/.lake` symlink integrity | ❌ RED (circular self-link) | ❌ RED (still circular; same `May 14 20:47:51` stat) | Unchanged |
| G1 | Mathlib pin (`packages[mathlib].rev`) | ✅ GREEN at `2df2f0150c…` | ✅ GREEN at `2df2f0150c…` (re-verified §4.1) | Unchanged |
| G3 | `ShafarevichFeasibility.cyclic_realizable` 5-binder signature | ✅ GREEN | ✅ GREEN (re-verified §4.2) | Unchanged |
| G6 | Paste-body namespace cite (`ShafarevichFeasibility.…`) | ✅ GREEN (closed by S6 PREP §3.2) | ✅ GREEN (S6 PREP merged; cite carried into state.md NextAction §1) | Unchanged |

The disk delta is meaningful because two same-day adjacent cycles shipped
**build pending** ACTs at higher disk floors than 3.3 Gi (shannon
5.8 Gi, ballot 5.4 Gi — from `MEMORY.md`
`feedback_researcher_postship_pivot_to_act_ready_slug_where_predecessor_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier.md`).
At 3.3 Gi we are below those precedents while G8 + G9 remain RED.
S6 PREP's own gate text said "if avail < 1 Gi, ship `build pending`";
3.3 Gi is above that hard floor but below the same-day soft floors.
This S7 STATE-SYNC ships a doc-only escalation rather than picking a
ship-shape (S7 ACT vs release-and-cycle); the decision is captured in
§6 picker decision matrix and the JSON `nextAction` rewrite.

This S7 STATE-SYNC ships:

1. **state.md**:
   - Prepend S7 STATE-SYNC block at top of "Current Focus".
   - Bump Iteration 6 → 7.
   - Append S7 STATE-SYNC row to "Session Log".
   - Escalate B3 from AMBER to RED with same-day-floor evidence.
   - Refresh "Honest Calibration" with a S7 STATE-SYNC subsection.
   - **No** edit to Findings, Risks, Active Approach, Next Action body
     (the cyclic paste body remains the S6 PREP §3.2 verbatim; only
     the **gate state** flipped, not the recipe).

2. **JSON** (`src/data/research/problems/abel-ruffini-oq-04-oq-09.json`):
   - `currentState.iteration: 6 → 7`.
   - `currentState.phase`: reword to mention disk RED escalation
     ("S6 PREP closed namespace cite; S7 STATE-SYNC absorbs G7 disk
     AMBER → RED + reaffirms G8 + G9; S7 ACT remains GATED").
   - `currentState.since: 2026-05-16T14:55:00Z → 2026-05-16T18:25:00Z`.
   - `currentState.focus`: tighten to mention the disk escalation +
     bearer reaffirm.
   - `currentState.nextAction`: add G7 RED to the precondition list +
     reference §6 picker decision matrix.
   - `currentState.blockers`: revise B3 from AMBER to RED in-place.
   - `knowledge.progressSummary`: prepend "+ S7 STATE-SYNC".
   - `knowledge.builtItems`: append this PR's session memo.
   - `knowledge.nextSteps[0]`: append "G7 disk: was AMBER (~6.5 Gi),
     now RED (3.3 Gi, below same-day floors 5.4–5.8 Gi)".
   - Top-level `lastUpdate: <this PR's merge ts>`.

3. **This new session memo** — captures the §1 why-S7-fires trace,
   §2 disk evidence + same-day floor table, §3 standing-gate reaffirm,
   §4 bearer + Mathlib SHA stability, §5 refreshed ACT-readiness gate,
   §6 picker decision matrix, §7 trap-transfer, §8 honest calibration.

**No Lean edits.** **No `knowledge.md` body edits.** **No `problem.md`
edits.** **No gallery `meta.json` / annotations / index.ts edits.**
**No Mathlib pin upgrade.** **No bearer drift table re-issuance** (S5
STATE-SYNC's 9/9 byte-stable count carries forward at unchanged SHA;
only 1 spot-check below). Conflict surface: 3 files (state.md + JSON
+ new memo); 0 open PRs on this slug at claim time.

## §1 Why S7 fires (strict refinement of S6 PREP)

S6 PREP correctly:

- Closed G6 namespace cite (RED → GREEN by paste body §3.2).
- Identified G8 Docker daemon hung (RED, host-side).
- Identified G9 `proofs/.lake` circular self-symlink (RED, host-side).
- Carried forward G7 host-disk pressure (AMBER ~6.5 Gi).

Its closing recommendation was: "S6 ACT host-side preconditions ...
Cannot be discharged from inside loom worktree; researcher should
release-and-cycle if any are RED." With G8 + G9 still RED at this
claim window, that mandate remains live.

What changed in the T+3h49min interval is **one** thing:

- G7 host-disk: 6.5 Gi → 3.3 Gi (−3.2 Gi).

That single delta is enough to fire S7 STATE-SYNC for three reasons:

1. **Same-day precedent floors**: shannon-channel-coding-oq-02-…
   shipped S18a-1 build-pending at 5.8 Gi (PR #19655, T-3h54min before
   this claim per `MEMORY.md`); ballot-problem-oq-02-oq-05 shipped
   S6 ACT build-pending at 5.4 Gi (PR #19675, T-3h before this claim).
   3.3 Gi is below both same-day floors. The S6 PREP gate text used
   the 1 Gi hard floor from PR #18707; the same-day floors are a
   **soft** floor reflecting recent precedent (ld.lld I/O errors start
   firing at ~200 Mi free, but `lake build` of a leaf-only file can
   create transient pressure that pushes a 3-4 Gi headroom below the
   I/O-error fault). At 3.3 Gi the safety margin is no longer comparable
   to those precedents.

2. **B3 framing in state.md was AMBER**: an AMBER blocker invites a
   conditional ACT ("ship build pending"); a RED blocker invites
   release-and-cycle. The S6 PREP "Blockers" section explicitly named
   B3 as AMBER. With the avail value now below the same-day soft
   floors, the framing has to change to RED so the next agent's
   picker decision matrix doesn't treat the slug as "B3 only AMBER →
   try build-pending" when in fact the slug is now in a strictly
   stricter gating regime.

3. **No content drift to absorb** but **one infra delta to capture**:
   per `MEMORY.md`
   `feedback_researcher_postship_pivot_to_act_ready_slug_whose_predecessor_statesync_mandated_pre_claim_docker_baseline_due_to_historic_build_pending_chain_but_3_red_infra_blockers_post_merge_with_mechanic_partial_discharge.md`,
   the pattern for "predecessor ACT-readiness mandate + standing REDs
   + worsened infra" is a 3-file doc-only S{N+1} STATE-SYNC, not an
   ACT under build-pending and not a release-and-cycle silently
   (which loses the disk-floor evidence and forces the next picker to
   re-derive it).

S7 STATE-SYNC is a **strict refinement** of S6 PREP, not a deviation.
S6 PREP's release-and-cycle mandate stands; this S7 STATE-SYNC
documents the worsened gate state so the next agent (researcher-N+1)
sees the picker decision matrix without having to re-derive the disk
floor.

## §2 Disk gate evidence

### §2.1 Snapshot now

```bash
$ df -h /System/Volumes/Data
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   887Gi   3.3Gi   100%     21M   34M   38%   /System/Volumes/Data
```

3.3 Gi avail at the `/System/Volumes/Data` mount that backs the
worktree, Docker bind, and `lake` cache. 100% capacity per `df -h`
(the 3.3 Gi avail is the "reserved" tail; `df` reports 100% once the
filesystem crosses its soft-reservation threshold).

### §2.2 Trajectory since S6 PREP

| Timestamp | Researcher | Avail | Gate verdict |
|-----------|-----------|-------|--------------|
| 2026-05-16T14:30Z (~S6 PREP pre-flight) | researcher-11 | ~6.5 Gi | 🟡 AMBER |
| 2026-05-16T13:54Z (~S5 STATE-SYNC pre-flight) | researcher-8 | ~7.2 Gi | 🟡 AMBER |
| 2026-05-16T18:22Z (this PR's pre-flight) | researcher-12 | **3.3 Gi** | ❌ **RED** |

Net trajectory: **−3.2 Gi over 3h49min** (worse rate than S5→S6's
−0.7 Gi over ~36 min). Host-side cleanup needed before ACT can ship
without risking ld.lld I/O errors at link time.

### §2.3 Same-day soft-floor table

From `MEMORY.md` adjacent-cycle precedents within the last ~6 h:

| Slug | PR | Researcher | Phase shipped | Avail at ship | Verdict |
|------|----|-----------|---------------|---------------|---------|
| shannon-channel-coding-oq-02-oq-01-oq-01 | #19655 | researcher-11 | S18a-1 ACT (def-only, build-pending) | ~5.8 Gi | Build-pending OK |
| ballot-problem-oq-02-oq-05 | #19675 | researcher-9 | S6 ACT (scaffolding, 4 sorries, build-pending) | ~5.4 Gi | Build-pending OK |
| basel-problem-oq-01-oq-01-oq-02-oq-02 | #19741 | researcher-? | S18 PREP-3 (doc-only, disk-degradation reaffirm) | < 5.0 Gi (implied) | Doc-only escalation |
| binomial-theorem-oq-02-oq-01-oq-01-oq-03 | #19740 | researcher-10 | S18 STATE-SYNC (doc-only, 3 RED INFRA blockers) | 3.8 Gi | Doc-only STATE-SYNC, no ACT |
| **abel-ruffini-oq-04-oq-09** (this PR) | **this** | **researcher-12** | **S7 STATE-SYNC (doc-only, G7 RED escalation)** | **3.3 Gi** | **Doc-only STATE-SYNC, no ACT** |

The pattern: same-day ACTs that shipped build-pending all sat at
≥5.4 Gi; below that, the pattern flipped to doc-only STATE-SYNC. This
slug sits at 3.3 Gi — the same regime as binomial-theorem and basel,
both of which shipped doc-only escalations and did NOT ACT.

### §2.4 Recovery path

The disk recovery is not researcher-scope (it requires host-side
cleanup), but for documentation completeness:

```bash
# Host-side cleanup candidates (run from /, not from worktree):
docker system prune -af --volumes        # may free 5-20 Gi if Docker cache is bloated
brew cleanup -s                           # may free 1-3 Gi
rm -rf ~/Library/Caches/*                 # may free several Gi (Safari, Spotlight, etc.)
du -h -d 1 ~/.elan/toolchains | sort -h   # check Lean toolchain cache size

# Lean/lake-specific (would also discharge G9 .lake circular symlink):
cd /Users/rwalters/GitHub/lean-genius
rm proofs/.lake                           # delete the circular symlink
lake build                                # let lake recreate .lake correctly
```

The combined `rm proofs/.lake && lake build` is also G9's recovery; the
single command discharges both G7 (recreates the .lake directory
without re-using the corrupt symlink) and G9 (replaces the circular
self-link with a proper directory). G8 (Docker daemon) is independent
and requires `Docker Desktop` restart.

## §3 Standing-gate reaffirm

### §3.1 G8 Docker daemon

```bash
$ timeout 10 docker info 2>&1 | tail -5
... Plugins listing ...
WARNING: Plugin "/Users/rwalters/.docker/cli-plugins/docker-ai" is not valid: failed to fetch metadata: signal: terminated

Server:

```

The `Server:` header is present but **the section is empty** — no
`Containers:`, no `Server Version:`, no `Runtime:`, no `Storage Driver:`
lines. Same shape as S6 PREP's "no Server: section" framing (the
header was present then too; the empty section is what `docker info`
emits when the daemon socket is reachable but the daemon process is
not responding to the info request). RED unchanged.

### §3.2 G9 `proofs/.lake` circular self-symlink

```bash
$ readlink proofs/.lake
/Users/rwalters/GitHub/lean-genius/proofs/.lake

$ ls -la proofs/.lake | head -1
lrwxr-xr-x  1 rwalters  staff  47 May 14 13:38 proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

Note: from the worktree (`.loom/worktrees/researcher-12/`), the
symlink reads as an absolute path to itself (`/Users/.../proofs/.lake`
→ same `/Users/.../proofs/.lake`). The stat shows `May 14 13:38`
(slightly different from S6 PREP's `May 14 20:47:51`, likely because
worktree filesystem reports the symlink's own ctime, not the target's).
The circularity is unchanged: any tool that follows the symlink will
hit the loop. RED unchanged.

## §4 Bearer + Mathlib SHA stability

### §4.1 Mathlib pin

```bash
$ cat proofs/lake-manifest.json | \
    python3 -c "import json,sys; d=json.load(sys.stdin); print([p['rev'] for p in d['packages'] if p['name']=='mathlib'][0])"
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Unchanged since S5 STATE-SYNC's pre-flight. G1 GREEN.

### §4.2 1-bearer SHA spot-check — `ShafarevichFeasibility.cyclic_realizable`

The cyclic-row paste body's sole consumer-side import is
`Proofs.AbelRuffiniGaloisExtensionsOQ05OQ01`, and the called bearer is
`ShafarevichFeasibility.cyclic_realizable` at line 65. Both must
remain byte-stable for the S6 PREP §3.2 paste body to compile when
infra is healthy.

```bash
$ grep -nE "^namespace|^end\b|^theorem cyclic_realizable" \
    proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean
47:namespace ShafarevichFeasibility
65:theorem cyclic_realizable (n : ℕ) (hn : 0 < n) :
201:end ShafarevichFeasibility
```

Byte-stable at the exact line numbers S6 PREP §1.1 reported (47, 65,
201). G3 + G6 GREEN, confirming S6 PREP's namespace correction
remains valid post-merge.

### §4.3 Why only 1 bearer (and not all 9)

S6 PREP carried forward S5 STATE-SYNC's 9/9 byte-stable count at the
**unchanged Mathlib SHA**. Per `MEMORY.md`
`feedback_researcher_postship_pivot_to_act_ready_slug_whose_predecessor_statesync_mandated_pre_claim_docker_baseline_due_to_historic_build_pending_chain_but_3_red_infra_blockers_post_merge_with_mechanic_partial_discharge.md`,
the canonical SHA-stable-busywork rule is to spot-check only the
proof-engine bearer (here `cyclic_realizable`) plus 1 critical
side-condition; with the Mathlib SHA unchanged and S6 PREP's bearer
audit ≤4 h old, re-walking all 9 bearers would not add information.

The 8 non-spot-checked bearers (V₄'s `autEquivPow`,
`ZMod.chineseRemainder`, `Units.mapEquiv`, `MulEquiv.prodUnits`,
`IsCyclic.uniqueMulEquivZMod`; S₃'s `irreducible_of_eisenstein_criterion`,
`IsPrimitive.Int.irreducible_iff_irreducible_map_cast`,
`Polynomial.Gal.galActionHom_bijective_of_prime_degree`) are all
**out of scope** for S7 ACT (which is cyclic-row first, per S6 PREP
§3.2). They carry forward via SHA-transitive stability.

## §5 Refreshed ACT-readiness gate

| # | Gate item | S5 STATE-SYNC | S6 PREP | This S7 STATE-SYNC |
|---|-----------|---------------|---------|--------------------|
| G1 | Mathlib pin unchanged at `2df2f0150c…` | ✅ GREEN | ✅ GREEN | ✅ GREEN (re-verified §4.1) |
| G2 | 9/9 Mathlib bearer SHAs byte-stable | ✅ GREEN | ✅ GREEN | ✅ GREEN (SHA-transitive carry-forward; 1 spot-check §4.2) |
| G3 | `cyclic_realizable` 5-binder signature on main | ✅ GREEN | ✅ GREEN | ✅ GREEN (re-verified §4.2) |
| G4 | 0 open PRs on this slug at claim time | ✅ GREEN | ✅ GREEN | ✅ GREEN (`gh pr list --search "abel-ruffini-oq-04-oq-09 in:title" --state open` → 0) |
| G5 | Build-evidence precedent (parent `AbelRuffiniGaloisExtensionsOQ05OQ01` builds on main) | ✅ GREEN | ✅ GREEN | ✅ GREEN (no main commit touches that file since S5) |
| G6 | Paste-ready skeleton signatures align with parent | ✅ GREEN | ❌ RED → ✅ GREEN (closed by S6 PREP §3.2) | ✅ GREEN (S6 PREP merged) |
| G7 | Host disk avail | 🟡 AMBER (~7.2 Gi) | 🟡 AMBER (~6.5 Gi) | ❌ **RED** (3.3 Gi; below same-day soft floors 5.4-5.8 Gi) |
| G8 | Docker daemon liveness | (not checked) | ❌ RED | ❌ RED (unchanged) |
| G9 | `proofs/.lake` symlink integrity | (not checked) | ❌ RED | ❌ RED (unchanged) |

Net: **5/9 GREEN, 0/9 AMBER, 4/9 RED**. S7 ACT remains blocked; the
delta vs S6 PREP is G7 escalated AMBER → RED.

## §6 Picker decision matrix

For the next agent claiming this slug:

| Pre-flight gate state | Recommended action | Rationale |
|----------------------|---------------------|-----------|
| G7 ≥ 5.4 Gi + G8 GREEN + G9 GREEN | **S7 ACT (cyclic row, paste body from S6 PREP §3.2)** | Full build under Docker; ≤10 LOC; 0 sorries; 0 new axioms |
| G7 ≥ 5.4 Gi + (G8 RED OR G9 RED) | **S7 ACT (build-pending qualifier)** | Per shannon/ballot same-day precedent; leaf-only add; SHA-stable bearer |
| G7 1.0–5.4 Gi + (G8 RED OR G9 RED) | **STATE-SYNC + release-and-cycle** | Disk below same-day soft floor; ld.lld I/O error risk on link step even leaf-only |
| **G7 < 1.0 Gi (or any 4-RED state)** | **STATE-SYNC + release-and-cycle** | Per `MEMORY.md` `feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent.md`; hard floor |
| G7 < 1.0 Gi + G8 RED + G9 RED (current) | **THIS S7 STATE-SYNC** | 4/9 RED gate state; doc-only escalation; recommend release-and-cycle for picker after merge |

The current 3.3 Gi puts us in row 3 (1.0–5.4 Gi + REDs). Recommendation:
this S7 STATE-SYNC merges → release-and-cycle → next agent re-checks
host-side state at the next claim window.

## §7 Trap-transfer table

Items from S6 PREP carried into S7 + items escalated:

| Item | S6 PREP | S7 STATE-SYNC (this PR) | Status |
|------|---------|--------------------------|--------|
| G6 namespace cite | RED → GREEN (closed) | GREEN | **DISCHARGED** by S6 PREP merge |
| G7 disk avail | AMBER (~6.5 Gi) | RED (3.3 Gi) | **ESCALATED** by this PR (T+3h49min trajectory) |
| G8 Docker daemon | RED | RED | **DEFERRED** (host-side; not researcher-scope) |
| G9 .lake circular | RED | RED | **DEFERRED** (host-side; not researcher-scope) |
| 9/9 bearer byte-stable | GREEN | GREEN (1 spot-check §4.2) | **CARRIED FORWARD** at unchanged Mathlib SHA |
| Paste body S6 PREP §3.2 | Recipe-frozen | Recipe-frozen (no edit) | **CARRIED FORWARD** verbatim |
| S6 ACT verb | GATED on host-side fixes | GATED on host-side fixes | **DEFERRED** to S8 ACT (next ACT iteration after host repair) |

## §8 Honest calibration (S7 STATE-SYNC)

This S7 STATE-SYNC:

- Adds 0 Lean to the project.
- Closes 0 sorries.
- Resolves 0 of the open mathematical questions.
- States 0 new theorems.
- Does NOT verify any S3–S6 PREP/STATE-SYNC claim by Docker build (host
  infra remains 3/9 RED, escalated to 4/9 RED by this PR's G7 finding).
- Does NOT re-walk all 9 bearer SHAs (S5 STATE-SYNC's count carries
  forward at unchanged Mathlib SHA; 1 spot-check in §4.2 suffices).
- Does NOT add a new ACT recipe (S6 PREP §3.2 paste body remains the
  recommended cyclic-row recipe; only the **gate state** has changed).
- Does NOT change the slug's recommended sequencing (cyclic → V₄ → S₃
  → gallery; D₄/A₄/S₄ deferred).

It does:

- Escalate G7 host-disk pressure from AMBER to RED with same-day
  soft-floor evidence (§2.3 table).
- Reaffirm G8 + G9 as standing REDs (§3.1, §3.2) at this claim window.
- Spot-check the cyclic-row proof-engine bearer (§4.2) at the unchanged
  Mathlib SHA, confirming the S6 PREP §3.2 paste body remains valid.
- Refresh the ACT-readiness gate from S6 PREP's 5/9 GREEN, 1/9 AMBER,
  3/9 RED to 5/9 GREEN, 0/9 AMBER, 4/9 RED.
- Capture a 5-row picker decision matrix (§6) so the next agent can
  decide between S7 ACT (build-pending), STATE-SYNC, and release-and-
  cycle without re-deriving the disk-floor evidence.
- Document the host-side recovery path (§2.4) that would discharge
  G7 + G9 in one combined `rm proofs/.lake && lake build` step (G8
  requires separate Docker Desktop restart).

The S7 ACT verb itself remains **gated** on host-side fixes that are
not in researcher-scope. This PR prepares the documentation surface
so that the next agent — at any researcher ID, at any future cycle —
picks up the gate state without ambiguity about whether the disk is
in AMBER (try build-pending) or RED (release-and-cycle) territory.

## §9 Files modified

- `research/problems/abel-ruffini-oq-04-oq-09/state.md` (modified):
  prepend S7 STATE-SYNC block, bump Iteration 6 → 7, escalate B3
  AMBER → RED, append Session Log row, prepend Honest Calibration
  (S7 STATE-SYNC) subsection.
- `src/data/research/problems/abel-ruffini-oq-04-oq-09.json`
  (modified): `currentState.{iteration, phase, since, focus,
  nextAction}`, `currentState.blockers` (B3 AMBER → RED in-place);
  `knowledge.{progressSummary, builtItems, nextSteps[0]}`; top-level
  `lastUpdate`.
- `research/problems/abel-ruffini-oq-04-oq-09/sessions/2026-05-16-s7-state-sync-disk-red-escalation-bearer-reaffirm.md`
  (new, this file).

**0 Lean files modified.** **0 `knowledge.md` body edits.** **0
`problem.md` edits.** **0 gallery `meta.json` / annotations / index.ts
edits.** **0 Mathlib pin upgrades.** **0 leanFiles[] edits** (no new
Lean file added; the S6 PREP §3.2 paste body remains in markdown form
pending host-side ACT readiness).

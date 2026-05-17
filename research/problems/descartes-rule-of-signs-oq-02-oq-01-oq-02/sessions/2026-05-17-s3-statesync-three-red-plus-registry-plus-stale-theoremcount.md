# Session 3 — S3 STATE-SYNC (researcher-10, 2026-05-17T01:05Z)

**Mode**: STATE-SYNC (doc-only catchup; no Lean / no gallery / no problem.md / no knowledge.md body edits)
**Outcome**: 3 RED INFRA blockers absorbed + registry phase NEW→PREP catchup + canonical `leanFiles[6].theoremCount` 28→26 corrected. ACT remains structurally foreclosed.
**Files modified**:
- `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json` (10 fields)
- `research/registry.json` (2 fields for this slug only)
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md` (head prepend)
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/sessions/2026-05-17-s3-statesync-three-red-plus-registry-plus-stale-theoremcount.md` (NEW — this file)

---

## §1. Why S3 fires (strict refinement of S2 PREP, not deviation)

S2 PREP (#19787, researcher-8, 2026-05-16T19:16Z) shipped four things
and left a precise pre-ACT gate:

1. Mathlib bearer recheck — 5 spot-checks at SHA `2df2f0150c…`,
   including the not-yet-exercised Step-A bearer
   `Polynomial.continuous`.
2. Paste-ready `private lemma sturmVariations_locally_constant` draft
   in session memo §3.
3. Canonical research JSON catchup — phase `COMPLETED → PREP`, status
   `completed → active`, `nextAction` rewrite, `lastUpdate` bump.
4. ACT-readiness gate snapshot with explicit RED items 1 (disk 3.5 Gi)
   and 2 (Docker hung).

S2's `nextAction` was: "S3 ACT — land Step-A lemma. Gated on host disk
recovery ≥30 Gi avail AND `docker info` responsive < 5 s."

At T+5h45m (S3 claim window opening 2026-05-17T00:52Z), the host state
has worsened, NOT recovered:

- Disk 3.5 Gi → **2.9 Gi** avail / 100% used. (-0.6 Gi / -17%.)
- Docker daemon: still hung (`docker info` returns Client: section
  promptly but Server: section completely empty — same shape as S2's
  "no return < 30 s").
- NEW: `proofs/.lake → itself` circular self-symlink. Not flagged at
  S2 — either pre-existing and not spot-checked, or appeared in the
  intervening window. Either way it now structurally blocks any Lake
  operation, including pin verification.

Three separate drift threads also accumulated/persisted that S2 PREP
either did not address or could not address inside its own scope:

- **A.** Registry entry phase: NEW (21d stale — last touched
  2026-04-26T14:51Z when the slug was first created).
- **B.** Canonical JSON `leanFiles[6].theoremCount: 28` vs actual file
  → 26. S2 PREP explicitly deferred `leanFiles[]` numerics.
- **C.** 3-RED gate snapshot needs explicit blocker entry in
  `currentState.blockers` (S2 had 2 entries; G9 is new).

S3 STATE-SYNC absorbs A, B, C in a single doc-only PR. It does NOT
land Step-A (foreclosed by G7+G8+G9) and does NOT re-PREP (the recipe
is already paste-ready in S2's memo §3 and Mathlib pin is byte-stable;
re-drafting would be busywork). The session is a **strict refinement
of S2 PREP's "gated on host recovery" wording**, not a deviation: the
gate is still set and still failing.

This matches memory:
`feedback_researcher_postship_pivot_to_prep_phase_slug_with_old_prep_predecessor_and_three_red_infra_plus_three_stale_thispr_loci`
(old PREP predecessor — here only 5h45m, not 11h, but the 3-RED-plus-
drift shape applies). It is **distinct** from memories where the
predecessor is STATE-SYNC, or where mechanic discharged numerics
mid-window: no intervening mechanic touched this slug; the predecessor
is PREP, not STATE-SYNC.

## §2. The 3 RED INFRA blockers in detail

### §2.1. G7 — host disk 2.9 Gi avail / 100% used

```
$ df -h /Users/rwalters
Filesystem      Size    Used   Avail Capacity iused ifree %iused  Mounted on
/dev/disk3s5   926Gi   887Gi   2.9Gi   100%     21M   31M   41%   /System/Volumes/Data
```

| Snapshot          | Avail   | Δ vs prior |
|-------------------|---------|------------|
| S1 OBSERVE        | 6.9 Gi  | —          |
| S2 PREP           | 3.5 Gi  | -3.4 Gi    |
| S3 STATE-SYNC     | 2.9 Gi  | -0.6 Gi    |

S2 PREP's nextAction gate is "≥30 Gi avail". Current is 2.9 Gi (10×
short). Same-day same-cluster precedent for soft floor:
- shannon-channel-coding S18a-1 ACT (researcher-11, PR #19655): 5.8 Gi
  build-pending qualifier — soft floor at ~5.8 Gi.
- ballot-problem-oq-01-oq-02 ACT (researcher-8): 5.4 Gi — soft floor
  at ~5.4 Gi.
- abel-ruffini-oq-04-oq-09 PREP-escalation (researcher-12, PR #19755):
  3.3 Gi — STATE-SYNC-only territory.

2.9 Gi is **below** all three same-day soft floors. Build-pending ACT
is not available; STATE-SYNC-only is the maximal safe action.

**Recovery (researcher-side notes, not run from this PR)**:
```bash
# Inspect Docker disk hog candidates
docker system df 2>&1 || echo "Docker daemon hung — skip"
# Inspect lake build cache
du -sh /Users/rwalters/GitHub/lean-genius/proofs/.lake 2>/dev/null
# Likely largest reclaimables (do NOT run blindly in researcher PR):
#   docker system prune -af --volumes        (when daemon recovers)
#   rm -rf /Users/rwalters/Library/Caches/{...}
#   git -C /Users/rwalters/GitHub/lean-genius gc --aggressive
```

### §2.2. G8 — Docker daemon Server: unreachable

```
$ timeout 5 docker info 2>&1
Client:
 Version:    29.4.1
 Context:    desktop-linux
 ... (Client section returns promptly)
Server:
                  ← empty, no fields, no error message printed
$ echo "exit=$?"
exit=0                  ← `docker info` exits 0 despite empty Server
```

| Snapshot     | `docker info` Server | Build allowed? |
|--------------|----------------------|----------------|
| S1 OBSERVE   | GREEN < 5 s          | YES            |
| S2 PREP      | hung > 30 s          | NO             |
| S3 STATE-SYNC | exits 0, Server: empty | NO             |

The S2→S3 wording change ("hung" → "exits 0, Server: empty") is just a
more precise diagnostic — both indicate full daemon unreachable. The
build cycle (`./proofs/scripts/docker-build.sh`) is structurally
foreclosed regardless.

### §2.3. G9 — `proofs/.lake → itself` circular self-symlink (NEW)

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 May 16 09:04 .lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

This is a self-loop: `proofs/.lake` is a symlink to itself. Any Lake
operation that resolves the path will spin. Not flagged at S2 — either
pre-existing and unchecked, or created in the intervening window
(no obvious trigger from the worktree side; possibly a stale recovery
state from an earlier daemon crash).

**Recovery (researcher-side notes, not run from this PR)**:
```bash
# Surgical recovery — NOT run in this PR:
cd /Users/rwalters/GitHub/lean-genius/proofs
rm .lake
# Then re-init or restore from cache as needed by docker-build.sh
```

This matches the `.lake → itself` pattern in memory
`feedback_researcher_postship_pivot_to_act_ready_slug_whose_predecessor_statesync_mandated_pre_claim_docker_baseline_..._three_red_infra_blockers_post_merge`
(researcher-10 binomial-theorem slug, same `proofs/.lake → itself`
shape).

## §3. Drift inventory — three threads absorbed at S3

### §3.1. Thread A — registry.json phase NEW (21d stale)

**Before**:
```json
{
  "slug": "descartes-rule-of-signs-oq-02-oq-01-oq-02",
  "phase": "NEW",
  "path": "full",
  "started": "2026-04-26T14:51:07.083Z",
  "status": "active",
  "lastUpdate": "2026-04-26T14:51:07.083Z"
}
```

**After**:
```json
{
  "slug": "descartes-rule-of-signs-oq-02-oq-01-oq-02",
  "phase": "PREP",
  "path": "full",
  "started": "2026-04-26T14:51:07.083Z",
  "status": "active",
  "lastUpdate": "2026-05-17T01:05:00Z"
}
```

S2 PREP corrected canonical JSON but did not mirror to registry.
Without the fix, future `claim-random` invocations could fail to
prioritize this slug correctly via the registry's knowledge index, or
seekers could incorrectly re-discover it as "fresh".

### §3.2. Thread B — canonical `leanFiles[6].theoremCount` 28→26

**Evidence the truth is 26, not 28**:

```
$ F=proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean
$ wc -l $F
     458 proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean
$ grep -cE '^(protected |private |noncomputable )*(theorem|lemma) ' $F
26
$ grep -cE '^(def|noncomputable def|opaque def) ' $F
6
$ grep -c '^axiom ' $F
1
$ grep -c '\bsorry\b' $F
0
```

S1 OBSERVE problem.md states **"26 theorems"** explicitly in the
opening problem statement.

S1 OBSERVE knowledge.md §1 enumerates the declaration list — counting
`kind = theorem` rows yields 26.

Git log shows the file is unchanged in content since PR #19454
(commit `ecb47b35601`, 2026-05-16T01:55Z) which **created** the file
with 458 LOC and 26 theorems (verified via `git show $REV^:$F
2>/dev/null | grep -cE '…' = 0` and `git show $REV:$F | grep -cE '…' =
26`). The 28-count was a baked-in miscount from initial JSON entry.

**This PR**: `leanFiles[6].theoremCount: 28 → 26`. All other 8
`leanFiles[i]` entries are NOT touched at S3 — out of researcher
scope, deferred to mechanic if drift exists.

### §3.3. Thread C — gallery meta.json mirror (DEFERRED)

`src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/meta.json`
also carries the same stale `leanFile.theoremCount: 28`. S3 STATE-SYNC
**does not touch gallery meta.json** — that is mechanic batch-sync
territory (per memory
`feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`).
Flagged in canonical `currentState.nextAction`:

> "Flag gallery `src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/meta.json` `leanFile.theoremCount: 28` for mechanic batch-sync (likely needs same fix across ≥1 sibling descartes meta.json — out of researcher scope)."

Researcher does NOT cross into mechanic responsibilities; the mechanic
agent has its own canonical-count conventions, Python `ensure_ascii`
handling, and batch-sync sibling enumeration.

## §4. ACT-readiness gate snapshot (S3 STATE-SYNC, 2026-05-17T01:05Z)

| # | Item                                                | Status   | Notes (S3)                                                                       |
|---|-----------------------------------------------------|----------|----------------------------------------------------------------------------------|
| 1 | host disk ≥ 30 Gi avail                             | **RED**  | 2.9 Gi avail (worsened from S2's 3.5 by -0.6 Gi); 10× short of gate              |
| 2 | Docker daemon responsive (`docker info` Server)     | **RED**  | Server: section empty (unchanged from S2's hung)                                 |
| 3 | no merge conflicts in target file                   | GREEN    | file unchanged since `ecb47b35601` (PR #19454); HEAD is `43bed8ca045` mechanic   |
| 4 | Mathlib pin unchanged                               | GREEN    | `2df2f0150c…` v4.26.0 — byte-stable from S2; carry-forward                       |
| 5 | paste-ready Lean drafted under `#check`             | GREEN    | inherited from S2 PREP memo §3                                                   |
| 6 | no overlapping open PR                              | GREEN    | `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 state:open"` → 0 |
| 7 | expected ACT LOC delta ≤ 180 per cycle              | GREEN    | Step-A draft is 80–120 LOC, well under cap                                       |
| 8 | ACT memo template prepared                          | GREEN    | naming convention inherited from S1/S2                                           |
| 9 | `proofs/.lake` is a real directory (NEW)            | **RED**  | self-symlink loop — Lake operations spin                                         |

**Verdict**: ACT-readiness **NOT MET** (items 1, 2, 9 RED). S4 must
either be another STATE-SYNC (if host worsens or new drift accumulates)
or S3-equivalent ACT (if host recovers AND no new drift).

## §5. Mathlib bearer carry-forward at SHA `2df2f0150c…`

S2 PREP's 5-spot bearer recheck recorded `Polynomial.continuous`
present in `Mathlib/Topology/Algebra/Polynomial.lean` at 8668 bytes.

S3 does **not** re-walk all 5 bearers — that would be busywork per
memory `feedback_researcher_skip_5-9_bearer_rewalk_when_sha_stable`.
Justification:

1. Mathlib pin (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) byte-stable
   since S2: `jq -r '.packages[] | select(.name=="mathlib") | .rev'
   proofs/lake-manifest.json` returns the same SHA.
2. No intervening Mathlib PR could affect the pinned commit — pins are
   immutable.
3. G9 (`proofs/.lake → itself`) prevents direct file inspection on the
   pinned tarball without surgical recovery — and the recovery is out
   of researcher-PR scope.

Bearer status: **CARRY-FORWARD GREEN** from S2. Net verdict: Step-A
recipe in S2 memo §3 remains valid if/when ACT becomes available.

## §6. Picker decision matrix for S4

Six-row matrix anticipating S4's claim window:

| Scenario                                                                     | Disk    | Docker Server | `.lake` | Decision                  |
|------------------------------------------------------------------------------|---------|---------------|---------|---------------------------|
| All 3 GREEN                                                                  | ≥30 Gi  | responsive    | dir     | **S3-ACT** Step-A land    |
| Disk recovered, Docker still hung, `.lake` fixed                             | ≥30 Gi  | empty         | dir     | **S4 STATE-SYNC** (gate2) |
| Disk recovered, Docker GREEN, `.lake` still self-loop                        | ≥30 Gi  | responsive    | loop    | **S4 STATE-SYNC** (gate9) |
| Disk still RED, all else GREEN                                               | <30 Gi  | responsive    | dir     | **S4 STATE-SYNC** (gate1) |
| Worsened on any axis vs S3 (e.g., disk <2 Gi, or NEW G10 blocker)            | any     | any           | any     | **S4 STATE-SYNC** absorb  |
| Unchanged from S3 (3 RED still)                                              | 2.9 Gi  | empty         | loop    | **S4 STATE-SYNC** carry   |

Rule: ACT only when **all** 3 host gates clear AND no new drift. Else
STATE-SYNC absorbs and waits.

## §7. Explicit non-actions (what S3 does NOT do)

1. **No `.lean` edits** — Step-A draft remains in S2 memo §3; landing
   gated by G7+G8+G9.
2. **No gallery meta.json edits** — mechanic territory; flagged in
   nextAction.
3. **No problem.md edits** — already accurate (says 26).
4. **No knowledge.md body edits** — already accurate; only the
   in-canonical-JSON `knowledge.progressSummary` field is prepended.
5. **No sibling `leanFiles[i]` checks/edits** — researcher scope is
   own slug only.
6. **No predecessor session memo edits** — immutable.
7. **No lake-manifest.json edits** — SHA byte-stable; G9 self-loop
   prevents direct inspection but pin is verified via stored file.
8. **No host-side recovery commands run** — researcher PRs do not
   run shell ops; recovery is operator/daemon territory.
9. **No bumping** `currentState.attemptCounts.approachesTried` (still
   1, the multi-cycle PREP+ACT plan — STATE-SYNC is not a new
   "approach", it is housekeeping inside the existing plan).
10. **No `cs.phase` change** — STATE-SYNC is a session type within
    PREP-phase, not a phase transition. Phase remains PREP.

## §8. Honesty calibration

- This PR is doc-only catchup. It does **not** advance the proof of
  Sturm's theorem or discharge `sturm_exact_count_axiom`.
- It absorbs accumulated drift (registry, leanFiles count, blockers
  list) and updates the ACT-readiness gate snapshot.
- The "value" delivered is preventing pool-drift symptoms (registry
  showing NEW when canonical is iter=3; future seeker mis-prioritizing)
  and keeping the canonical record consistent with the actual file.
- The Step-A lemma remains undrafted-and-unlanded — same status as
  end-of-S2. No regression, no advance.
- The mechanic still needs to fix gallery meta.json `theoremCount: 28`
  for this slug (and likely siblings); this PR explicitly does NOT
  attempt that.

## §9. Memory citations

- `feedback_researcher_postship_pivot_to_prep_phase_slug_with_old_prep_predecessor_and_three_red_infra_plus_three_stale_thispr_loci`
  — 3 RED INFRA + drift absorption ship shape (this is closest match)
- `feedback_researcher_claim_random_re_rolls_same_slug_due_to_registry_phase_new_vs_canonical_observe_iter1`
  — registry phase NEW vs canonical drift pattern
- `feedback_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap`
  — canonical theoremCount regex; ensure_ascii Python JSON trap
- `feedback_researcher_postship_pivot_to_act_ready_slug_whose_predecessor_statesync_mandated_pre_claim_docker_baseline_..._three_red_infra_blockers_post_merge`
  — `.lake → itself` self-loop pattern from prior researcher-10 binomial slug
- `feedback_mechanic_pnpm_build_regenerates_all_research_jsons` — do NOT
  run `pnpm build`; validate with `python3 json.load` instead
- `feedback_worktree_absolute_path_lands_in_main_repo` — Edit/Read/Write
  resolved correctly into `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-10/...`
  (worktree-local), confirmed via `git rev-parse --show-toplevel`

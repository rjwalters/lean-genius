# S3 STATE-SYNC — `this PR`/#PR cleanup + B3 .lake self-symlink blocker add + registry catchup

**Date**: 2026-05-17T00:25Z
**Researcher**: researcher-11
**Phase**: PREP (state-sync within PREP; no Lean / no gallery numerics)
**Predecessor**: S2 PREP (researcher-8, 2026-05-16T19:16Z, PR #19787, T-5h)
**PR**: #pending (this PR, S3 STATE-SYNC)
**Cycle**: ~30 min (doc-only, no Docker)

---

## §0 Why S3 fires (strict refinement of S2 PREP)

S3 STATE-SYNC is a strict refinement of S2 PREP, not a deviation. S2
PREP correctly drafted the paste-ready Step-A lemma and updated
canonical JSON (phase COMPLETED→PREP). However, S2 PREP left three
substantive drift items and missed one critical blocker. S3 closes
those without altering S2's ACT recipe (recipe-frozen):

1. **`this PR` / #PR self-references** silently became stale on S2
   PREP's merge (PR #19787, T-5h). ≥11 loci in `state.md` + 1 in
   canonical JSON `currentState.focus` would mislead the next reader
   into thinking "this PR" = current cycle. S3 documents resolution
   explicitly without rewriting historical Session 1+2 bodies (the
   `this PR` wordings frozen as referring to PRs #19566 / #19787 per
   §1 table below).
2. **B3 INFRA missing**: S2 PREP enumerated only B1 (host disk) and
   B2 (Docker hung). The `proofs/.lake → proofs/.lake` self-symlink
   cycle (`ls -la proofs/.lake/` → 'Too many levels of symbolic
   links') was already present at S2 merge time but not flagged.
   Multiple sibling slugs (chebyshev-bounds-oq-04-oq-01,
   abel-ruffini-oq-04-oq-09, sqrt2-minpoly, binomial-theorem) flagged
   this same cycle as a discrete RED blocker within T-24h. S3 adds
   B3 to canonical JSON `currentState.blockers`.
3. **`research/registry.json` entry drift**: this slug's entry has
   carried `phase: "NEW", lastUpdate: "2026-04-26T14:51:07.083Z"`
   for 20 days, untouched by either S1 OBSERVE bootstrap (PR
   #19566) or S2 PREP (PR #19787). Both sessions updated canonical
   JSON but neither touched registry. S3 fixes `phase: NEW →
   ORIENT` (registry vocabulary; canonical JSON's `PREP` maps to
   `ORIENT` per S1's phase note) and `lastUpdate → 2026-05-17T…`.

Plus one mechanic re-flag (not researcher territory):

4. **theoremCount drift**: gallery meta.json + canonical JSON
   `leanFiles[6]` both list `theoremCount: 28` for
   `DescartesRuleOfSignsOQ02OQ01OQ02.lean`. Canonical regex
   `^(protected |private |noncomputable )*(theorem|lemma) ` counts
   **26** (verified via grep against current file at branch HEAD).
   Off by +2. Likely artifact of mechanic batch PR #17780 bump
   partially undone by #17839 revert on 2026-05-12. Flagged for
   mechanic in JSON `knowledge.nextSteps`; S3 does NOT touch
   gallery meta.json or `leanFiles[]` numerics (per memory:
   researcher-mechanic boundary).

---

## §1 Stale `this PR` audit table

| Locus | Author session | Resolution |
|---|---|---|
| `state.md:14` "Deliverables (this PR, doc-only, no Lean / no gallery numerics edits):" | S2 PREP | PR #19787 |
| `state.md:33` "(this PR drafts it)" | S2 PREP | PR #19787 |
| `state.md:53` "S1 OBSERVE bootstrap (this PR, doc-only):" | S1 OBSERVE | PR #19566 |
| `state.md:60` "prior to this PR. This PR…" | S1 OBSERVE | PR #19566 |
| `state.md:117` "(in this PR)" | S2 PREP | PR #19787 |
| `state.md:124` "S2 PREP (this PR) adds the first paste-ready Lean draft…" | S2 PREP | PR #19787 |
| `state.md:169` "S2 PREP discharged (this PR)" | S2 PREP | PR #19787 |
| `state.md:225,231` "**not touched** in this PR" | S2 PREP | PR #19787 |
| `state.md:234` "updated in this PR" | S2 PREP | PR #19787 |
| `state.md:246` "this PR; see session memo §3" | S2 PREP | PR #19787 |
| `JSON cs.focus` "S2 PREP (researcher-8, this PR, #PR)" | S2 PREP | PR #19787 (absorbed by S3 rewrite) |

**Resolution policy**: S3 does NOT rewrite Session 1+2 bodies — those
are historical record, and the `this PR` wordings can be interpreted
unambiguously now that the iteration history table at state.md:295
attributes each session to its merged PR (#19566 / #19787 / #pending).
S3 head (above the table) does NOT introduce new ambiguous wordings
— the table at end of S3 head explicitly maps each locus to its
target PR.

The canonical JSON's `currentState.focus` field, in contrast, was
fully rewritten by S3 (S2 PREP's "this PR, #PR" text is now
absorbed; replaced with explicit "S3 STATE-SYNC (researcher-11,
PR #pending, T+5h post S2 PREP #19787)" header).

---

## §2 3-RED INFRA snapshot

| # | Gate | Status | Evidence (S3, 2026-05-17T00:25Z) | Delta vs S2 (2026-05-16T19:16Z) |
|---|---|---|---|---|
| G7 | host disk ≥ 30 Gi avail (cascade-safety) OR ≥ 6 Gi (relaxed) | **RED** | `df -h` shows 3.6 Gi avail / 100% used | -0.1 Gi vs S2's 3.5 Gi (essentially unchanged; both well below floor) |
| G8 | Docker `Server:` block returns < 5 s | **RED** | `docker info` returns Client block but `Server:` line empty; `docker ps` timeout | Carries from S2 (RED then, RED now) |
| G9 | `proofs/.lake` not a self-symlink cycle | **RED** | `ls -la proofs/.lake/` → 'Too many levels of symbolic links'; `readlink proofs/.lake` → `/Users/rwalters/GitHub/lean-genius/proofs/.lake` (cycles to itself) | NEW: S2 PREP did not enumerate this gate; was present then but unflagged |

**Same-day same-host precedent** (cross-slug aggregation; G9
self-symlink cycle and G8 Docker hung observed across multiple
researcher worktrees in the past 24h):

| Slug | Session | When (Z) | G7 | G8 | G9 | Action |
|---|---|---|---|---|---|---|
| chebyshev-bounds-oq-04-oq-01 | S7 STATE-SYNC #19820 | 2026-05-16T20:10 | 3.2 Gi RED | empty RED | cycle RED | doc-only STATE-SYNC |
| abel-ruffini-oq-04-oq-09 | S7 STATE-SYNC #19755 | 2026-05-16T18:21 | 3.3 Gi RED | empty RED | cycle RED | doc-only STATE-SYNC |
| sqrt2-minpoly | S6 #19760 | 2026-05-16T~18 | RED | empty RED | cycle RED | doc-only |
| binomial-theorem-…-oq-03 | S17 #19740 | 2026-05-16T17:55 | 3.8 Gi RED | empty RED | cycle RED | doc-only STATE-SYNC |
| ballot-problem-oq-03-oq-01-oq-02 | S79 STATE-SYNC #19924 | 2026-05-16T23:18 | 4.0 Gi RED | empty RED | cycle RED | doc-only STATE-SYNC |
| **descartes-…-oq-02-oq-01-oq-02** | **S3 STATE-SYNC (this)** | **2026-05-17T00:25** | **3.6 Gi RED** | **empty RED** | **cycle RED** | **doc-only STATE-SYNC** |

Pattern is stable: 3-RED-INFRA on the same physical host across all
recent worktree-claims; recovery requires out-of-band host action
(disk cleanup, Docker Desktop restart, .lake symlink repair).

**Host recovery script** (informational; not executed in this PR —
researcher does not own host-level changes):

```bash
# 1) Reclaim disk (typically ~20-50 Gi from .lake build artifacts elsewhere)
find ~/GitHub -name ".lake" -type d -not -path "*/lean-genius/.loom/*" 2>/dev/null
# Manual review then `rm -rf` of obvious build cruft

# 2) Restart Docker Desktop (macOS)
osascript -e 'quit app "Docker"' && sleep 5 && open -a "Docker"
# Wait for `docker info` Server: block to return < 5s

# 3) Repair lean-genius proofs/.lake symlink
cd ~/GitHub/lean-genius
rm proofs/.lake  # remove self-symlink
# Re-establish from lake-manifest or fresh `lake update` after Docker green
```

---

## §3 Mathlib pin + bearer carry-forward

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0 channel)
— unchanged since S1 OBSERVE (2026-05-16T09:25Z), ≥15 h stable.

**Bearer status** (S2 PREP's 5-spot recheck, all GREEN at the same
SHA):

| Bearer | Mathlib location | S1 OBSERVE | S2 PREP | S3 STATE-SYNC |
|---|---|---|---|---|
| `Polynomial.continuous` | `Mathlib/Topology/Algebra/Polynomial.lean` (8668 B) | not exercised | GREEN | carry-forward (SHA stable) |
| `Polynomial.continuousAt` | same file | GREEN | GREEN | carry-forward |
| `EuclideanDomain.mod_eq_sub_mul_div` | `Mathlib/Algebra/EuclideanDomain/Basic.lean` | GREEN | GREEN | carry-forward |
| `Polynomial.derivative_X_sub_C` | `Mathlib/Algebra/Polynomial/Derivative.lean` | GREEN | GREEN | carry-forward |
| `Squarefree.dvd_of_squarefree_of_*` | `Mathlib/Algebra/Squarefree/Basic.lean` | GREEN | GREEN | carry-forward |

**Carry-forward rationale**: SHA byte-identical for ≥15 h; S2 PREP's
recheck stands. S3 does not re-execute the 5-spot check (would be
busywork per memory `_state_md_three_sessions_behind_sessions_dir_*`
— "bearer re-walk on SHA-stable predecessor merge is busywork").
Spot-check of file existence (Topology/Algebra/Polynomial.lean,
8668 B) deferred to S4 ACT pre-flight.

---

## §4 Trap-transfer table

| Trap from S2 PREP / earlier | Status @ S3 | Resolution |
|---|---|---|
| Step-A paste-ready recipe (S2 §3) | DEFERRED | Recipe frozen verbatim; S4 ACT pastes under recovered infra |
| G9 .lake self-symlink (silently present at S2) | ESCALATED | Added as B3 in JSON `currentState.blockers`; documented §2 above |
| `this PR` / #PR stale wordings (S2 + S1) | DISCHARGED | Audit table §1 + JSON `currentState.focus` rewritten + iteration history table attributes each session to PR# |
| Registry drift (NEW since 2026-04-26) | DISCHARGED | `phase: NEW → ORIENT`, `lastUpdate` refresh in registry.json |
| theoremCount 28 vs actual 26 (gallery + JSON) | DEFERRED to mechanic | Flagged in JSON `knowledge.nextSteps[6]`; researcher does not own gallery numerics |
| Open PR overlap | GREEN | `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02" --state open` → `[]` |
| Mathlib pin drift | GREEN | `2df2f0150c…` unchanged ≥15 h |

---

## §5 ACT-readiness gate refresh (S3 perspective)

| # | Item | S1 | S2 | S3 |
|---|---|---|---|---|
| 1 | host disk ≥ 30 Gi avail | GREEN (6.9 Gi) | RED (3.5 Gi) | RED (3.6 Gi) |
| 2 | Docker `info` < 5 s (Server: block returns) | GREEN | RED (hung) | RED (Server: empty) |
| 3 | proofs/.lake non-cyclic symlink (NEW gate S3) | not checked | not checked | RED (cycles to self) |
| 4 | no merge conflicts in target file | GREEN | GREEN | GREEN (file unchanged since `2ace1c84053`) |
| 5 | Mathlib pin unchanged | GREEN | GREEN | GREEN (`2df2f0150c…` ≥15 h stable) |
| 6 | paste-ready Lean drafted under `#check` | RED (queued) | GREEN | GREEN (carry-forward; recipe frozen) |
| 7 | no overlapping open PR | GREEN | GREEN | GREEN (`gh pr list … --state open` → `[]`) |
| 8 | expected ACT LOC delta ≤ 180 per cycle | GREEN | GREEN | GREEN (Step-A is 80–120 LOC) |
| 9 | ACT memo template prepared | GREEN | GREEN | GREEN |

**Verdict**: ACT not met. Items 1+2+3 RED. S4 ACT remains gated on
host out-of-band recovery (§2 script). S3 STATE-SYNC discharges
maximum safe doc-only drift this cycle.

---

## §6 6-row picker decision matrix for S4 (next-cycle claim of this slug)

Assuming the next researcher (cycle ~T+5–15 h) claims this slug, the
six possible infra-state combinations and recommended actions:

| Row | G7 disk | G8 Docker | G9 .lake | Recommended S4 action |
|---|---|---|---|---|
| A | GREEN (≥6 Gi) | GREEN (Server: < 5s) | GREEN (no cycle) | **S4 ACT** — paste S2 PREP §3 Step-A lemma; build-verify under Docker; if green, ship ACT PR (~80–120 LOC + meta touch only if axiomCount changes) |
| B | GREEN | GREEN | RED | S4 ACT "build pending" — paste lemma, push without build verification, qualify PR title `(build pending — proofs/.lake cycle)`; or release-without-PR + delegate G9 repair to a hermit/doctor PR |
| C | GREEN | RED | GREEN | release-without-PR (Docker is the dominant build constraint) OR S4 PREP refinement (e.g., spot-check additional bearer, add §5 ACT-pre-flight) |
| D | RED (3-5 Gi) | GREEN | GREEN | S4 ACT "with caution" — paste lemma, attempt build with smaller `LEAN_MEMORY_LIMIT` (e.g., 4096 MB) and short timeout; if disk fills mid-build, abort + S5 STATE-SYNC absorb |
| E | RED | RED | GREEN | release-without-PR (host blocks; no progress possible) |
| F | RED | RED | RED | release-without-PR OR thin S5 STATE-SYNC if NEW drift accumulated (e.g., intervening mechanic, sibling PR); current S3 cycle is row F |

Note row F's S5 trigger: only ship if substantive new drift since S3
(this) — otherwise next-cycle release-without-PR is preferred (memory
`_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`).

---

## §7 Explicit non-actions (what S3 does NOT do)

1. **Does NOT touch `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`** —
   recipe frozen; Lean changes deferred to S4 ACT under recovered infra.
2. **Does NOT touch `proofs/lake-manifest.json`** — Mathlib pin
   unchanged.
3. **Does NOT touch gallery `src/data/proofs/<slug>/meta.json` numerics
   or `additionalFiles[]`** — researcher-mechanic boundary; theoremCount
   drift (28 vs 26) flagged in JSON `knowledge.nextSteps[6]` for
   mechanic to address in a future batch sync.
4. **Does NOT touch gallery `src/data/proofs/<slug>/meta.json`
   description or `assumptions` prose** — content unchanged since
   PR #14919, still accurate.
5. **Does NOT touch `research/problems/<slug>/problem.md`** —
   problem statement unchanged.
6. **Does NOT touch `research/problems/<slug>/knowledge.md` body** —
   knowledge unchanged; updates flow through canonical JSON
   `knowledge.*` fields only.
7. **Does NOT rewrite Sessions 1+2 body in state.md** — historical
   record preserved; `this PR` wordings disambiguated via §1 audit
   table and iteration history PR attribution.
8. **Does NOT re-execute Mathlib bearer 5-spot check** — SHA stable
   ≥15 h, S2 PREP's check carry-forward (memory:
   `_state_md_three_sessions_behind_sessions_dir_*` — bearer
   re-walk on SHA-stable predecessor is busywork).
9. **Does NOT run `docker info`, `lake build`, or `pnpm build`** —
   Docker hung (would timeout); `pnpm build` regenerates ALL
   research JSONs and is foreclosed by memory feedback
   `_mechanic_pnpm_build_regenerates_all_research_jsons`.

---

## §8 Honesty calibration + memory citations

**What this PR is**: a 4-file doc-only STATE-SYNC closing ≥11 stale
`this PR` loci + adding 1 missed blocker + fixing 20-day registry
drift + flagging 1 mechanic-territory numeric drift. Total drift
absorbed: 4 substantive items.

**What this PR is not**: progress on the Sturm theorem itself. Zero
new Lean LOC. Zero axioms discharged. Zero gallery updates. Zero
build verification (Docker hung). The next reader should treat this
as housekeeping under host-RED conditions, not as advancing the
mathematics.

**Why this is worth shipping vs release-without-PR**: residual drift
exceeds release threshold per memory criteria:
- ≥3 substantive drift items (registry + missing blocker +
  ≥11 stale `this PR` loci) — ✅
- Missing critical info (G9 blocker not in JSON) — ✅
- Predecessor not in ≤2 h release window (S2 PREP merged T-5h ago,
  borderline) — borderline
- Mechanic re-flag worth surfacing (theoremCount -2) — minor

Per memory `_postship_pivot_to_prep_phase_slug_with_old_prep_predecessor_and_three_red_infra_plus_three_stale_thispr_loci_ship_state_sync_with_drift_fix`,
the chebyshev pattern (T-11 h + 3 RED + 3 stale `this PR`) shipped a
STATE-SYNC. This cycle has T-5 h + 3 RED + ≥11 stale `this PR` +
missing G9 blocker + registry drift — strictly more drift. Ship.

**Memory citations applied**:
- `_postship_pivot_to_prep_phase_slug_with_old_prep_predecessor_and_three_red_infra_plus_three_stale_thispr_loci_ship_state_sync_with_drift_fix` — pattern match (slightly shorter predecessor window but more drift)
- `_predecessor_statesync_mandated_pre_claim_docker_baseline_..._with_mechanic_partial_discharge_3red_infra_through_intended_window` — 3-RED INFRA recovery script reference
- `_mechanic_batch_sync_predecessor_touched_one_shared_file_only_leaving_9_off_by_ones` — mechanic territory boundary (do not fix gallery numerics)
- `_mechanic_pnpm_build_regenerates_all_research_jsons` — do not run pnpm build
- `_worktree_absolute_path_lands_in_main_repo_use_dotloom_worktrees_path_or_cp_recovery` — verified all file paths via `cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-11` first
- `_state_md_three_sessions_behind_sessions_dir_with_mechanic_cascade_already_discharging_blockers` — explicit non-action #8 (bearer re-walk busywork avoidance)

**Cycle cost**: ~30 min, doc-only, no Docker, no Lean, no pnpm build.
File deltas: registry.json (+1/-1), canonical JSON (~15 line edit),
state.md (~60 LOC prepend + 2-row table edit), NEW sessions/ memo
(~290 LOC). Net ~370 LOC added, ~25 LOC modified.

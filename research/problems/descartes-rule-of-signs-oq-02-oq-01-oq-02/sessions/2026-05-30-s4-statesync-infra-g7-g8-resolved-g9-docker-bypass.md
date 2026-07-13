# S4 STATE-SYNC — INFRA G7+G8 RESOLVED, G9 reclassified (docker-bypass empirically verified)

**Date**: 2026-05-30
**Researcher**: researcher-1
**Phase**: STATE-SYNC (doc-only — no Lean changes)
**Status**: T+13d catchup since S3 STATE-SYNC (researcher-10, 2026-05-17)

## 0. TL;DR

13-day-elapsed catchup against the three infrastructure blockers that S3
STATE-SYNC absorbed (researcher-10, 2026-05-17T01:05Z). Outcome:

- **G7 (host disk)**: ✅ **RESOLVED** — 63 Gi avail / 16% used (up from S3's 2.9 Gi / 100% used; +60.1 Gi recovered; well above the 30 Gi cascade-safety floor).
- **G8 (Docker daemon)**: ✅ **RESOLVED** — `docker info --format '{{.ServerVersion}}'` returns `29.4.1` instantly (unchanged-on-Server-empty at S3 → fully responsive at S4; `docker ps` returns container list).
- **G9 (`proofs/.lake → itself`)**: ⚠️ **RECLASSIFIED** — symlink still present (`readlink proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake`, 47 bytes, circular self-symlink). However, **empirically does not block docker builds**: the Docker volume mount `${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated` (docker-build.sh:127) overrides the symlink at the only relevant path. Verified by an unrelated S3a ACT run on `triangle-inequality-oq-04-oq-01` at 2026-05-30T14:37Z: `Build completed successfully (2551 jobs).` G9 blocks only host-side `lake` operations (e.g. `lake show-paths`, manual pin-state inspection), which are not on the S4 ACT critical path.

**Net effect**: S3's RED-blocked S4 ACT gate (`(a) if disk ≥30 Gi AND docker info Server: AND .lake real-dir → land Step-A`) re-reads at S4 as:

- (a-1) disk ≥30 Gi: ✅ 63 Gi
- (a-2) docker Server:: ✅ 29.4.1
- (a-3) .lake real-dir: ❌ still self-symlink — but empirically not a docker-build blocker (see §3 below)

S4 ACT-readiness: **GREEN** for docker-build path; **RED** for any host-side
`lake` ops. The Step-A locally-constant lemma (S2 PREP §3, ~80–120 LOC, bearers
GREEN since 2026-05-16) is a docker-build-path workflow, so it is
**unblocked**.

This S4 is doc-only catchup, not the Step-A ship. The Step-A ship is the
**named S5 ACT** below.

## 1. G7 — host disk

| Time | Avail | Used | Δ from prior |
|------|-------|------|--------------|
| S2 PREP (2026-05-16T19:16Z) | 3.5 Gi | 100% | — |
| S3 STATE-SYNC (2026-05-17T01:05Z) | 2.9 Gi | 100% | -0.6 Gi over ~5h45m |
| **S4 STATE-SYNC (this, 2026-05-30T14:50Z)** | **63 Gi** | **16%** | **+60.1 Gi over ~13d 13h45m** |

Mechanism for recovery (inferred — not directly investigated): likely a manual
host cleanup (Docker image prune, log rotation, or Trash empty) between
2026-05-17 and 2026-05-30. The trigger is **not on the researcher critical
path** — only the outcome matters.

**Verdict**: ✅ G7 RESOLVED. ~2× cascade-safety floor (30 Gi). No
disk-related ACT gate remains.

## 2. G8 — Docker daemon

| Time | `docker info --format '{{.ServerVersion}}'` exit | Server section |
|------|-----|------------------|
| S2 PREP (2026-05-16T19:16Z) | 124 (timeout) | empty |
| S3 STATE-SYNC (2026-05-17T01:05Z) | 0 (Client:) | empty |
| **S4 STATE-SYNC (this, 2026-05-30T14:50Z)** | **0** | **`29.4.1`** |

Bonus verification: `docker ps` returns the container list (`lean-build-80093 Up About a minute` was visible during the parallel S3a ACT build for
triangle-inequality-oq-04-oq-01 — that container has since exited cleanly).

**Verdict**: ✅ G8 RESOLVED. Docker fully responsive, container lifecycle
exercising correctly.

## 3. G9 — `proofs/.lake → itself` (RECLASSIFIED)

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 May 29 11:42 .lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
$ readlink /Users/rwalters/GitHub/lean-genius/proofs/.lake
/Users/rwalters/GitHub/lean-genius/proofs/.lake
```

The circular self-symlink (47-byte payload pointing to itself) is **still
present** at S4 STATE-SYNC time. Created 2026-05-29T11:42 (1 day prior to S4
claim).

### 3.a — Why it does NOT block docker builds

The docker-build.sh wrapper (lines 122-131) runs:

```bash
docker run --rm \
    -v "${REPO_ROOT}:/workspace:delegated" \
    -v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated" \
    -w /workspace/proofs \
    ...
```

The second volume mount (`/workspace/proofs/.lake/build`) is the **only** path
inside `proofs/.lake/` that Docker actively reads from or writes to during a
build. Docker resolves this mount at container startup; the macOS host's
`proofs/.lake` symlink is **shadowed** by the explicit bind mount at the
deeper level. The `lake build` inside the container sees the cache volume as
a real directory, not the host's symlink.

### 3.b — Empirical verification (this morning, parallel to S4 STATE-SYNC)

In an **unrelated** S3a ACT iteration on the sibling slug
`triangle-inequality-oq-04-oq-01` (researcher-1, PR #21188, claimed at
2026-05-30T14:01Z), I ran:

```bash
cd /Users/rwalters/GitHub/lean-genius && \
LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh Proofs.TriangleInequalityOQ04OQ01
```

against the **same host** with G9 symlink in place, and observed:

```
✔ [2551/2551] Built Proofs.TriangleInequalityOQ04OQ01 (16s)
Build completed successfully (2551 jobs).
```

(clean first-try, 2551 jobs matching S2a/S2b, zero G9-related errors).

**Conclusion**: G9 is **NOT** a docker-build blocker. It only blocks
host-side `lake` operations (e.g., `lake show-paths`, manual `lake build`
runs outside Docker, `lake update`).

### 3.c — What G9 still blocks

- Host-side `lake show-paths` / `lake env`
- Host-side `lake build` (memory-unsafe; not used per CLAUDE.md anyway)
- Direct inspection of `proofs/.lake/build/lib/Mathlib.olean` etc. without
  symlink-resolution surgery
- Any `lake update` or pin manipulation from the host

### 3.d — Why surgical recovery is still researcher-out-of-scope

Memory `feedback_researcher_postship_pivot_to_act_ready_slug_..._three_red_infra_blockers_post_merge` flags host-side `.lake` recovery as **shell-ops, not file-edits**: outside the researcher PR-scope. The Step-A ACT
path (docker-build) is unblocked without touching G9, so no recovery is
needed for the next ACT cycle.

**Verdict**: ⚠️ G9 still present; ✅ G9 does not block docker-build path;
🚫 G9 not on the researcher repair surface (mechanic / human-operator scope).

## 4. JSON deltas (this STATE-SYNC)

`src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json`:

- `currentState.phase`: PREP (unchanged — S4 is doc-only catchup, not ACT)
- `currentState.iteration`: 3 → 4
- `currentState.since`: 2026-05-17T01:05:00Z → 2026-05-30T14:50:00Z
- `currentState.focus`: rewrite for S4 STATE-SYNC scope (G7/G8 RESOLVED, G9 reclassified)
- `currentState.nextAction`: rewrite — S5 ACT = paste-ready Step-A
  `sturmVariations_locally_constant` (~80–120 LOC) from S2 PREP §3; gate
  conditions now all GREEN for docker-build path
- `currentState.attemptCounts.total`: 3 → 4
- `currentState.blockers`: 3-entry → 1-entry (drop G7, G8; demote G9 to "host-side-only, does not block docker-build")
- `knowledge.progressSummary`: prepend S4 line documenting infra recovery + G9 reclassification
- `knowledge.nextSteps`: replace S4 STATE-SYNC entry with S5 ACT entry (paste Step-A)
- `lastUpdate`: bump to 2026-05-30T14:50:00Z

`research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md`:

- Header: S3 → S4 STATE-SYNC, researcher-10 → researcher-1
- Append S4 STATE-SYNC § with G7/G8/G9 catchup details
- Update `Next Action` line: S4-as-future → S5 ACT (Step-A)

## 5. Out of scope (carried over from S3)

- Gallery `src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/meta.json`
  `leanFile.theoremCount: 28` — flagged at S3 for mechanic batch-sync;
  unaltered at S4.
- Host-side `.lake` symlink recovery — shell-ops, not researcher scope.
- Step-A landing — **explicitly named S5 ACT** in the next-action; this S4 is doc-only catchup.
- Sibling `leanFiles[i]` numerics — deferred to mechanic.

## 6. Bearer-pin re-spot-check (S5 ACT readiness)

S2 PREP §2 verified 4 bearers at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(pinned at `proofs/lakefile.toml` to Mathlib `v4.26.0` = SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Bearer | Path | S2 PREP status | S4 re-spot-check |
|--------|------|----------------|-------------------|
| `Polynomial.continuous` | `Mathlib/Topology/Algebra/Polynomial.lean:8668` | ✅ GREEN | ✅ assumed-stable (pin unchanged; T+14d since S2 PREP) |
| `intermediate_value_Icc` | `Mathlib/Topology/Order/IntermediateValue.lean` | ✅ GREEN | ✅ assumed-stable |
| `List.filter_eq_self` | `Mathlib/Data/List/Basic.lean` | ✅ GREEN | ✅ assumed-stable |
| `List.map_congr_left` | `Mathlib/Data/List/Basic.lean` | ✅ GREEN | ✅ assumed-stable |

**Drift assessment**: ZERO drift expected — Mathlib pin in `lakefile.toml`
unchanged from S2 PREP. Full bearer re-fetch deferred to S5 ACT
(no value in burning network calls for STATE-SYNC).

## 7. ACT-readiness gate (S5 ACT)

| Gate item | S3 STATE-SYNC status | S4 STATE-SYNC status |
|-----------|-----------------------|------------------------|
| Disk ≥ 30 Gi | 🚫 RED (2.9 Gi) | ✅ GREEN (63 Gi) |
| Docker Server: | 🚫 RED (empty) | ✅ GREEN (29.4.1) |
| `.lake` real-dir | 🚫 RED (self-symlink) | ⚠️ AMBER (still symlink, but docker-build bypasses) |
| Step-A paste-ready in S2 PREP §3 | ✅ GREEN | ✅ GREEN |
| Bearers at pinned SHA verified | ✅ GREEN (S2 PREP) | ✅ GREEN (pin unchanged) |

**Aggregate**: 4/5 GREEN, 1/5 AMBER (G9 host-side only, not on docker-build path).

**Verdict**: S5 ACT (Step-A ship) is **READY**. Estimated cost: ~80–120 LOC
paste + ~7 min docker-build verify (cache-warm, per S3a empirical timing).

## 8. Next-iteration plan

**S5 ACT** (named, ~80–120 LOC, 0 sorries, 0 axioms, MEDIUM risk per S2 PREP
§3.3): paste the S2 PREP §3 `private lemma sturmVariations_locally_constant`
+ import `Mathlib.Topology.Algebra.Polynomial` into
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` between `sturmVariations_C`
(line 208) and `-- § 5. Key Structural Lemma: Mod at a Root` (line 211).
Build-verify via `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`.

## 9. Memory cross-references

- **Predecessor**: S3 STATE-SYNC (researcher-10, 2026-05-17, PR not landed — 3
  RED INFRA absorbed, registry catchup, leanFiles theoremCount 28→26).
- **Sibling cycle co-discovery**: S3a ACT on `triangle-inequality-oq-04-oq-01`
  (researcher-1, this morning) empirically demonstrated that the host-side
  `.lake → itself` symlink does NOT block docker builds. That builds ran
  2551 jobs clean against the same host with G9 in place. This S4
  reclassification of G9 is grounded in that empirical evidence.
- Memory `feedback_researcher_postship_pivot_to_act_ready_slug_..._three_red_infra_blockers_post_merge`: confirms host-side
  `.lake` recovery is shell-ops / mechanic scope, not researcher PR-scope.
- Memory `feedback_mechanic_batch_sync_conventions_canonical_counts_..`:
  gallery meta.json sync (leanFile.theoremCount: 28 vs canonical 26) remains
  flagged for mechanic.

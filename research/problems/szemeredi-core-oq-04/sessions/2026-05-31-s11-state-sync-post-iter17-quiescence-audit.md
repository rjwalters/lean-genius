# S11 STATE-SYNC — post-Iter-17 14-day quiescence audit

**Date**: 2026-05-31 (UTC; local 2026-05-30)
**Researcher**: researcher-1
**Mode**: Doc-only STATE-SYNC (zero `*.lean` / `problem.md` / `knowledge.md` /
`lake-manifest` / `lakefile` edits; sessions/ + state.md + slug JSON only).
**Iteration**: 18 (merge-order monotone successor to Iter 17 PR #19619).
**Baseline**: Iter 17 STATE-SYNC + PREP (PR #19619, researcher-10, merged
2026-05-16T14:33:03Z UTC).
**Goal**: confirm 14-day quiescence on slug bearer files, re-verify
ACT-readiness gates, clear Iter 17 §9 infra block (G8 Docker daemon hung)
if resolved, refresh JSON to iter 18.

---

## §1. Window summary

* **Iter 17 merge**: 2026-05-16T14:33:03Z (`b52e24a1948`, PR #19619, S10 PREP
  by researcher-10).
* **This SYNC author-time**: 2026-05-31T06:20Z (≈ 14 days 16 h after Iter 17
  merge).
* **Origin/main tip**: `7777cb1d3fe` (`fix(meta): erdos-1048 register
  Erdos1048Aristotle.lean companion (#21295)`, 2026-05-30 21:14:28 -0700 ≈
  2026-05-31T04:14Z).
* **Repo churn in window**: **1421 commits** on origin/main between
  Iter 17 merge and this audit's author-time (`git log origin/main
  --since="2026-05-16T15:00:00Z" --oneline | wc -l`).

---

## §2. Slug quiescence audit (the load-bearing finding)

**Query**: `git log origin/main --since="2026-05-16T15:00:00Z" --oneline --`
across all slug paths:

| Path | Commits in window |
|---|---|
| `proofs/Proofs/SzemerediCoreOQ04.lean` | **0** |
| `proofs/Proofs/SzemerediCore.lean` | **0** |
| `proofs/Proofs/SzemerediRegularity.lean` | **0** |
| `proofs/lake-manifest.json` | **0** |
| `research/problems/szemeredi-core-oq-04/` | **0** |
| `src/data/research/problems/szemeredi-core-oq-04.json` | **0** |

**Interpretation**. Among 1421 commits to origin/main in the 14-day window,
**zero** touched any slug bearer or slug-owned doc/JSON. The slug is
strictly quiescent post-Iter-17, both at the Lean-source layer and at the
research-doc layer.

---

## §3. Lake-manifest byte-stability

The most-recent commit to `proofs/lake-manifest.json` on origin/main is
**still** `ecb47b35601` (Sperner PR #19454, 2026-05-16T08:55:07Z UTC) — the
same commit recorded by Iter 17 §3. That commit predates Iter 17's merge,
so the lake-manifest has not moved at all in the 14-day window.

Recorded SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib `v4.26.0`).
File SHA1 of `proofs/lake-manifest.json` at this audit: `272effadcde902c98bd16e2d88c457d02d99a5a6`.

**Transitivity**: since the Mathlib `rev` pin in lake-manifest is byte-stable
*and* lake-manifest itself is byte-stable, every Mathlib bearer file SHA
pinned by Iter 14 / Iter 15 / Iter 17 is byte-stable by construction. No
per-file SHA recheck is needed; Iter 17's §3 / §4 conclusions (10/10
Mathlib SHAs byte-stable, 5/5 Iter 15 line-cites corrected) all carry
forward verbatim.

---

## §4. Slug Lean file byte-stability

`proofs/Proofs/SzemerediCoreOQ04.lean`:

* **Line count**: 1054 (matches Iter 13 / 14 / 15 / 16 / 17 records).
* **SHA1 at this audit**: `a51ac94f3e2aaa9ccea77c2f2496719a75b6fa83`.
* **Most recent main-touch**: `ecb47b35601` (Sperner PR #19454,
  2026-05-16T08:55:07Z). Confirms zero post-Iter-17 main-touch.

Sorry inventory unchanged: 2 (line 291 archival-unprovable + line 831
deferred-provable). 0 axioms. 0 assumption-encoding structure fields.

---

## §5. ACT-readiness gate refresh (8 gates)

Iter 17 closed with **7/8 GREEN substantive + 1/8 RED INFRA** (G8 = Docker
daemon hung). Audit at 2026-05-31T06:20Z:

| Gate | Iter 17 | Iter 18 | Notes |
|---|---|---|---|
| G1 lake SHA byte-stable | ✅ | ✅ | `2df2f015…` unchanged 14 d |
| G2 bearer file SHAs byte-stable | ✅ | ✅ | transitive on G1 |
| G3 bearer line cites | ✅ (post-§4 correction) | ✅ | unchanged on byte-stable files |
| G4 prerequisites built | ✅ | ✅ | last green build = Iter 13 PR #19042 Docker 7744 jobs |
| G5 symmetric projections in scope | ✅ | ✅ | Iter 10/11 deliverable, unmoved |
| G6 sorry inventory matches | ✅ | ✅ | 2 sorries, line 291 + line 831 |
| G7 no overlapping open PRs | ✅ | ✅ | `gh pr list --search "szemeredi-core-oq-04 in:title" --state open` returns empty (pre-this-PR) |
| G8 build infrastructure | ❌ (B2 Docker hung) | ✅ | **CLEARED** — see §6 |

**Net change**: 7/8 → 8/8. The Iter 17 §9 infra blocker is fully released;
the slug is *ACT-ready* for the next iteration's paste of Part 9
first-moment skeleton (Iter 17 §6 paste-ready content, ~55 LOC declarations
+ ~45 LOC structural comments, 4 new sorries transiently).

---

## §6. Infrastructure note — Docker daemon recovered

Iter 17 §9 recorded **B2**: `docker info` returning blank `ServerVersion`
and `OperatingSystem` past a 12 s timeout, with `docker ps` returning
empty instantly. At this audit's pre-flight (2026-05-31T06:20Z):

* `timeout 30 docker info` returns within ~3 s with full `Server:` block.
* `Server Version: 29.4.1` (client and server agree, single host).
* `Storage Driver: overlayfs` (`io.containerd.snapshotter.v1`).
* `Kernel Version: 6.12.76-linuxkit` (Docker Desktop VM).
* `Containers: 0`, `Images: 3` — clean slate.

Disk pre-flight: `df -h /System/Volumes/Data` reports `926Gi 839Gi 57Gi
94%` — 57 GiB free, well above Iter 16's recommended ≥10 GiB threshold
(noting overall capacity remains tight at 94 %, so the next ACT cycle
should re-check ≥10 GiB free before committing to a Docker build).

**Combined pre-flight recipe** (preserved from Iter 17, all now passing):

```bash
df -h /System/Volumes/Data | awk 'NR==2 {print $4}'   # expect ≥10G
timeout 10 docker info 2>&1 | grep "^ Server Version:"  # expect non-blank
```

---

## §7. JSON catchup

Slug JSON at `src/data/research/problems/szemeredi-core-oq-04.json`:

* `currentState.iteration`: 17 → 18.
* `currentState.since`: `2026-05-16T10:30:00.000Z` → `2026-05-31T06:20:00.000Z`.
* `currentState.phase`: `ACT-ready` (unchanged; Iter 17 already set this).
* `currentState.focus`: rewritten 2-paragraph form absorbing this SYNC's
  G8-clear finding and 14-day quiescence; preserves the Iter 17 menu of
  Part 9 first-moment route (preferred) vs Part 9' second-moment route
  (tight alt).
* `currentState.nextAction`: trimmed and re-prioritised — first bullet now
  reads "Iter 19 ACT-α paste Part 9 first-moment skeleton (Iter 17 PREP
  §6 paste-ready content, ~55 LOC declarations + ~45 LOC structural
  comments, 4 new sorries transiently) under a clean Docker pre-flight";
  bullets 2-N preserve Iter 17's menu order.
* `currentState.attemptCounts`: unchanged (`total: 6`, `currentApproach: 5`,
  `approachesTried: 2`). No new approach attempted in this SYNC.
* Top-level `lastUpdate`: `2026-05-16` → `2026-05-31`.

No edits to `knowledge.*`, `knownResults`, `references`, `tier`, `tags`,
or `status` fields.

---

## §8. Race / saturation check (PR creation time)

* `gh pr list --search "szemeredi-core-oq-04 in:title" --state open`:
  empty (this STATE-SYNC will be the sole open slug PR upon creation).
* Active claims on slug: 1 (this session's, `researcher-22732`, expires
  2026-05-31T07:35:37Z UTC per `claim-problem.sh status`).
* Stale claims on slug: 0 (Iter 17's "abel-ruffini" listing in status is
  for an unrelated slug).
* Most recent slug merge: Iter 17 PR #19619 at 2026-05-16T14:33:03Z UTC
  (~ 14 d 16 h before this SYNC's author-time).
* File overlap with open PRs: not surveyed in detail (this SYNC modifies
  only `state.md` + `sessions/` + slug JSON — zero overlap is conjectured
  on the basis that no slug-overlapping PR has been opened in 14 days).

---

## §9. Stranded branches (carry-forward)

Iter 17 §10 listed two reaffirmed orphans:

* `research/szemeredi-energy-weighted` `4b16c813dc58…`
* `research/szemeredi-furstenberg-prokhorov-spec` `5ef69e8d8a62…`

Both off-slug; out of scope for this SYNC. No new orphan branches detected
in a quick `git branch -r | grep szemeredi` scan beyond these two.

---

## §10. Iteration-numbering note

This Iter 18 entry continues the **merge-order monotone** convention from
Iter 9 / 14 / 16 / 17 re-numbering precedent: PRs are entered in
merge-time order, and a STATE-SYNC takes the next integer after the most
recently merged slug PR. Iter 18 succeeds Iter 17 with no skipped numbers
(Iter 17 was the most-recent narrative head on `state.md` per PR #19619).

---

## §11. Files modified (Iter 18)

* `research/problems/szemeredi-core-oq-04/sessions/2026-05-31-s11-state-sync-post-iter17-quiescence-audit.md`
  (this SYNC, ~190 LOC).
* `research/problems/szemeredi-core-oq-04/state.md` (head block + new
  Iter 18 entry inserted before Iter 17 entry; no deletions, no narrative
  edits to Iter 17 or earlier entries).
* `src/data/research/problems/szemeredi-core-oq-04.json`
  (`currentState.{iteration, since, focus, nextAction}` + top-level
  `lastUpdate`; no other field edits).

**Build status (Iter 18)**: N/A — doc-only (zero `*.lean` edits;
G4 prerequisites unchanged from Iter 13 PR #19042 Docker 7744-job clean
build).

---

## §12. Honest scope

This SYNC contributes one observation and one infra-clear:

1. **Observation (load-bearing)**: 14 days of repo churn (1421 commits)
   produced zero touches on any slug bearer. The Iter 17 ACT-readiness
   state is intact.
2. **Infra clear**: Docker daemon recovered (G8 RED → GREEN), unblocking
   the next ACT cycle's paste of Part 9.

No mathematical advance, no new bearer pins, no new approach attempts.
The next iteration (Iter 19 ACT-α) is the load-bearing one — pasting
the Iter 17 §6 paste-ready Part 9 skeleton and running a Docker build
to verify.

# Research State: erdos-1006-oq-01-oq-02

## Current State
**Phase**: STATE-SYNC (S3 STATE-SYNC — INFRA gates recovered RED→GREEN over T+23d; S2 picker-matrix top row now operationally valid, but S2 skeleton is not paste-ready (has `sorry` + `...` placeholders), so S4 PREP is the next required step)
**Path**: full
**Since**: 2026-06-09T23:58:00Z
**Iteration**: 4 (state.md was at 2 after S2; JSON silently bumped to 3 in a 2026-05-18 metadata sync without a sessions/ memo; this S3 STATE-SYNC bumps both to 4 to align)
**Last Updated**: 2026-06-09T23:58:00Z

## Current Focus (S3 STATE-SYNC, 2026-06-09, researcher-1)

S3 STATE-SYNC (researcher-1, 2026-06-09, this PR — doc-only INFRA recovery
documentation + picker-matrix amendment): T+23d after S2 OBSERVE, all three
INFRA gates have recovered from RED to GREEN:

| Gate | S2 status (2026-05-17) | S3 status (2026-06-09) | Δ |
|------|------------------------|------------------------|---|
| G7 host disk available | RED (3.3 Gi, deteriorating) | **GREEN** (99 GiB free) | +95.7 Gi |
| G8 `docker info` Server: | RED (empty) | **GREEN** (populated; Server Version 29.5.3, overlayfs storage) | recovered |
| G9 `proofs/.lake` symlink | RED (self-cycle reported) | **GREEN** (real directory) | recovered |

Per the S2 picker matrix, the top row should now fire (full S3 ACT chains
sub-case). However, the S2 skeleton at §4 is **NOT paste-ready** despite
the framing — `recognizeChainCover` body contains `...` placeholder and
`chain_cover_recognition_decidable` body is a single `sorry`. S3
STATE-SYNC amends the picker matrix to require **both** INFRA GREEN AND
skeleton paste-readiness (0 `sorry`, 0 `...`) as joint preconditions for
ACT.

Updated picker matrix (post-S3):

| G7 | G8 | G9 | SHA | Skeleton state | S4 action |
|----|----|----|-----|----------------|-----------|
| ≥5 Gi | populated | real dir | unchanged | **paste-ready** | S4 ACT chains sub-case |
| ≥5 Gi | populated | real dir | unchanged | sketch (current) | **S4 PREP refine skeleton** ← current |
| ≥5 Gi | populated | real dir | bumped | any | S4 ACT after bearer re-walk |
| ≥5 Gi | empty | real dir | unchanged | any | S4 PREP refine — wait for Docker |
| ≥5 Gi | populated | self-cycle | unchanged | any | S4 INFRA recovery |
| <5 Gi | any | any | any | any | S4 STATE-SYNC only |
| any | any | any | unknown | any | S4 OBSERVE — re-verify pin |

**Current state hits row 2: S4 PREP refine skeleton.**

**Mathlib pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
unchanged since S1 OBSERVE (T+24d SHA-stable).

**File status re-verified at S3 STATE-SYNC start (`wc -l` + `grep -cE`)**:

| Path | LOC | thm | axiom | def | sorry |
|---|---|---|---|---|---|
| `proofs/Proofs/Erdos1006OQ01OQ02.lean` | 256 | 9 | 2 | 4 | 0 |

Byte-for-byte identical to S2 OBSERVE state. Full INFRA recovery and
picker-matrix amendment detailed in
`sessions/2026-06-09-s3-statesync-infra-green-recovery.md`.

---

## Prior Focus (S2 OBSERVE, 2026-05-17, researcher-5) — preserved for traceability

S2 OBSERVE (researcher-5, 2026-05-17, this PR — doc-only sub-class
PREP memo + stale-PR-citation fix + INFRA snapshot refresh):
predecessor S1 OBSERVE PR **#19887** (researcher-3, merged
2026-05-16T~22:30Z) bootstrapped state.md + problem.md + sessions/
+ 8 missing JSON top-level fields + 3 categories of drift fix
(leanFiles[1].lineCount 257→256, knowledge.progressSummary
261/10→256/9, knowledge.builtItems[6/7/8] line refs 213/224/256 →
208/219/251). S2 OBSERVE does NOT touch the Lean file (host Docker
daemon empty, host disk worsened **4.3 Gi → 3.3 Gi** over ~2.5h)
and instead:

1. **Identifies the trivial sub-case** for partial-class
   formalization: **chains (linear orders) → cover graphs are
   precisely paths** (Hasse diagram of a finite chain is the
   path graph). Cover-graph recognition restricted to graphs of
   maximum degree ≤ 2 reduces to path recognition, which is
   trivially in P. This carves off a concrete sub-result from
   the open `cover_graph_recognition_in_p` axiom: a future S3
   ACT can replace a restricted instance of the axiom (over the
   chain-shaped sub-class) by a fully-machine-checked theorem.
2. **Sketches a paste-ready Lean skeleton** for the chains
   sub-case: a definition `isCoverGraphOfChain`, a constructive
   recognition function `recognizeChainCover :
   SimpleGraph V → Bool`, and a theorem
   `chain_cover_recognition_decidable` showing
   `recognizeChainCover G = true ↔ ∃ (_ : LinearOrder V),
   isCoverGraphOf G`. The Mathlib bearer surface is small
   (`SimpleGraph.IsPath`, `Finset.image_of_card_le`,
   `SimpleGraph.degree`); see `sessions/2026-05-17-s2-observe-
   chains-subcase-skeleton.md` §3 for full bearer table.
3. **Fixes 5 stale `(this PR)` citations** that were correct at
   S1 OBSERVE PR-write time but became citationally stale once
   PR #19887 merged: 2 in JSON (knowledge.progressSummary line 10,
   currentState.focus line 139) + 3 in state.md (current-focus
   header line 12, iteration-history row, reference-files line).
   These are not factual errors — the work S1 documents IS the
   work of PR #19887 — but the literal "this PR" wording grows
   confusing once a successor session exists, so S2 updates them
   inline to `PR #19887`.
4. **Refreshes the INFRA snapshot** to record the disk delta
   over the past ~2.5h (G7 4.3 Gi → 3.3 Gi, still RED, same-day
   soft floor ≤5 Gi; G8 Docker info `Server:` section still
   empty; G9 `proofs/.lake → itself` self-symlink unchanged).
   None of the three RED gates block this doc-only S2; all three
   continue to block any future S3 ACT.

**File status re-verified at S2 OBSERVE start (`wc -l` + `grep -cE`
host-side, byte-for-byte identical to S1)**:

| Path | LOC | thm | axiom | def | sorry |
|---|---|---|---|---|---|
| `proofs/Proofs/Erdos1006OQ01OQ02.lean` | 256 | 9 | 2 | 4 | 0 |

**Mathlib pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(worktree `proofs/lake-manifest.json` at S2 OBSERVE start; **unchanged
since S1 OBSERVE**, ≥50h stable; same pin as in-flight schauder-fp /
abel-ruffini / shannon / ballot / lagrange / chebyshev slugs).

**INFRA snapshot (S2 OBSERVE start, 2026-05-17T~00:50Z)**:

| Gate | Status | S1 (~22:05Z) | S2 (~00:50Z) | Δ |
|------|--------|--------------|--------------|---|
| G7 host disk available | RED | 4.3 Gi | **3.3 Gi** | **−1.0 Gi** over ~2.5h |
| G8 `docker info` Server: | RED | empty | empty | unchanged (continuous ≥9.5h) |
| G9 `proofs/.lake` symlink | RED | → itself | → itself | unchanged |

S2 OBSERVE is doc-only and therefore unblocked. A future S3 ACT
(building the chains sub-case in `Erdos1006OQ01OQ02.lean`) is gated
on G7 ≥ 5 Gi AND G8 Server populated AND G9 .lake healthy (rmtree
+ re-`lake new` after `lake clean`).

---

## Prior Focus (S1 OBSERVE, 2026-05-16, researcher-3) — preserved for traceability

S1 OBSERVE (researcher-3, 2026-05-16, PR #19887 — doc-only bootstrap +
drift fix): The slug previously lacked state.md, problem.md, and a
sessions/ directory entirely. The canonical research JSON was missing
top-level `slug`, `title`, `phase`, `status`, `currentState`, `started`,
`tags`, and `lastUpdate` fields. This S1 OBSERVE creates the missing
infrastructure (NEW state.md + problem.md + sessions/ + 8 missing
top-level JSON fields) and fixes drift in the existing JSON `knowledge`
and `leanFiles[]` subsets:

1. **`leanFiles[1].lineCount`** 257 → **256** (matches host
   `wc -l proofs/Proofs/Erdos1006OQ01OQ02.lean`).
2. **`knowledge.progressSummary`** said "10 theorems (was 7) ... 261
   lines"; both numbers are pre-#15112 stale. Refreshed to "9 theorems
   ... 256 lines".
3. **`knowledge.builtItems[6/7/8]`** line refs `213/224/256` →
   **`208/219/251`** (shifted by 5 lines after #15112 removed the
   `True` stub).
4. **`knowledge.nextSteps[0]`** "Run docker build to verify Lean file
   compiles with 0 sorries" — preserved, but a clarifying note added
   that the parent gallery slug `erdos-1006` is the build-bearing entry.

**File status verified at session start (`wc -l` + `grep -cE` host-side)**:

| Path | LOC | thm | axiom | def | sorry |
|---|---|---|---|---|---|
| `proofs/Proofs/Erdos1006OQ01OQ02.lean` | 256 | 9 | 2 | 4 | 0 |

The 2 axioms are intentional:
- `comparability_recognition_in_p` (line 159) — Golumbic-classical
  "comparability graph recognition is in P", stated as axiom for
  compactness.
- `cover_graph_recognition_in_p` (line 176) — **the open question**
  itself, stated as axiom so the file type-checks while the
  mathematical question remains open. **Not a defect**; this is the
  load-bearing problem statement.

**Mathlib pin SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (worktree
`proofs/lake-manifest.json` at session start; same pin as in-flight
schauder-fp / abel-ruffini / shannon / ballot / lagrange / cebyshev
slugs across the 2026-05-15→05-16 wave; ≥48h stable).

**Build status**: not directly attempted in this S1 OBSERVE (the slug
is doc-only-bootstrap scope; host Docker daemon hung as of S22 schauder
session ~30 min ago — `docker info` Server: section empty; same as
≥7 same-wave precedent PRs). The parent gallery slug `erdos-1006`
is the build-bearing entry; this -oq-01-oq-02 slug's file is an
auxiliary research support file with all 9 theorems already at 0
sorries.

## Active Approach (post-S2 OBSERVE)

**Sub-class formalization: chains → paths.** The slug's mathematical
question (cover graph recognition in P for *arbitrary* finite graphs)
remains **genuinely open**. However, the open `cover_graph_recognition_in_p`
axiom can be carved up by sub-class: for the chain (linear-order) sub-class,
cover-graph recognition is **trivially in P**, because the cover graph of
a finite chain is precisely the corresponding path graph (a graph with
n vertices, n−1 edges, all internal-vertex degrees = 2, endpoint degrees = 1).
S2 OBSERVE sketches a paste-ready Lean skeleton for this sub-case; the full
construction is deferred to S3 ACT under recovered Docker. See
`sessions/2026-05-17-s2-observe-chains-subcase-skeleton.md` for the
4-definition + 1-theorem skeleton with Mathlib bearer table.

## Attempt Count

- Total attempts: 2 (S1 OBSERVE bootstrap; S2 OBSERVE sub-class PREP memo)
- Current approach attempts: 1 (S2 OBSERVE introduces the chains sub-case)
- Approaches tried: 2 (bootstrap + drift fix; sub-class PREP memo)

## Blockers

None for this S2 OBSERVE (doc-only PREP memo). Forward research splits
into two layers:

- **Mathematical**: the full open question
  `cover_graph_recognition_in_p` remains genuinely open (no
  literature breakthrough since the 2026-05-03 last direct Lean
  edit).
- **INFRA (blocks S3 ACT only)**: 3 RED gates as of S2 OBSERVE start
  — G7 host disk 3.3 Gi (below 5 Gi soft floor), G8 `docker info`
  `Server:` empty (≥9.5h continuous), G9 `proofs/.lake → itself`
  self-symlink. All three must clear before the chains-sub-case S3
  ACT can ship a buildable Lean change.

## Next Action

S3 ACT: implement the chains-sub-case skeleton from
`sessions/2026-05-17-s2-observe-chains-subcase-skeleton.md` §4 in
`proofs/Proofs/Erdos1006OQ01OQ02.lean` (append ~30 LOC: one definition
`isCoverGraphOfChain`, one recognition function
`recognizeChainCover`, one theorem `chain_cover_recognition_decidable`).
Gates for S3 ACT: G7 disk ≥ 5 Gi AND G8 Docker `Server:` populated AND
G9 `proofs/.lake` resolvable (rmtree + `lake new` after `lake clean`).
Estimated build cost: small (the new definitions reuse the existing
`isCoverGraphOf` machinery from `Erdos1006OQ01.lean`).

Fallback if INFRA stays RED: another doc-only S2-style refinement
identifying a second sub-class (interval orders, planar cover graphs,
or bounded-treewidth posets) is acceptable. The slug carries no hard
time-bound; release is also acceptable.

## Open PRs

None for this slug at S2 OBSERVE session start.

- Last direct Lean-file edit: #15097 (2026-05-03) "research:
  add K₃ strict separation"; followed by #15112 (2026-05-03) "fix:
  correct theoremCount 10→9, remove True stub".
- Most recent slug-level documentation touch: **#19887** (2026-05-16
  T-2.5h, researcher-3) "S1 OBSERVE — bootstrap state.md +
  problem.md + sessions/ + 8 missing JSON top-level fields + drift
  fix (doc-only)".
- Most recent JSON-related batch touch: #19841 (2026-05-16, mechanic
  batch sync of `Erdos1006OQ04.lean` leanFiles across 19 siblings;
  did NOT touch `Erdos1006OQ01OQ02.lean` entry; that entry's LOC 257
  drift was fixed by S1 OBSERVE #19887).

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|----|--------|
| S1 OBSERVE | 2026-05-16 | researcher-3 | #19887 | Bootstrap state.md + problem.md + sessions/ + JSON top-level fields (slug/title/phase/status/currentState/started/tags/lastUpdate); fix leanFiles[1].lineCount 257→256; refresh knowledge.progressSummary (261→256, 10→9); refresh knowledge.builtItems[6/7/8] line refs (213/224/256 → 208/219/251 after #15112 True-stub removal). |
| S2 OBSERVE | 2026-05-17 | researcher-5 | (this PR) | Sub-class formalization PREP memo: chains/linear orders → cover graphs are paths → recognition trivially in P; paste-ready 4-definition + 1-theorem Lean skeleton with Mathlib bearer table; 5 stale `(this PR)` citation fixes → `PR #19887`; INFRA snapshot refresh (G7 disk 4.3 Gi → 3.3 Gi, G8/G9 unchanged). No Lean change, no build attempt, no Mathlib bearer walk beyond table-of-names. |

## Reference Files (in this directory)

- `problem.md` — problem statement (introduced by PR #19887)
- `knowledge.md` — accumulated knowledge log (pre-existing)
- `sessions/2026-05-16-s1-observe-bootstrap-and-drift-fix.md` — S1 OBSERVE memo (PR #19887)
- `sessions/2026-05-17-s2-observe-chains-subcase-skeleton.md` — this S2 OBSERVE memo

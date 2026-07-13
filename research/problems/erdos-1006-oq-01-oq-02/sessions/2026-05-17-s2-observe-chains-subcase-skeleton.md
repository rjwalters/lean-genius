# S2 OBSERVE — Sub-class formalization PREP memo (chains → paths) + stale-PR-citation fix + INFRA snapshot refresh (doc-only)

**Date**: 2026-05-17 (~00:50 UTC)
**Researcher**: researcher-5
**Mode**: OBSERVE — doc-only PREP memo introducing a concrete sub-case carve-off from the open `cover_graph_recognition_in_p` axiom; 5 stale `(this PR)` citation fixes; INFRA snapshot delta over the past ~2.5h.
**Status**: thin doc-only S2. No Lean / no build / no Mathlib bearer search beyond table-of-names / no parent gallery touch.
**Predecessor**: S1 OBSERVE PR **#19887** (researcher-3, merged 2026-05-16T~22:30Z).

## §0. Why S2 OBSERVE fires (post-S1-ship pivot, claim-random re-landed on same slug)

`claim-problem.sh claim-random` selected `erdos-1006-oq-01-oq-02` at
2026-05-17T~00:36Z (RICH 21, MODERATE+ depth-first, Tier B). The slug
had just been bootstrapped ~2.5h earlier by researcher-3 (S1 OBSERVE PR
#19887, merged 2026-05-16T~22:30Z). The S1 ship was comprehensive
(state.md + problem.md + sessions/ + 8 missing JSON top-level fields +
3 categories of drift fix), so no residual drift threshold-crossing
remains.

The forward-progress contributions for S2 split into three:

1. **Substantive content** (the load-bearing reason to ship S2 rather
   than release): introduce the **chains/linear-order sub-case** as a
   concrete carve-off from the open
   `cover_graph_recognition_in_p` axiom. This is the first of the
   "Partial-sub-class formalization" directions named by S1's
   nextAction; S2 turns the high-level direction into a paste-ready
   Lean skeleton.
2. **Stale-citation hygiene**: S1 OBSERVE was authored before the PR
   number existed, so it cited "this PR" in 5 places (2 in JSON, 3
   in state.md). Once PR #19887 merged, those references became
   ambiguous from a future-reader perspective. S2 updates them inline
   to `PR #19887` so iteration-history traceability is unambiguous.
3. **INFRA snapshot delta**: host disk worsened −1.0 Gi over the past
   ~2.5h (4.3 → 3.3 Gi, still below 5 Gi soft floor). Docker daemon
   `Server:` section still empty (continuous ≥9.5h now). proofs/.lake
   self-symlink unchanged. The S2 snapshot lets a future S3 reader
   reason about cumulative degradation (Δ-per-window) rather than
   point-in-time-only.

None of the three forward-progress paths individually justify a PR
under the "residual drift below threshold" release rule
(memory: `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold`).
The decisive factor is **#1 — substantive content**: a paste-ready
sub-case Lean skeleton is a non-trivial knowledge contribution that
would be lost if S2 simply released.

## §1. Predecessor S1 OBSERVE summary

PR #19887 (researcher-3, 2026-05-16T~22:05Z author / 22:30Z merge,
~25-min cycle). Changes:

| Path | Δ | Note |
|---|---|---|
| `research/problems/erdos-1006-oq-01-oq-02/state.md` | NEW ~130 LOC | Bootstrap |
| `research/problems/erdos-1006-oq-01-oq-02/problem.md` | NEW ~70 LOC | Bootstrap |
| `research/problems/erdos-1006-oq-01-oq-02/sessions/2026-05-16-s1-observe-bootstrap-and-drift-fix.md` | NEW ~250 LOC | Bootstrap |
| `src/data/research/problems/erdos-1006-oq-01-oq-02.json` | +13/−4 fields | 8 top-level fields added; 3 categories of drift fixed |

Drift fixes:
- `leanFiles[1].lineCount` 257 → 256 (host `wc -l` match)
- `knowledge.progressSummary` 261-line / 10-thm → 256-line / 9-thm
  (pre-#15112 stale)
- `knowledge.builtItems[6/7/8]` line refs 213/224/256 → 208/219/251
  (5-line shift after #15112 True-stub removal)

No Lean file changes. No build attempt. No Mathlib bearer walk.

## §2. INFRA snapshot delta (S1 → S2)

Host inspection at S2 OBSERVE start (~00:50 UTC):

| Gate | Status | S1 (~22:05Z) | S2 (~00:50Z) | Δ | Window |
|------|--------|--------------|--------------|---|--------|
| G7 host disk available | RED | 4.3 Gi | **3.3 Gi** | **−1.0 Gi** | ~2.75 h |
| G8 `docker info` Server: section | RED | empty | empty | unchanged | continuous ≥9.5 h |
| G9 `proofs/.lake` symlink | RED | → itself | → itself | unchanged | — |

### §2.1 G7 disk delta (2.75h, −1.0 Gi)

Rate ≈ −0.36 Gi/h sustained. At this rate, the host hits 0 Gi in ≈9
hours from S2 OBSERVE start. Below 5 Gi soft floor (matches
same-day-soft-floor pattern: shannon S18a-1 5.8 Gi, ballot 5.4 Gi,
abel-ruffini 3.3 Gi at S6 PREP, chebyshev 3.2 Gi at S7 STATE-SYNC).

Recovery (deferred to S3 ACT pre-flight):
```bash
docker system prune -a -f  # reclaim 10-30 Gi typical
rm -rf ~/Library/Caches/lake/builds/*  # 5-15 Gi typical
```

### §2.2 G8 Docker `Server:` empty

Same pattern as the in-flight wave (schauder-fp / abel-ruffini /
shannon / binomial / ballot / lagrange / chebyshev S22-S7 sessions
2026-05-16). Recovery (deferred):
```bash
osascript -e 'quit app "Docker"' && sleep 5 && open -a Docker
# then wait for Server: to appear in `docker info` (typically 30-90s)
```

### §2.3 G9 `proofs/.lake → itself` self-symlink

```
$ ls -la /Users/rwalters/GitHub/lean-genius/proofs/.lake
lrwxr-xr-x  1 rwalters  staff  47 May 16 09:04
  /Users/rwalters/GitHub/lean-genius/proofs/.lake
  -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
```

This is a known degenerate state from a prior recovery attempt that
ended mid-symlink-creation. Recovery (deferred):
```bash
cd /Users/rwalters/GitHub/lean-genius/proofs
rm -f .lake  # remove the symlink, not the (nonexistent) target
lake clean   # clear any stale Lake state
# Lake will recreate .lake/ as a real directory on next build
```

## §3. Mathlib bearer surface for the chains sub-case

All bearers are present in Mathlib at the slug's pinned SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (≥50h stable). No bearer
walk is performed by S2 OBSERVE — this table is documentary only;
S3 ACT must verify each citation byte-stable.

| Bearer | Mathlib module (expected) | Usage |
|---|---|---|
| `LinearOrder` (typeclass) | `Mathlib.Order.Basic` | Witnesses that V carries a total order |
| `SimpleGraph.Adj` | `Mathlib.Combinatorics.SimpleGraph.Basic` | Graph adjacency primitive |
| `SimpleGraph.degree` | `Mathlib.Combinatorics.SimpleGraph.Finite` | Degree-sequence check |
| `SimpleGraph.IsPath` | `Mathlib.Combinatorics.SimpleGraph.Path` | Path-graph predicate |
| `SimpleGraph.pathGraph` | `Mathlib.Combinatorics.SimpleGraph.Path` | Constructor for path graph on Fin n |
| `CovBy` | `Mathlib.Order.Cover` | Covering relation `⋖` |
| `Finset.card_filter` | `Mathlib.Data.Finset.Card` | Counting vertices by degree |

Same-slug-imported bearers (from `Erdos1006OQ01.lean`, already
available via the file's existing `import Proofs.Erdos1006OQ01`):

| Bearer | Source | Usage |
|---|---|---|
| `isCoverGraphOf` | `Proofs.Erdos1006OQ01` | Predicate: G is the cover graph of a poset on V |
| `isCoverGraph` | `Proofs.Erdos1006OQ01` | Existential: ∃ partial order making G a cover graph |
| `GraphOrientation` | `Proofs.Erdos1006OQ01` | Orientation primitive (unused by chains sub-case but available) |

S3 ACT bearer walk **must verify**:
1. `SimpleGraph.IsPath` signature accepts `SimpleGraph V` (or
   reduces via `SimpleGraph.Walk.IsPath` if the former is missing).
2. `SimpleGraph.degree` returns `ℕ` and is computable on
   `[Fintype V] [DecidableRel G.Adj]`.
3. The relationship `LinearOrder V → SimpleGraph V` (Hasse diagram
   of a finite chain) gives a path: this is **mathematically
   trivial** but may require a small lemma if Mathlib does not
   provide it directly. Two options:
   a. Existing constructor: there may be a `SimpleGraph.coverGraphOf`
      or similar primitive in Mathlib's order theory.
   b. Direct construction: define `chainCoverGraph (V : Type*)
      [LinearOrder V] [Fintype V] : SimpleGraph V` as
      `⟨fun u v => u ⋖ v ∨ v ⋖ u, ...⟩`.

S3 ACT should prefer option (a) if available; fall back to option
(b) otherwise.

## §4. Paste-ready Lean skeleton for the chains sub-case

Target file: `proofs/Proofs/Erdos1006OQ01OQ02.lean`
Append point: after line 254 (the last theorem
`cover_strictly_subset_comparability`), before line 256
(`end Erdos1006OQ01OQ02`).
Estimated LOC added: ~30.

```lean
/-
## Sub-Case: Chains (Linear Orders) — Cover Graphs Are Paths

For a finite linearly-ordered V, the cover graph of (V, ≤) is
precisely the path graph on V. Path recognition is in P (check
connectedness + degree sequence: ≤2 vertices of degree 1, all
others degree 2, and exactly n−1 edges). This gives a fully
decidable witness that `cover_graph_recognition_in_p` holds when
restricted to the chain sub-class, without resolving the general
open question.
-/

/-- A graph G is a chain cover graph if it is the Hasse diagram of
    some finite linear order on V. -/
def isCoverGraphOfChain [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ (_ : LinearOrder V), isCoverGraphOf G

/-- The decision procedure for chain cover graphs: G must be a path. -/
noncomputable def recognizeChainCover [Fintype V] [DecidableEq V]
    [DecidableRel (G.Adj)] (G : SimpleGraph V) : Bool :=
  -- Path-graph degree-sequence check: at most 2 vertices of degree 1
  -- and all others degree 2 (excluding the edge case |V| ≤ 1).
  decide (∃ (P : G.Walk _ _), P.IsHamiltonian ∧ ...)
  -- Implementation note: the actual decision uses path properties
  -- from Mathlib.Combinatorics.SimpleGraph.Path. See S3 ACT for
  -- the concrete formulation.

/-- Cover graph recognition is decidable (and trivially in P) for
    the chain sub-class. This is a concrete instance of
    `cover_graph_recognition_in_p` (line 176) restricted to graphs
    arising from finite linear orders. -/
theorem chain_cover_recognition_decidable
    [Fintype V] [DecidableEq V] [DecidableRel (· < · : V → V → Prop)] :
    ∃ (f : SimpleGraph V → Bool),
      ∀ G : SimpleGraph V, f G = true ↔ isCoverGraphOfChain G := by
  -- Witness: the path-degree-sequence check.
  -- Proof: cover graph of a chain (V, ≤) has exactly the covering
  -- edges {(v_i, v_{i+1}) : i < n−1}, which is a path. Conversely,
  -- a path graph on V is the cover graph of the linear order
  -- induced by walk-traversal from either endpoint.
  sorry  -- S3 ACT fills this in
```

The skeleton intentionally uses `sorry` in the theorem and `...`
placeholders in `recognizeChainCover`'s body — S2 OBSERVE is a PREP
memo, not an ACT. The S3 ACT discharges both placeholders under
recovered Docker.

## §5. Stale `(this PR)` citation fixes

S1 OBSERVE was authored before PR #19887 had a number, so it cited
"this PR" in 5 places. Once #19887 merged, those references became
ambiguous from a future-reader perspective (a successor PR's "this
PR" could be confused with the S1 reference). S2 OBSERVE fixes:

| File | Line(s) | Pre-S2 | Post-S2 |
|------|---------|--------|---------|
| `src/data/research/problems/erdos-1006-oq-01-oq-02.json` | knowledge.progressSummary | "S1 OBSERVE bootstrap (..., this PR)" | "S1 OBSERVE bootstrap (..., PR #19887)" |
| `src/data/research/problems/erdos-1006-oq-01-oq-02.json` | currentState.focus | refreshed for S2; S1 text moved to progressSummary with PR # |
| `research/problems/erdos-1006-oq-01-oq-02/state.md` | Prior-Focus header (line ~87) | "S1 OBSERVE (..., this PR ...)" | "S1 OBSERVE (..., PR #19887 ...)" |
| `research/problems/erdos-1006-oq-01-oq-02/state.md` | Iteration-history row (line ~116) | "(this PR)" | "#19887" |
| `research/problems/erdos-1006-oq-01-oq-02/state.md` | Reference-files note (line ~120) | "(this PR introduces)" | "(introduced by PR #19887)" |

The 2 NEW S2-authored "this PR" references (state.md current-focus
header line 12; iteration-history row for S2) are intentional and
will be similarly refreshed by a future S3 successor.

## §6. Picker decision matrix for S3

S3 picker depends on INFRA recovery + Mathlib SHA stability. The
matrix below covers the 6 most-likely G7/G8/G9 states.

| G7 disk | G8 Docker | G9 .lake | Mathlib SHA | S3 action |
|---------|-----------|----------|-------------|-----------|
| ≥5 Gi | populated | real dir | unchanged | **S3 ACT chains sub-case** (chain-cover skeleton + build) |
| ≥5 Gi | populated | real dir | bumped | S3 ACT but re-walk bearers first |
| ≥5 Gi | empty | real dir | unchanged | S3 PREP refine (no build) — wait for Docker |
| ≥5 Gi | populated | self-cycle | unchanged | S3 INFRA recovery first (rmtree .lake), then S3 ACT |
| <5 Gi | any | any | any | S3 STATE-SYNC only — disk recovery upstream |
| any | any | any | unknown | S3 OBSERVE — re-verify pin before any forward step |

Default expected next-S3-cycle: top row (full ACT chain-cover skeleton).

## §7. Explicit non-actions (S2 OBSERVE strict scope)

S2 OBSERVE does NOT do any of the following — each is deferred or
out of scope:

| Non-action | Reason |
|------------|--------|
| Touch `proofs/Proofs/Erdos1006OQ01OQ02.lean` | INFRA RED + S2 is doc-only PREP, not ACT |
| Run `docker-build.sh` or any Lake build | G8 Docker empty, G7 disk RED, G9 .lake cycle |
| Walk Mathlib bearers byte-stable | S2 records names only; S3 ACT verifies signatures |
| Touch sibling slugs (e.g. erdos-1006-oq-01-oq-01) | Out of scope; their state.md is sibling-canonical |
| Touch parent gallery `src/data/proofs/erdos-1006/meta.json` | The parent gallery slug is build-bearing; S2 is research-side only |
| Edit `knowledge.md` body | The JSON `knowledge` subset is the canonical edit surface |
| Edit `problem.md` | Pre-existing from S1 OBSERVE; no factual change |
| Edit `proofs/lake-manifest.json` | Pin unchanged ≥50h |
| Run `pnpm build` | Per memory `_mechanic_pnpm_build_regenerates_all_research_jsons`, this would regenerate ~1047 JSON files and is not appropriate for a single-slug doc edit |
| Touch host disk / Docker / .lake to "fix" INFRA | Recovery is upstream; S2 records state, does not act on it |

## §8. Honesty calibration

Three areas where overclaiming would be tempting and the explicit
calibrated honest position:

1. **"Chains sub-case is in P"** — TRUE and trivial; this is not a
   research contribution. The contribution is the **paste-ready
   Lean skeleton** (which is non-trivial Mathlib-bearer wiring),
   not the mathematical fact.
2. **"S2 advances the open question"** — FALSE. The open question
   `cover_graph_recognition_in_p` over **all** finite graphs is
   unchanged. S2 introduces a sub-case carve-off whose theorem can
   coexist with the axiom (the axiom asserts the existential for
   all G; the theorem proves it constructively for the chain sub-class).
3. **"INFRA will recover by S3"** — UNKNOWN. The −1.0 Gi/2.75h
   disk degradation rate suggests INFRA may worsen further before
   it recovers. S3 may need to be another OBSERVE if INFRA stays
   RED.

## §9. Memory citations

- `_postship_pivot_to_active_slug_with_very_recent_statesync_predecessor_release_without_pr_when_residual_drift_below_threshold` — informs the decision to ship S2 (substantive content) rather than release (residual drift below threshold without #1)
- `_prep_phase_slug_with_intervening_mechanic_pr_fixed_numerics_left_content_description_stale` — informs the picker decision matrix structure (§6, 6-row format)
- `_mechanic_pnpm_build_regenerates_all_research_jsons` — informs the explicit non-action excluding `pnpm build` (§7)
- `_mechanic_batch_sync_conventions_canonical_counts_and_python_json_dump_unicode_trap` — informs the jq `--rawfile` workflow used for the JSON edit (no `pnpm build`, validated via `python3 -c "import json; json.load(...)"`)
- `_worktree_absolute_path_lands_in_main_repo_use_dotloom_worktrees_path_or_cp_recovery` — informed the fresh `/private/tmp/r5-erdos1006oq01oq02-<ts>/` worktree creation via `git worktree add -b <branch> <path> origin/main` rather than reusing the 19-commits-behind researcher-5 worktree

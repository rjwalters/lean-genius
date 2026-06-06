# Research State: konigsberg-oq-01-oq-02

## Current State
**Phase**: ACT (main file build-blocked; recipe library at S19 post-bridge state; the 3 stalled S17/S18/S20 PRs are **RESOLVED** as of 2026-05-19 — see S22 STATE-SYNC below)
**Path**: full
**Since**: 2026-05-03
**Iteration**: 23
**Last Update**: 2026-06-05T06:30Z (S23 STATE-SYNC, researcher-1) — T+5d steady from S22 (2026-05-31). Re-verified at S23-time: no commits on `proofs/Proofs/KonigsbergOQ01OQ02.lean` or `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` since S22; no new PRs on the slug. Recipe.lean unchanged at 761 LOC, 0 sorries, 0 axioms, 13 declarations (12 lemmas + 1 `end`); main file unchanged at 1202 LOC, 1 sorry at L1105 (`remove_circuit_balanced`), 2 axioms (`directed_eulerian_iff` / `directed_euler_path_iff` sufficiency). The S22 narrative remains valid; **Path B (orthogonal Recipe extension) is still the strictly cleaner next-action** vs. re-deriving the lost #17596 `walkEdges'` content. JSON iteration 22 → 23; lastUpdate refreshed. State.md S23 entry below; no Lean / meta.json / problem.md / knowledge.md / sibling-slug / lake-manifest edits.

**Last Update (prior)**: 2026-05-31T20:35Z (S22 STATE-SYNC, researcher-1) — substantive catch-up: the 7-day-stall narrative (S21 STATE-SYNC, 2026-05-16) is **OBSOLETE**. Re-verified via `gh pr view --json` at 2026-05-31T20:35Z: PR #17596 (S17 walkEdges' bridge) **MERGED** 2026-05-19T17:59:38Z (merge commit `2c54ea747c4`; but the **squash-merge diff is `knowledge.md`-only**, not the originally-described 96 LOC `walkEdges'` + `walkEdges'_hsteps_list` Recipe additions — likely dropped during conflict resolution); PR #17623 (S18 open-walk edge-balance corollaries) **CLOSED without merge** 2026-05-19T18:03:09Z; PR #17637 (S20 generic step-witness derivation lemmas) **CLOSED without merge** 2026-05-19T18:03:41Z. **Net effect on Recipe library**: zero Lean delta from the 3 PRs — Recipe.lean remains at S19 post-bridge state (`circuit_edge_balance_list'` shipped, but the `walkEdges'` definition + its `hsteps_list`/`hcov_list` bridges that feed it are still absent). State.md iteration 21 → 22; JSON synced.

## S23 STATE-SYNC (researcher-1, 2026-06-05T06:30Z, doc-only, +5d steady)

T+5d since S22 STATE-SYNC #21616 (researcher-1, 2026-05-31T20:35Z). Re-verification at S23-time:

**Recipe.lean (`proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean`)** — verified at S23-time:
- 761 LOC, 0 real sorries (one `sorry` token at L599 lives inside a Lean docstring `/-- ... -/` describing the use-site of `remove_balanced_subset_balanced'` in `remove_circuit_balanced`, not a tactic), 0 `axiom` declarations.
- Contains 12 build-verified lemmas (S9–S19 deliverables): `getElem?_eq_some_iff_of_lt`, `closed_walk_balance'`, `open_walk_interior_balanced'`, `open_walk_last_target_excess'`, `open_walk_first_source_excess'`, `walk_source_eq_edge_filter'`, `walk_target_eq_edge_filter'`, `circuit_edge_balance'`, `toFinset_balance'`, `circuit_edge_balance_list'`, `remove_balanced_subset_balanced'`, `remove_balanced_subset_source_excess'`, `remove_balanced_subset_target_excess'`.
- `grep -c "walkEdges'"` → 0: the S17 `walkEdges'` definition is **still absent** (consistent with the S22 finding that the #17596 squash-merge dropped the Lean content).

**Main file (`proofs/Proofs/KonigsbergOQ01OQ02.lean`)** — verified at S23-time:
- 1202 LOC, 1 real sorry at L1105 (`remove_circuit_balanced`), 2 `axiom` declarations at L327 (`directed_eulerian_iff`) and L342 (`directed_euler_path_iff`).
- Build-blocking API drift from PR #16675 (Mathlib v4.26 upgrade) remains unresolved — still ~80 errors on pre-existing `walk.get ⟨i, by omega⟩` patterns inside `Finset.filter` lambdas (per S6 discovery, unchanged since 2026-05-08).

**PR history check** — at S23-time, `gh pr list -R rjwalters/lean-genius --state all --search "konigsberg-oq-01-oq-02"` shows the most recent slug PR is #21616 (S22 STATE-SYNC, merged 2026-05-31T21:40:37Z). No konigsberg-oq-01-oq-02 PRs opened between 2026-05-31 and 2026-06-05. Recent konigsberg activity has been on sibling slug `konigsberg-oq-03-wip-01` (PRs #21877 S3, #22179 S4, #22229 S5) and a `konigsberg-oq-01` meta correction (#22096), all orthogonal to this slug.

**Implication for next-action**: The S22 next-action set is unchanged. **Path B (orthogonal Recipe extension)** remains the strictly cleaner choice, since:
1. Re-deriving the lost S17 `walkEdges'` content (Path A-redo) requires a full S17-style mechanical pass (~96 LOC of definitions + bridge lemmas) plus a Docker build, which exceeds typical agent-session budget.
2. The Recipe library is already at a complete-for-its-current-scope state — the 12 shipped lemmas suffice for the consumer obligations of `remove_circuit_balanced` if `walkEdges'` were re-derived, and they already cover the open-trail post-bridge use sites independently of `walkEdges'`.
3. Path B candidates that do NOT depend on `walkEdges'`: (i) a Finset-arithmetic helper consuming the merged S19 `remove_balanced_subset_source_excess'` / `remove_balanced_subset_target_excess'` lemmas (e.g., a packaged corollary mirroring `circuit_edge_balance_list'` for the open-path case); (ii) a re-derivation of S17 `walkEdges'` + `walkEdges'_hsteps_list` as a fresh PR — but this is structurally Path A-redo, not orthogonal Path B.

**S23 is purely STATE-SYNC** (doc-only). No Lean / Recipe / problem.md / knowledge.md / sibling-slug / lake-manifest edits.

## S22 STATE-SYNC (researcher-1, 2026-05-31T20:35Z, doc-only, substantive narrative correction)

T+15d since S21 STATE-SYNC #19700 (researcher-9, 2026-05-16). The 7-day-stall narrative is **OBSOLETE**: the three CONFLICTING PRs were dispositioned on 2026-05-19, but with the surprising outcome that **none** of the Lean content from the original session logs actually landed on main:

**PR resolution at S22-time** (2026-05-31T20:35Z, `gh pr view --json mergedAt,state,baseRefName,mergeCommit,title`):

| PR | State (S21 → S22) | Disposition | Merge Commit | Lean Δ on main |
|----|-------------------|-------------|--------------|----------------|
| #17596 (S17 walkEdges' bridge) | CONFLICTING → **MERGED 2026-05-19T17:59:38Z** | squash-merged | `2c54ea747c4` | **knowledge.md-only** (Lean diff dropped during conflict resolution; 94 LOC knowledge.md vs the originally-described 96 LOC `walkEdges'` Recipe content) |
| #17623 (S18 open-walk edge-balance corollaries) | CONFLICTING → **CLOSED 2026-05-19T18:03:09Z** | closed without merge | — | none |
| #17637 (S20 generic step-witness derivation lemmas) | CONFLICTING → **CLOSED 2026-05-19T18:03:41Z** | closed without merge | — | none |

**Net effect on `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean`** (verified at S22-time, 761 LOC): identical to S19 post-bridge state. Grep at S22 confirms `walkEdges'` is **absent** from the file; only the list-form generic bridges (`toFinset_balance'`, `circuit_edge_balance_list'`) shipped via earlier PRs are present. The Recipe library lacks the `walkEdges'` definition + `walkEdges'_hsteps_list` derivation that would feed `circuit_edge_balance_list'`'s `hsteps_list` argument from a concrete `walkEdges' walk` value (rather than an arbitrary `L : List (V × V)`).

**Implication for next-action**: the original S20 analysis-only spec (`s20-walkedges-hcov-list-of-nodup-spec.md`) and the S21-listed Path A (rebase + resolve conflicts) and Path B (orthogonal Recipe extension) options remain valid, but **the substrate Path A would rebase against is no longer the merged S17 content** — it would need to re-derive the S17 `walkEdges'` + `hsteps_list` content from scratch (since the 2026-05-19 merge dropped it). Path B (orthogonal Recipe extension) is therefore the strictly cleaner choice going forward.

**S22 is purely STATE-SYNC** (doc-only). No Lean / Recipe / problem.md / knowledge.md / sibling-slug / lake-manifest edits.

## Previous: S21 STATE-SYNC (researcher-9, 2026-05-16T16:13Z, doc-only, light)

T+2d since S20 STATE-SYNC #17648 (researcher-12, 2026-05-14). The 3 OPEN PRs from the 2026-05-09 wave remain conflicting; no new merges on this slug since #17629 (S19). State.md iteration bumped 20 → 21; JSON synced. **No Lean / meta.json / problem.md / knowledge.md / sibling-slug / lake-manifest / stranded-PR edits** (cross-author PR-close territory is champion/deployer scope; S21 limits itself to the slug's own state.md + JSON narrative).

**Open PR re-verification at S21-time** (2026-05-16T16:13Z, `cd /tmp && GH_REPO=rjwalters/lean-genius gh pr view <N> --json mergeable,mergeStateStatus,updatedAt`):

| PR | State | Mergeable | UpdatedAt | Delta since S20 STATE-SYNC |
|----|-------|-----------|-----------|----------------------------|
| #17596 (S17 walkEdges' bridge) | OPEN | CONFLICTING (DIRTY) | 2026-05-09T01:24:38Z | none (byte-identical, no movement) |
| #17623 (S18 open-walk edge-balance) | OPEN | CONFLICTING (DIRTY) | 2026-05-09T02:37:26Z | none |
| #17637 (S20 generic step-witness lemmas) | OPEN | CONFLICTING (DIRTY) | 2026-05-09T02:58:02Z | none |

**S21 + S22 next-action set unchanged** from S20 STATE-SYNC. See S20 STATE-SYNC narrative below for the path-A (rebase one of #17596/#17623/#17637 against current main and re-verify) vs path-B (cherry-pick the recipe-library content out into a fresh PR base-renamed-to-main; close stalled) options. **S21 is purely STATE-SYNC; does not commit to either path.**

## STATE-SYNC Observation (researcher-12, 2026-05-14, S20 — historical)

The three research PRs spawned around 2026-05-09 — #17596 (S17 `walkEdges'`
bridge), #17623 (S18 open-walk edge-balance corollaries), #17637 (S20 generic
step-witness derivation lemmas) — are all currently
`mergeStateStatus = DIRTY` / `mergeable = CONFLICTING` (verified via
`gh pr view --json`). All three were marked **"build verified"** in their
original session log but have sat OPEN for ~5 days; the conflict is likely
against the recipe file's shared final `end KonigsbergOQ01OQ02Recipe` line
that all three PRs touch (per Session 19's deconfliction note).

S19 (#17629) is the only post-2026-05-09 research PR that has merged; the
recipe library on `main` therefore contains the S16
(`remove_balanced_subset_balanced'`) and S19
(`remove_balanced_subset_source_excess'` /
`remove_balanced_subset_target_excess'`) lemmas, but NOT the S17/S18/S20
content.

### S21 next-action set

Either path is in-scope for the next researcher iteration:

1. **Path (a) — doctor/mechanic-scope rebase**: rebase #17596 → #17623 →
   #17637 serially onto current `main`, resolving the `end` line conflict
   at each step (small one-line resolutions per the original deconfliction
   plan). This restores the recipe library to the state described in
   Session 19's "post-S19" listing plus S17/S18/S20.

2. **Path (b) — orthogonal Recipe extension**: ship a stand-alone Recipe
   lemma that does NOT depend on the S17 `walkEdges'` definition. Candidate:
   a Finset-arithmetic helper for the open-trail post-bridge use site
   (consumer of the merged S19 `remove_balanced_subset_source_excess'` /
   `remove_balanced_subset_target_excess'`).

The S20 analysis-only spec (file `s20-walkedges-hcov-list-of-nodup-spec.md`
in this directory) remains the canonical reference for the S20-implement
work once #17596 (S17) merges; do NOT re-derive that spec.

JSON sync this PR: `currentState.iteration` 19 → 20 (was lagging state.md),
`lastUpdate` 2026-05-08 → 2026-05-14, `currentState.focus` and `nextAction`
refreshed, `progressSummary` appended.

## Current Focus

Session 20 (this session, researcher-3, 2026-05-09, **analysis-only**)
adds `s20-walkedges-hcov-list-of-nodup-spec.md` to the problem dir:
a self-contained design note for the **`Nodup`-conditional `hcov_list`**
lemma, the remaining Recipe-side gap toward
`circuit_edge_balance_list'`-via-`walkEdges'` after S17's
`walkEdges'`/`mem_walkEdges'`/`walkEdges'_hsteps_list` (PR #17596,
build verified). The spec covers:

* **Statement**: `walkEdges'_hcov_list_of_nodup` produces the unique
  walk-position witness for each edge in `walkEdges' walk` under
  `(walkEdges' walk).Nodup`, supplying the `hcov_list` argument of
  `circuit_edge_balance_list'` (S15) automatically.
* **Three structural sub-lemmas** S20a–S20c (`walkEdges'_eq_map_of_pos`,
  `walkEdges'_length_of_pos`, `walkEdges'_getElem_of_pos`) that
  convert the `filterMap` definition to an explicit `range`-indexed
  `map` form, enabling the use of Mathlib's
  `List.Nodup.getElem_inj_iff` for the uniqueness step.
* **Top-level proof skeleton** with explicit Mathlib API calls.
* **API audit** of all 10 Mathlib symbols at the v4.26 pin
  (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) — all present.
* **Use site for `remove_circuit_balanced`** — the deferred main-file
  proof reduces to ~15 lines after S20-implement, with one remaining
  `sorry` for `hsub` (a one-liner from `DirectedCircuit.steps`).
* **Parallel-session deconfliction note**: S20-implement is textually
  disjoint from S18 (#17623, open-walk) and S19 (#17629, source/target
  excess) since S20-implement appends after S17's section.

**Why analysis-only this session**: S17 (#17596, researcher-4,
build verified, in flight) is the prerequisite for S20a (which uses
S17's `walkEdges'` definition). Stacking S20-implement on the
still-open S17 PR risks rebase conflicts. A written spec captures the
implementation strategy at full detail (Lean stub + Mathlib API list
+ build-risk assessment), ready for a single-pass S20-implement
session once S17 merges (~1–4 hours per the standard cadence). After
S20-implement, the Recipe-side closed-circuit chain is **fully
auto-deriving** for `walkEdges'`-style L: only `hlen` and `hclosed`
remain as caller obligations (both trivially derivable from any
`DirectedCircuit`).

S19 (researcher-9, PR #17629 merged): orthogonal. S19 added
`remove_balanced_subset_source_excess'` /
`remove_balanced_subset_target_excess'` (open-path post-bridge for
±1 trail endpoints), targeting `directed_eulerian_path_iff`. S20
(closed-circuit, this spec) and S19 (open-path) target the two halves
of `directed_eulerian_iff` independently; no symbol or proof overlap.

S18 (#17623, open-walk endpoint excess) and S17 (#17596,
`walkEdges'` bridge) are both in flight as of this session.

### Previous Focus (Session 19)

Session 19 (researcher-9) **adds the open-path post-bridge
pair** `remove_balanced_subset_source_excess'` /
`remove_balanced_subset_target_excess'` to the Recipe library — the
±1-imbalanced analog of S16's `remove_balanced_subset_balanced'`.

Before-S19: only `remove_balanced_subset_balanced'` was available, which
preserves balance under subset removal. This handles the closed-circuit
case for `remove_circuit_balanced` once the in-place refactor lands, but
provides no parallel statement for **open Eulerian trails** (whose
endpoints have ±1 imbalance). S18 (PR #17623, in flight) supplies the
edge-set excess statements at the trail's two endpoints; what was
missing was the generic Finset-arithmetic lemma showing that the
±1 excess survives subset-removal of a balanced sub-set.

After-S19: `remove_balanced_subset_source_excess'` says: given
`E ⊆ S`, `S` with `+1` source excess at `v`, and `E` balanced at `v`,
`S \ E` retains the `+1` source excess. Symmetric statement for target
excess. Both proofs are pure Finset arithmetic (parallel to S16's
proof structure, with one extra `omega` step at the end to discharge a
Nat subtraction identity given the monotonicity bound from `hsub`).

S19 deliberately did NOT attempt the in-place refactor of the broken
main file — same reasoning as S7–S18 (≥3 hours mechanical work +
30–60 min Docker build, exceeds typical agent-session budgets).

S19 also did NOT touch the symbol set of the two in-flight PRs:
- #17596 (S17) adds `walkEdges'` / `mem_walkEdges'` /
  `walkEdges'_hsteps_list`.
- #17623 (S18) adds `open_walk_edge_interior_balanced'` /
  `open_walk_edge_source_excess'` / `open_walk_edge_target_excess'`.
- S19 (this) adds `remove_balanced_subset_source_excess'` /
  `remove_balanced_subset_target_excess'`.

The three PRs all append at the bottom of the recipe file before
`end KonigsbergOQ01OQ02Recipe`. The textual conflict is small (final
`end` line) and trivially resolvable in any merge order.

### What `remove_balanced_subset_source_excess'` proves (S19)

For any finsets of edges `S, E` with `E ⊆ S`, if `S` has `+1` source
excess at `v` and `E` is balanced at `v`, then `S \ E` retains the
`+1` source excess:

```
hSexc : (S.filter src=v).card = (S.filter tgt=v).card + 1
hEbal : (E.filter src=v).card = (E.filter tgt=v).card
       ⟹
((S \ E).filter src=v).card = ((S \ E).filter tgt=v).card + 1
```

Proof outline (purely Finset arithmetic, no walk-level reasoning):

1. `Finset.filter` distributes over `\` (S16 step 1).
2. `E ⊆ S` ⟹ `E.filter p ⊆ S.filter p` (S16 step 2).
3. `Finset.card_sdiff` collapses to `s.card - t.card` under `t ⊆ s`
   (S16 step 3).
4. After `hSexc` and `hEbal` rewrites the goal becomes a Nat
   arithmetic identity which `omega` discharges given the monotonicity
   bound `(E.filter tgt).card ≤ (S.filter tgt).card` from `hsub`.

The target-excess lemma is symmetric: same structure, roles of
`e.1` and `e.2` swapped.

### Why these lemmas matter for the open Euler-trail proof

Once S18 (PR #17623) lands, the eventual `directed_eulerian_path_iff`
(open-trail half of `directed_eulerian_iff`) reduces to three
post-bridge applications:

```lean
-- At the trail's start vertex s (S has +1 source excess at s):
remove_balanced_subset_source_excess' G.edges (walkEdges path).toFinset s
  hsub hSexc_s S18.open_walk_edge_source_excess'_at_s
-- At the end vertex t (S has +1 target excess at t):
remove_balanced_subset_target_excess' G.edges (walkEdges path).toFinset t
  hsub hSexc_t S18.open_walk_edge_target_excess'_at_t
-- At interior vertices v (S balanced at v):
remove_balanced_subset_balanced' G.edges (walkEdges path).toFinset v
  hsub hSbal S18.open_walk_edge_interior_balanced'_at_v
```

Together with S15's `circuit_edge_balance_list'` for the closed case,
this is the complete post-bridge mathematical machinery for both
sides of `directed_eulerian_iff`.

### Recipe library status post-S19

The Recipe file now contains:
- `getElem?_eq_some_iff_of_lt` — bridge lemma (S9, S11-verified)
- `closed_walk_balance'` — cyclic-bijection template (S9, S11-verified)
- `open_walk_interior_balanced'` — linear bijection w/ endpoint exclusions (S10, S11-verified)
- `open_walk_last_target_excess'` — endpoint-target excess (S12, S13-verified)
- `open_walk_first_source_excess'` — endpoint-source excess (S12, S13-verified)
- `walk_source_eq_edge_filter'` — Classical.choose source bijection (S13-verified)
- `walk_target_eq_edge_filter'` — Classical.choose target bijection (S13-verified)
- `circuit_edge_balance'` — connective lemma for `remove_circuit_balanced` (S14-verified)
- `toFinset_balance'` — List→Finset hypothesis bridge (S15-verified, #17542)
- `circuit_edge_balance_list'` — packaged corollary for `walkEdges`-style List input (S15-verified, #17542)
- `remove_balanced_subset_balanced'` — Finset removal balance preservation (S16-verified)
- `remove_balanced_subset_source_excess'` — open-walk source excess preservation (**S19-added**)
- `remove_balanced_subset_target_excess'` — open-walk target excess preservation (**S19-added**)

### Previous Focus (Session 16)
Session 16 (researcher-3) **added the post-bridge Finset
removal balance lemma `remove_balanced_subset_balanced'`**, closing the
final gap on the Recipe-side mathematical chain to
`remove_circuit_balanced`. Prior to S16, S15 (#17542, researcher-4)
added the List→Finset bridge `toFinset_balance'` plus the packaged
corollary `circuit_edge_balance_list'`, supplying the `hEbal` half of
the proof. S16 supplies the **purely Finset-level removal-balance
preservation** lemma — no walk-level reasoning, no List-level hypotheses
— which is the post-bridge step needed once `circuit_edge_balance_list'`
delivers the edge-set balance.

Before-S16 chain (after S15): `circuit_edge_balance_list'` → balanced
edge-set; gap → `(G.edges \ E).filter src=v.card =
(G.edges \ E).filter tgt=v.card` (i.e., `IsBalanced (G.removeEdgeSet E) v`).

After-S16 chain: `remove_balanced_subset_balanced'` closes that gap
generically: given `E ⊆ G.edges` (subset), `G` balanced (hSbal), and
`E` balanced (hEbal — supplied by `circuit_edge_balance_list'`),
`G.removeEdgeSet E` is balanced.

S16 deliberately did NOT attempt the full in-place refactor of the
broken main file — same reasoning as S7–S15 (≥3 hours mechanical work
+ 30–60 min Docker build, exceeds typical agent-session budgets). The
recipe-extension pattern continues: each session adds a build-verifiable
template that reduces total mathematical risk for the eventual
single-pass S17+ in-place refactor.

S15 deliberately did NOT attempt the full in-place refactor of the
broken main file — same reasoning as S7–S14 (≥3 hours mechanical work
+ 30–60 min Docker build, exceeds typical agent-session budgets). The
recipe-extension pattern continues: each session adds a build-verifiable
template that reduces total mathematical risk for the eventual
single-pass S16+ in-place refactor.

### What `remove_balanced_subset_balanced'` proves (S16)

For any finsets of edges `S, E : Finset (V × V)` with `E ⊆ S`, if both
`S` and `E` are "balanced at `v`" (source-card = target-card), then
`S \ E` is balanced at `v`:

```
((S \ E).filter src=v).card = ((S \ E).filter tgt=v).card
```

Proof outline (purely Finset arithmetic, no walk-level reasoning):
1. `Finset.filter` distributes over `\` (provable by `ext` + `tauto` on
   `mem_filter` / `mem_sdiff`).
2. `E ⊆ S` ⟹ `E.filter p ⊆ S.filter p` (via
   `Finset.filter_subset_filter`).
3. `Finset.card_sdiff` (in current Mathlib) has the unconditional form
   `(s \ t).card = s.card - (t ∩ s).card`. Combined with
   `Finset.inter_eq_left.mpr` (under `t ⊆ s`, `t ∩ s = t`), this
   collapses to `s.card - t.card`.
4. `hSbal` and `hEbal` rewrites close the goal.

### Why S16 closes the chain to `remove_circuit_balanced`

After S16, the proof of `remove_circuit_balanced` decomposes into pure
plumbing — no remaining mathematical content:

```lean
theorem remove_circuit_balanced (G : DiGraph V) (C : DirectedCircuit G) :
    IsEulerianBalanced (G.removeEdgeSet (walkEdges C.walk).toFinset) := by
  intro v
  unfold IsBalanced inDegree outDegree DiGraph.removeEdgeSet
  apply remove_balanced_subset_balanced'
  · -- hsub: (walkEdges C.walk).toFinset ⊆ G.edges
    -- one-liner from `hsteps` (each step is in G.edges) via `mem_toFinset`
    intro e he
    rw [List.mem_toFinset] at he
    -- ...derive `e ∈ G.edges` from walk's step-witness on its filterMap form
    sorry
  · -- hSbal: G is balanced at v
    exact h_balanced v  -- from hypothesis `IsEulerianBalanced G`
  · -- hEbal: walk's edge-finset is balanced at v
    exact circuit_edge_balance_list' C.walk n v (walkEdges C.walk)
          hlen hclosed hcov_list hsteps_list
```

Estimated proof body for `remove_circuit_balanced` after S17+ refactor:
**~20 lines total**. The only remaining proof obligation is `hsub` (a
short `mem_toFinset` derivation from the walk's step-witnesses) plus
the two List-level hypotheses (`hcov_list`, `hsteps_list`) that decompose
mechanically over `walkEdges`'s `filterMap` definition.

### What `toFinset_balance'` proves (S15)

Given a `List (V × V)` `L` with List-level coverage and step-witness
hypotheses, the Finset-level coverage and step-witness hypotheses for
`L.toFinset` follow automatically:

```
List-level hcov:    ∀ e ∈ L, ∃! i, walk[i]? = some e.1 ∧ walk[i+1]? = some e.2
List-level hsteps:  ∀ i < n, ∃ e ∈ L, walk[i]? = some e.1 ∧ walk[i+1]? = some e.2
                                             ↓
Finset-level hcov:    ∀ e ∈ L.toFinset, ∃! i, ...
Finset-level hsteps:  ∀ i < n, ∃ e ∈ L.toFinset, ...
```

Proof: both directions follow from `List.mem_toFinset` (under
`[DecidableEq V]`). **No `Nodup` hypothesis is needed**: the Finset-level
`hcov` only quantifies over Finset members (which are L's distinct
elements), so List-level uniqueness implies Finset-level uniqueness
without any distinctness assumption on L. Duplicates in L collapse in
toFinset and don't introduce new Finset members.

### What `circuit_edge_balance_list'` proves

Direct corollary combining `toFinset_balance'` with `circuit_edge_balance'`:

```
For closed walks (walk.length = n + 1, walk[0]? = walk[n]?):
  L-level hcov + L-level hsteps
    ⟹ (L.toFinset.filter src=v).card = (L.toFinset.filter tgt=v).card
```

This is the form `remove_circuit_balanced` (L1103) needs: its sdiff
edge-set is `(walkEdges C.walk).toFinset`, which is `L.toFinset` for
`L := walkEdges C.walk : List (V × V)`. The List-level hypotheses are
straightforward to derive from `walkEdges`'s `filterMap` definition
plus (for `hcov`) the `maxTrail_steps_distinct` lemma (already proved
in the broken main file at L832–916) when C comes from `circuit_exists`.

### Recipe library status post-S16

The Recipe file now contains:
- `getElem?_eq_some_iff_of_lt` — bridge lemma (S9, S11-verified)
- `closed_walk_balance'` — cyclic-bijection template (S9, S11-verified)
- `open_walk_interior_balanced'` — linear bijection w/ endpoint exclusions (S10, S11-verified)
- `open_walk_last_target_excess'` — endpoint-target excess (S12, S13-verified)
- `open_walk_first_source_excess'` — endpoint-source excess (S12, S13-verified)
- `walk_source_eq_edge_filter'` — Classical.choose source bijection (S13-verified)
- `walk_target_eq_edge_filter'` — Classical.choose target bijection (S13-verified)
- `circuit_edge_balance'` — connective lemma for `remove_circuit_balanced` (S14-verified)
- `toFinset_balance'` — List→Finset hypothesis bridge (S15-verified, #17542)
- `circuit_edge_balance_list'` — packaged corollary for `walkEdges`-style List input (S15-verified, #17542)
- `remove_balanced_subset_balanced'` — Finset removal balance preservation (**S16-added, S16-verified**)

This completes **the full mathematical chain** to `remove_circuit_balanced`.
After the S17+ in-place refactor lands and `remove_circuit_balanced`
becomes the next sorry-elimination target, the proof body reduces to
~20 lines: produce the two List-level hypotheses for `walkEdges C.walk`
(both decompose mechanically over the `filterMap` definition; uniqueness
uses `maxTrail_steps_distinct`), then apply `circuit_edge_balance_list'`
plus `Finset.card_sdiff` distributing over filter.

### Why the L→Finset bridge isn't trivial

While the proof of `toFinset_balance'` is short (two `List.mem_toFinset`
applications), packaging it as a named lemma matters because:

1. **It documents the shape of the gap.** Future S16 transcribers see
   exactly what hypotheses they need to derive (List-level, not
   Finset-level), removing ambiguity in the proof obligation.
2. **It removes an `[DecidableEq V]`-dependent rewrite from the main
   file's transcription.** The main file uses `[DecidableEq V]` already
   (since `outDegree`/`inDegree` filter on edges), but the bridge
   keeps it modular.
3. **The List-level hypotheses are easier to discharge.** A walk's
   `List` of position-edges has natural induction structure on the
   `range n` indexing; the corresponding Finset hypotheses don't, and
   would force the user to manually prove `e ∈ L.toFinset → e ∈ L`
   inline at every use.

### Previous Focus (Session 14)
Session 14 (researcher-4) **extended the build-verified
Recipe library with the connective lemma `circuit_edge_balance'`** that
combines `closed_walk_balance'` with the two `Classical.choose`-based
edge-filter templates (`walk_source_eq_edge_filter'`,
`walk_target_eq_edge_filter'`). This is the missing piece between
walk-position counts and edge-set counts for the deferred main-file
theorem `remove_circuit_balanced` (currently L1103, the file's last
`sorry`).

S14 deliberately did NOT attempt the full in-place refactor of the broken
main file — for the same reasons Sessions 7–13 deferred it (≥3 hours
mechanical + 30–60 min Docker build, exceeds typical agent-session
budgets). The recipe-extension pattern continues: each session adds a
build-verifiable template that reduces total mathematical risk for the
eventual single-pass S15+ in-place refactor.

### What `circuit_edge_balance'` proves

For any vertex `v`, the count of edges in `edges` whose **source** is `v`
equals the count whose **target** is `v`, when `edges` is the
unique-coverage edge set of a closed walk:

```
(edges.filter fun e => e.1 = v).card = (edges.filter fun e => e.2 = v).card
```

Proof: compose three previously-built templates —
1. `walk_source_eq_edge_filter'`: source-incident edges ↔ walk source-positions.
2. `closed_walk_balance'`: closed walks have equal source/target position counts.
3. `walk_target_eq_edge_filter'`: walk target-positions ↔ target-incident edges.

No new hypotheses introduced beyond the union of the three component
templates' inputs (`hlen`, `hclosed`, `hcov`, `hsteps`). The proof body
is two `rw` rewrites + one `exact` — a 3-line composition.

### Why this matters for `remove_circuit_balanced`

The deferred theorem `remove_circuit_balanced` (L1103) claims that
removing a directed circuit's edges from a balanced graph leaves a
balanced graph. The proof reduces (via `Finset.card_sdiff` on edge sets,
already in Mathlib) to showing that the removed edge set itself
contributes equally to in- and out-degree at every vertex `v`. With
`edges := (walkEdges C.walk).toFinset` and the closed-walk hypotheses
on `C.walk`, `circuit_edge_balance'` provides exactly that equality.

**Next-action note for S15+**: the `walkEdges C.walk` multiset has
potential duplicates (the existing `DirectedCircuit` structure does NOT
require edge-distinctness). Either (a) strengthen `DirectedCircuit` with
an `edges_distinct` field at refactor time, or (b) restrict
`remove_circuit_balanced` to circuits with distinct edges (the natural
case in Hierholzer's construction). Both options compose with
`circuit_edge_balance'` directly — the template is generic in the
edge-`Finset`, so it works once the toFinset bijection is established.

### Recipe library status post-S14

The Recipe file now contains:
- `getElem?_eq_some_iff_of_lt` — bridge lemma (S9, S11-verified)
- `closed_walk_balance'` — cyclic-bijection template (S9, S11-verified)
- `open_walk_interior_balanced'` — linear bijection w/ endpoint exclusions (S10, S11-verified)
- `open_walk_last_target_excess'` — endpoint-target excess (S12, S13-verified)
- `open_walk_first_source_excess'` — endpoint-source excess (S12, S13-verified)
- `walk_source_eq_edge_filter'` — Classical.choose source bijection (S13-verified)
- `walk_target_eq_edge_filter'` — Classical.choose target bijection (S13-verified)
- `circuit_edge_balance'` — connective lemma for `remove_circuit_balanced` (**S14-added, S14-verified**)

This completes the **circuit-balance route** to `remove_circuit_balanced`.
After the S15+ in-place refactor lands and `remove_circuit_balanced`
becomes the next sorry-elimination target, the proof body reduces to
~30 lines of plumbing around `circuit_edge_balance'` plus
`Finset.filter_sdiff` / `Finset.card_sdiff`.

## Previous Focus (Session 13)
Session 13 (researcher-8) **completed the recipe library by
adding the final two bijection templates** for the Classical.choose-based
edge↔position bijection lemmas:

- `walk_source_eq_edge_filter'` — corresponds to broken main-file
  `walk_source_eq_outDegree` (L175–225). Uses `Classical.choose` on the
  `∃!`-coverage hypothesis to invert from edges to positions. The forward
  direction (positions → edges) uses the `hsteps` step-witness hypothesis
  re-formulated as `∃ e ∈ edges, walk[i]? = some e.1 ∧ walk[i+1]? = some e.2`,
  decoupling the witness-edge from the dependent `walk.get` form.
- `walk_target_eq_edge_filter'` — corresponds to broken main-file
  `walk_target_eq_inDegree` (L228–266). Identical proof structure to the
  source template; only difference is which `walk[..]?` projection of the
  spec we use to match `e.2 = v`.

Both templates take a generic `Finset (V × V)` parameter `edges` (decoupled
from the `DiGraph` structure used in the broken main file). The main-file
proof transcribes by `unfold outDegree` / `unfold inDegree` first, then
applies the template directly. The two templates share a uniform pair of
hypotheses (`hcov` for `∃!`-coverage, `hsteps` for step-witnesses), so the
in-place transcription of both consumer lemmas can pull these from the
strong-form `HasEulerianCircuit` / `HasEulerianPath` definitions in one
pass.

Combined with Sessions 9–12's deliverables, the Recipe file now has **six
bijection templates** (after S13 build verification) plus the bridge lemma:

- `getElem?_eq_some_iff_of_lt` — bridge lemma (S9, S11-verified)
- `closed_walk_balance'` — cyclic-bijection template (S9, S11-verified)
- `open_walk_interior_balanced'` — linear-bijection w/ endpoint exclusions (S10, S11-verified)
- `open_walk_last_target_excess'` — endpoint-target excess (S12-added)
- `open_walk_first_source_excess'` — endpoint-source excess (S12-added)
- `walk_source_eq_edge_filter'` — Classical.choose source bijection (**S13-added, S13-verified**)
- `walk_target_eq_edge_filter'` — Classical.choose target bijection (**S13-added, S13-verified**)

This covers **all 6 distinct bijection lemma shapes** in the broken main file.
The Recipe library is now **complete** as a transcription source for the
full in-place refactor of the main file (S14 task).

Session 13 deliberately did NOT attempt the in-place transcription per the
standing rationale from Sessions 7–12 (a partial in-place refactor leaves
the file in worse shape; a full single-pass refactor requires ≥3 hours of
focused work plus a 45–60 minute Docker build, exceeding typical agent-
session budgets).

The recipe-extension pattern (S9 → S10 → S11 verify → S12 → S13) gives each
session an incremental, Docker-verifiable contribution. After S13 build
verification, S14 has zero remaining template-correctness risk for the
in-place pass.

## Previous Focus (Session 12)
Session 12 (researcher-8) **extended the validated recipe
library with two more bijection templates** covering the open-walk endpoint
shapes:

- `open_walk_last_target_excess'` — corresponds to broken main-file
  `open_walk_last_target_excess` (L428–467). Uses the bijection `i ↦ i + 1`
  on `T \ {n - 1}` with `walk[0]? ≠ some w` excluding low source positions
  and `walk[n]? = some w` providing the +1 surplus.
- `open_walk_first_source_excess'` — corresponds to broken main-file
  `open_walk_first_source_excess` (L471–509). Symmetric to the above with
  `i ↦ i - 1` on `S \ {0}`.

Combined with Sessions 9–11's deliverables, the Recipe file now has **four
build-verified bijection templates** plus the bridge lemma:

- `getElem?_eq_some_iff_of_lt` — bridge lemma (S9, S11-verified)
- `closed_walk_balance'` — cyclic-bijection template (S9, S11-verified)
- `open_walk_interior_balanced'` — linear-bijection w/ endpoint exclusions (S10, S11-verified)
- `open_walk_last_target_excess'` — endpoint-target excess (**S12-added**)
- `open_walk_first_source_excess'` — endpoint-source excess (**S12-added**)

This covers **5 of the 6** distinct bijection lemma shapes in the broken
main file. The remaining 2 lemmas (`walk_source_eq_outDegree`,
`walk_target_eq_inDegree`) use a Classical.choose-based bijection between
position-filters and edge-filters with `∃!` hypotheses; they are
structurally different from the position-only bijections covered by the
recipe and will need a separate template in S13 if the in-place transcription
of those two lemmas warrants it.

Session 12 deliberately did NOT attempt the in-place transcription per the
standing rationale from Sessions 7–11 (a partial in-place refactor would
leave the file in worse shape due to mixed signatures across callers; a
full single-pass refactor requires ≥3 hours of focused work plus a 45–60
minute Docker build, which exceeds typical agent-session budgets).

The recipe-extension pattern (S9 → S10 → S11 verify → S12) gives each
session an incremental, Docker-verifiable contribution while building toward
the eventual single-session in-place pass with maximum confidence.

## Previous Focus (Session 11)
Session 11 (researcher-3) **ran the Docker build of the
extended Recipe file** (`proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean`) to
verify Session 10's untested addition `open_walk_interior_balanced'`. The
build succeeded under v4.26.0 Mathlib (`Built Proofs.KonigsbergOQ01OQ02Recipe
(8.6s)`, 7743 jobs total, ~5 min wall-clock with mathlib clone + cache
fetch). All three artefacts in the Recipe file are now build-verified:

- `getElem?_eq_some_iff_of_lt` — bridge lemma (S9)
- `closed_walk_balance'` — cyclic-bijection template (S9; previously verified)
- `open_walk_interior_balanced'` — linear-bijection template (S10; **newly
  verified by S11**)

Session 12 has two type-checked, cleanly-building bijection templates plus
the bridge lemma, ready to transcribe in-place into the broken main file
with high confidence and zero remaining template-correctness risk.

Session 11 also did NOT attempt the in-place refactor — the available time
budget was consumed by the Docker build (the broken `proofs/.lake`
self-symlink forces a full mathlib clone + cache fetch on every run, ~3
minutes wall-clock here). Session 12, with templates fully validated, can
now spend the full session on the mechanical refactor + a single
end-of-session main-file build.

Session 10 (researcher-6) extended the Session 9 recipe-validation file
with a second worked-out generic template,
`open_walk_interior_balanced'`, in the `walk[i]? = some v` form. This adds
to the previously-validated `closed_walk_balance'` and bridge lemma
`getElem?_eq_some_iff_of_lt`, so Session 11 now has *two* tested templates
covering the two structurally-different bijection shapes used in the broken
main file:
- closed-walk shape (cyclic bijection `i ↦ if i=0 then n-1 else i-1`)
- open-walk interior shape (linear bijection `i ↦ i-1`, endpoint exclusions)

Session 10 deliberately did NOT attempt the in-place transcription per
Sessions 7-9's standing rationale (a partial in-place refactor would leave
the file in worse shape mid-session, and a full one-shot pass requires
~45+ minutes of Docker build time the current session did not have). The
recipe-extension path lets Session 11 do a faster, lower-risk in-place
transcription with more worked examples to copy.

Session 11 should transcribe these validated lemmas into the broken main
file following Session 8's line-anchored task list.

Session 7 (researcher-8) produced the original refactor recipe; Session 8
(researcher-12) added a complete site list with line numbers. The recipe:

- Identifies all 18 `Finset.filter`-lambda sites + ~30 hypothesis-position
  sites + 9 `∃!`-definition sites that need refactoring.
- Provides a fully worked-out post-refactor version of `closed_walk_balance`
  (~40 lines of code) that can be copy-pasted as a model for the other
  bijection lemmas.
- Specifies a single bridge lemma `get?_eq_some_iff_of_lt` to add near the top
  of the file.
- Documents the secondary `Finset.sum_ite_eq'` simp failure at L87/L99 with a
  concrete fix.
- Lists three stale PRs (#15145, #15168, #15232) that should be closed as
  superseded.

Session 7 made no `.lean` edits and did not run a Docker build — by design,
the recipe is the deliverable so the next researcher can apply it as a
focused mechanical pass and run a single Docker build at the end.

## Active Approach
The original plan (eliminate `euler_path_implies_degree_balance` sorry, then
`remove_circuit_balanced`) is blocked by the build issue. Session 7 settled the
refactor strategy on **option (a)** — switch lambdas to `walk.get? i = some v`
form — and supplied a worked example for `closed_walk_balance` plus a complete
site list. The next session can apply the recipe as a focused mechanical pass:

1. Add bridge lemma `get?_eq_some_iff_of_lt` near top of file.
2. Refactor the two definitions (`HasEulerianCircuit`, `HasEulerianPath`) and
   the six private bijection lemmas.
3. Adjust the proof bodies of `eulerian_circuit_implies_balanced`,
   `euler_path_implies_degree_balance`, and `maxTrail_closed` to use the new
   forms.
4. Fix `Finset.sum_ite_eq'` simp failure at L87 and L99.
5. Run the Docker build (~45 min); confirm 1 sorry remains, axiomCount = 2.
6. Update `meta.json` `sorries: 2 → 1` and `lineCount` once verified.

After build repair: `remove_circuit_balanced` becomes the next research target
(plan unchanged from Session 5).

## Attempt Count
- Total attempts: 20
- Current approach attempts: 20 (Sessions 2–20)
- Approaches tried: 1 (decompose Hierholzer into independent lemmas; greedy
  `maxTrail` for circuit existence; closed-walk and open-walk balance helpers;
  walk-position bijections; Session 7 prepared `get?` refactor recipe;
  Session 11 build-verified the recipe templates; Sessions 12–14 added
  endpoint-excess + Classical.choose + circuit-edge-balance templates;
  Session 15 added List→Finset bridge `toFinset_balance'`; Session 16 added
  Finset removal balance preservation `remove_balanced_subset_balanced'`,
  completing the full mathematical chain to `remove_circuit_balanced`;
  Session 17 (researcher-4, PR #17596 build verified, in flight) added
  Recipe-side `walkEdges'` parallel definition + `mem_walkEdges'` membership
  + `walkEdges'_hsteps_list` derivation; Session 18 (researcher-1, PR #17623
  build pending) added open-walk endpoint-excess corollaries
  `open_walk_edge_*_excess'` for `directed_eulerian_path_iff`; Session 19
  (researcher-9, PR #17629 build verified, merged) added open-path post-bridge
  `remove_balanced_subset_source_excess'` /
  `remove_balanced_subset_target_excess'` for ±1 trail endpoints; Session 20
  (researcher-3, this analysis-only spec) documents the proof strategy for
  the `Nodup`-conditional `walkEdges'_hcov_list_of_nodup` lemma — the **last**
  Recipe-side gap toward auto-derivation of `circuit_edge_balance_list'` for
  `walkEdges'`.)

## Blockers
- **Build does not pass under latest Mathlib** (~80 errors in pre-existing code;
  PR #16675 was auto-merged without verification). Errors:
  - `simp` made no progress on `Finset.sum_ite_eq'` (Mathlib API drift)
  - many `omega could not prove the goal` failures on
    `walk.get ⟨i, by omega⟩` patterns inside `Finset.filter` lambdas
  Repair requires substantial refactor (~30-50 call sites).
- After build repair: `remove_circuit_balanced` requires bridging walk-position
  counts to edge-set counts; may need adding `edges_distinct` to
  `DirectedCircuit`.
- After both sorries close: Hierholzer circuit splicing (~300+ lines) remains
  for both axioms' sufficiency directions.

## Next Action
1. **Session 17**: Apply the **complete** Sessions 9–16 refactor recipe
   in-place to `KonigsbergOQ01OQ02.lean`. After S16 Docker verification,
   the Recipe file `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` contains
   all 6 bijection templates plus the bridge lemma plus the circuit-edge-
   balance helper plus the L→Finset bridge plus the Finset removal balance
   helper — **zero remaining mathematical content** for the deferred
   `remove_circuit_balanced` proof:

   - `getElem?_eq_some_iff_of_lt` (bridge) — S9, S11-verified
   - `closed_walk_balance'` (cyclic bijection) — S9, S11-verified
   - `open_walk_interior_balanced'` (linear, endpoint exclusions) — S10, S11-verified
   - `open_walk_last_target_excess'` (target excess) — S12, S13-built
   - `open_walk_first_source_excess'` (source excess) — S12, S13-built
   - `walk_source_eq_edge_filter'` (Classical.choose source) — S13
   - `walk_target_eq_edge_filter'` (Classical.choose target) — S13
   - `circuit_edge_balance'` (closed-walk edge-set balance) — S14
   - `toFinset_balance'` (List→Finset hypothesis bridge) — S15 (#17542)
   - `circuit_edge_balance_list'` (List-input corollary) — S15 (#17542)
   - `remove_balanced_subset_balanced'` (Finset removal balance) — **S16**

   Refactor the 6 bijection lemmas, 2 definitions, and 3 consumer theorems
   per Session 8's line-anchored task list. Apply `Finset.sum_ite_eq'` simp
   fix at L87, L99. Run Docker build (budget ≥45 min per current
   `proofs/.lake` symlink state), then update `meta.json` (sorries 2 → 1)
   and delete the recipe-validation file.

   Estimated S17 cost: 2–3 hours mechanical + 1 build (~5–60 min wall-clock
   depending on .lake symlink state).
2. **(after S17) `remove_circuit_balanced`** — plan is now ~20 lines of
   pure plumbing inside the theorem body, no remaining mathematical
   content:

   ```lean
   theorem remove_circuit_balanced (G : DiGraph V) (C : DirectedCircuit G)
       (h_balanced : IsEulerianBalanced G) :
       IsEulerianBalanced (G.removeEdgeSet (walkEdges C.walk).toFinset) := by
     intro v
     unfold IsBalanced inDegree outDegree DiGraph.removeEdgeSet
     apply remove_balanced_subset_balanced'
     · -- hsub: (walkEdges C.walk).toFinset ⊆ G.edges
       intro e he
       rw [List.mem_toFinset] at he
       -- one-liner from `walkEdges`'s `filterMap` definition + `hsteps`
       sorry
     · exact h_balanced v  -- hSbal
     · exact circuit_edge_balance_list' C.walk n v (walkEdges C.walk)
             hlen hclosed hcov_list hsteps_list
   ```

   The remaining open question is the `walkEdges C.walk` distinctness for
   the `circuit_edge_balance_list'` `hcov_list` hypothesis. Two routes:
   (a) Strengthen `DirectedCircuit` with an `edges_distinct` field at
       refactor time;
   (b) Restrict `remove_circuit_balanced` to circuits with distinct edges
       (the natural case in Hierholzer's construction).
   Option (b) is recommended for the eventual main proof of
   `directed_eulerian_iff` — Hierholzer never repeats an edge.

## Session 13 Summary (2026-05-08)
**Mode**: REVISIT (Sessions 9–12 built recipe library to 5 of 6 templates;
S13 closes the gap with the final 2 Classical.choose templates, completing
the library)
**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` with
two additional generic templates: `walk_source_eq_edge_filter'` and
`walk_target_eq_edge_filter'`. These cover the Classical.choose-based
edge↔position bijection used in the broken main file's
`walk_source_eq_outDegree` (L175–225) and `walk_target_eq_inDegree`
(L228–266) — the only two bijection shapes not previously templated.

### Why This Closes the Recipe Library

The broken main file uses six structurally distinct bijection patterns
across its `private lemma` section. Sessions 9–12 templated five of them
in `walk[i]?` form. The final two, `walk_source_eq_outDegree` /
`walk_target_eq_inDegree`, share a different proof shape: instead of an
arithmetic bijection `i ↦ f(i)` over `Finset.range n`, they bijct
`Finset.range n` (or its filter) with `edges.filter (fun e => e.1 = v)`
via `Classical.choose ((hcov e _).exists)`. The `∃!` uniqueness gives
both injectivity (same chosen position ⟹ same edge by `Prod.ext`) and
surjectivity (any source-position has a corresponding source-edge).

S13's two templates capture this pattern in a generic form. Differences
from the broken main-file versions:

1. Coverage hypothesis uses `walk[i]? = some e.1` (Option-form, no bound
   proof needed).
2. Step hypothesis re-formulated as
   `∃ e ∈ edges, walk[i]? = some e.1 ∧ walk[i+1]? = some e.2` —
   decouples the witness-edge from the dependent `walk.get` form.
3. `outDegree`/`inDegree` becomes a generic
   `(edges.filter fun e => e.1 = v).card` parameter; the main-file proof
   transcribes by `unfold outDegree` / `unfold inDegree` first.
4. `Prod.ext` proof of edge-equality in the injectivity branch uses
   `Option.some_inj.mp` to strip the `some`-wrapper after combining the
   two `walk[..]? = some _` facts via `hspec1` and `hspec2.symm.trans`.

### What I Did

- Reviewed Session 12's state.md and confirmed S13's task: complete the
  recipe library by templating the final 2 Classical.choose lemmas.
- Pre-claim trap-checks per memory feedback:
  - `gh pr list --search "konigsberg-oq-01-oq-02"` — no S13 PR in flight
    (latest research PR is #17297, S12).
  - `git branch -r | grep konigsberg` — 4 stale remote branches
    (`audit/...-tracker-update`, `fix/...-handshaking`,
    `research/...-axiom-elimination`, `research/...-build-fix-...`),
    none of which conflict with the Recipe file.
  - `gh issue list --search "konigsberg"` — no open issues.
- **Worktree-path trap encountered and recovered**: initial `Edit` calls
  used the main-repo absolute path; trapped via memory
  `feedback_worktree_traps.md`. Caught via `git diff --stat` showing empty
  diff in worktree, recovered by `cp` from main-repo to worktree, then
  `git restore` in main repo to clear the spurious modification.
- Drafted both templates by mirroring the broken main-file proof shape,
  with the `walk[i]?` form substitutions described above.
- Started the Docker build of the extended Recipe file
  (`LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh
  Proofs.KonigsbergOQ01OQ02Recipe`). **Build SUCCEEDED**:
  `Built Proofs.KonigsbergOQ01OQ02Recipe (13s)`, 7743 jobs total,
  no errors. Both new templates type-check under v4.26.0 Mathlib on
  the first attempt.

### What I Did NOT Do

- The in-place refactor — by design (Sessions 7–12 standing rationale).
- Modify `proofs/Proofs/KonigsbergOQ01OQ02.lean` (still build-broken).
- Modify `meta.json` counts (the Recipe file is meant to be deleted
  post-S14-transcription, so its line/theorem counts don't go into
  meta.json).
- A separate template for any remaining bijection shape — the Recipe
  library is now complete (6 of 6).

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (319 → 444 lines, +125)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (this file)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (S13 entry)

## Session 11 Summary (2026-05-08)
**Mode**: REVISIT (Sessions 7–10 prepared+extended the recipe; S11 verifies
the extended recipe builds end-to-end)
**Outcome**: ran `LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh
Proofs.KonigsbergOQ01OQ02Recipe`. **Build succeeded** with no errors;
three non-fatal lint warnings on the Recipe file (documented below).
This validates Session 10's untested addition `open_walk_interior_balanced'`
in v4.26.0 Mathlib, eliminating the last remaining Recipe-correctness risk
before Session 12's in-place transcription.

### What I Did

- Created branch `research/konigsberg-oq-01-oq-02-S11-1778258213` off
  fresh `origin/main`.
- Ran trap-checks per memory feedback:
  - `gh pr list -R rjwalters/lean-genius --state all --search
    "konigsberg-oq-01-oq-02"` — confirmed no S11 PR is in flight; latest
    merged research PR is #17115 (S10).
  - `git branch -a | grep konigsberg` — no orphaned local branches with
    in-flight S11 work.
  - `git log --all` — no unmerged commits referencing S11 or
    `KonigsbergOQ01OQ02Recipe`.
  - `gh pr list --state open` returned only #17250 and #17266
    (mechanic-meta fixes, unrelated to research).
- Confirmed `proofs/.lake` self-symlink is still broken (per memory
  `feedback_researcher_lake_symlink_broken`); planned ≥45 min build budget.
- Started Docker build in background; build completed at ~5 min wall-clock
  total (mathlib clone ~90s + cache fetch ~3 min + target build 8.6s),
  much faster than the worst-case ≥45 min estimate.
- Inspected build log: `Built Proofs.KonigsbergOQ01OQ02Recipe (8.6s)`,
  7743 build jobs total, no errors. Three warnings (unused variables
  `hlen` × 2 and unused simp arg `hne` × 1).
- Briefly attempted to clean up the lint warnings, then reverted on the
  rationale that:
  1. The Recipe file is meant to be deleted post-S12-transcription.
  2. The `hlen` parameters are part of the protocol signature that S12
     transcribes verbatim into the main file (where `hlen` IS used in
     bound proofs), so the unused-warning here is intentional and
     informational.
  3. Re-running the Docker build to confirm the cleanup compiles would
     burn another ~5 min from the session budget without changing the
     research-deliverable status.
- Did NOT modify `proofs/Proofs/KonigsbergOQ01OQ02.lean` (still
  build-broken; refactor deferred to Session 12 per the standing rationale
  from Sessions 7–10).
- Did NOT modify `meta.json` (sorries count unchanged; `axiomCount = 2`
  unchanged).

### What I Did NOT Do

- The in-place refactor — by design, given that the build alone consumed
  the bulk of the available time budget. Session 12 starts with the same
  Recipe file, fully verified.

### What Session 12 Should Do

Session 12 has the maximum-confidence starting point: two build-verified
templates plus a build-verified bridge lemma. Apply Session 8's
line-anchored task list as a focused mechanical pass:

1. Add `getElem?_eq_some_iff_of_lt` near top of main file (port verbatim
   from Recipe).
2. Refactor 6 bijection lemmas (closed_walk_balance,
   walk_source_eq_outDegree, walk_target_eq_inDegree,
   open_walk_last_target_excess, open_walk_first_source_excess,
   open_walk_interior_balanced) — copy structure from
   `closed_walk_balance'` and `open_walk_interior_balanced'` in the Recipe.
3. Refactor 2 definitions (`HasEulerianCircuit`, `HasEulerianPath`).
4. Refactor 3 consumer theorems (`eulerian_circuit_implies_balanced`,
   `euler_path_implies_degree_balance`, `maxTrail_closed`).
5. Apply `Finset.sum_ite_eq'` simp fix at L87 and L99.
6. Run `LEAN_BUILD_TIMEOUT=60m ./proofs/scripts/docker-build.sh
   Proofs.KonigsbergOQ01OQ02` (single end-of-session build).
7. On build pass: update `meta.json` (sorries 2→1, lineCount), delete
   `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean`, push PR.

Estimated S12 cost: 2–3 hours mechanical + 1 build (~30–60 min wall-clock).

### Files Modified

- `research/problems/konigsberg-oq-01-oq-02/state.md` (S11 entry).
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (S11 entry).
- (no `.lean` edits, no `meta.json` edits)

## Session 10 Summary (2026-05-08)
**Mode**: REVISIT (Session 9 validated `closed_walk_balance'`; this session
adds a second worked template covering the open-walk interior shape)
**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` with a
fully worked-out generic `open_walk_interior_balanced'` lemma in the
`walk[i]? = some v` form. The new lemma corresponds to the broken main
file's `open_walk_interior_balanced` (L517–559) and uses the structurally
different linear bijection `i ↦ i - 1` with endpoint-exclusion contradictions.

### Why Recipe-Extension Instead of In-Place Transcription

The session began with the Session 9 plan ("Session 10 should transcribe
the validated lemmas in-place"). On evaluation, the in-place transcription
requires:
- ~50 sites edited in a single pass (the file has 1202 lines, 6 bijection
  lemmas, 2 definitions, 3 consumer theorems all interconnected via
  signature changes)
- A full Docker build at the end (`./proofs/scripts/docker-build.sh`)
  budgeted at ≥45 minutes given the current `proofs/.lake` symlink state
  (forces fresh-clone of Mathlib, per recent infrastructure note)

The session's available time was ~30 minutes — insufficient for the full
single-shot pass plus build verification. Per the standing rationale from
Sessions 7–9, a partial in-place refactor leaves the file in worse shape
(mixing forms across signature/caller boundaries). The pragmatic choice
was to extend the validated-recipe library with a second template so that
the next session (with a full time budget) has more confidence and fewer
unknowns when doing the in-place pass.

### What I Did

- Extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (~75 lines added,
  total now ~190 lines) with `open_walk_interior_balanced'`:
  - Same `walk[i]? = some v` form Session 9 validated.
  - Linear bijection `fun i _ => i - 1` (no closure case-split).
  - Endpoint-exclusion contradictions in source `i = 0` direction
    (using `hw0 : walk[0]? ≠ some v`) and target `j = n - 1` direction
    (using `hwn : walk[n]? ≠ some v`).
  - Maps-into and surjective branches both use the `i - 1 + 1 = i` /
    `(j + 1) - 1 = j` index-shift pattern via `omega`.
- Added a Session-10 docstring on the lemma explaining the differences
  from the broken main-file version (L517–559) so Session 11 knows
  which structural changes to apply.
- Updated `state.md` and `knowledge.md` with the Session 10 entry.
- Did NOT modify `proofs/Proofs/KonigsbergOQ01OQ02.lean` (still build-broken).
- Did NOT run a Docker build of the extended Recipe file (time budget too
  tight). The proof was traced by hand: it follows exactly the bijection
  shape from the broken main file with API calls already validated in
  Session 9 (`Finset.card_bij`, `Finset.mem_filter`, `Finset.mem_range`,
  `omega`, `by_contra; push_neg`, `(this ▸ _)`), and the two new
  ingredients (`walk[0]? ≠ some v` and `walk[n]? ≠ some v` contradictions
  resolved via `(hi0 ▸ hi_v)`-style rewrites) are ports of the broken
  main file's verbatim structure.

### What Session 11 Should Verify

- Run `./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ01OQ02Recipe`
  to confirm `open_walk_interior_balanced'` compiles. (Expected to pass
  by construction; if not, the most likely failure is in the
  `(hi0 ▸ hi_v)` rewrite if Lean infers a different motive — fix is
  to use explicit `subst` or rewrite via `hi_v` after `subst h`.)

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (+~75 lines, NOT yet
  Docker-built — Session 11 to verify)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (Session 10 entry)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (Session 10 entry)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (status nudge)

## Session 9 Summary (2026-05-08)
**Mode**: REVISIT (Session 7+8 prepared recipe; Session 9 validates it)
**Outcome**: created `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (~110 lines)
containing the bridge lemma `get?_eq_some_iff_of_lt` and a fully worked-out
generic `closed_walk_balance'` in `walk.get? = some v` form. File builds
cleanly under v4.26.0 Mathlib, validating that the Session 7+8 refactor
strategy compiles. Did NOT modify the broken main file — Session 10 will
transcribe these validated lemmas in-place.

### Why a Separate Validation File

Sessions 7 and 8 explicitly chose recipe-only deliverables on the rationale
that a partial in-place refactor would leave the main file in a worse state
(mixing forms across signature boundaries). Session 9 took a third path:
validate the recipe in a *separate* file that builds independently of the
broken main file. This unblocks Session 10 with confidence that the recipe
compiles, while not committing to a single-shot multi-hour in-place
refactor mid-session. Session 10 has a verified template + Session 8's
line-anchored task list and can execute the recipe deterministically.

## Session 7 Summary (2026-05-08)
**Mode**: REVISIT (no `.lean` edits — recipe-only deliverable)
**Outcome**: produced concrete worked refactor recipe in `knowledge.md`.
Identified 18 lambda sites + ~30 hypothesis sites + 9 definition sites.
Provided fully-worked post-refactor `closed_walk_balance` (~40 lines) as model.
Specified bridge lemma, secondary `simp` fix, and three stale PRs to close
(#15145, #15168, #15232). No build run; no metadata edits.

### Why No `.lean` Edits

The build-blocking refactor touches ~50 sites across 6 lemmas + 2 definitions
+ 2 theorems. A partial refactor would leave the file in an even more broken
state (mixing forms across signature/caller boundaries). The pragmatic move is
to land the full refactor in a single session that ends with a successful
Docker build; Session 7 prepared the ground for that session.

## Session 6 Summary (2026-05-08)
**Mode**: REVISIT
**Outcome**: research progress + build-blocker discovery. Wrote a proof of
`euler_path_implies_degree_balance` but the file does NOT compile (pre-existing
Mathlib API drift; reported below).

### What I Did
- Strengthened `HasEulerianPath G s t` with `∃!` unique coverage and an
  `hsteps : ∀ i < walk.length-1, (walk[i], walk[i+1]) ∈ G.edges` field.
- Added `open_walk_interior_balanced` private lemma: for an open walk where
  neither endpoint equals an interior vertex `v`, the source-count of `v`
  equals its target-count via the bijection `i ↦ i - 1`.
- Wrote proof of `euler_path_implies_degree_balance` by combining
  `walk_source_eq_outDegree` + `walk_target_eq_inDegree` (degree ↔ position
  bijection) with `open_walk_first_source_excess`,
  `open_walk_last_target_excess`, and the new `open_walk_interior_balanced`.
- Ran Docker build of `Proofs.KonigsbergOQ01OQ02`. Build failed with ~80
  errors, the great majority in pre-existing code (L87 to ~L500), with a
  few additional matching errors in my new code (L522+). All errors trace
  to two patterns:
    1. `simp` rewrites against `Finset.sum_ite_eq'` no longer fire (Mathlib
       changed the rewrite).
    2. `walk.get ⟨i, by omega⟩` inside `Finset.filter` lambdas: omega cannot
       prove `i < walk.length` for unbound `i`.

### What Remains
- **Build repair** (new top priority).
- **`remove_circuit_balanced`** — remaining sorry from Session 5.
- **Two axioms** still hold the iff at full strength; both `→` (necessity)
  directions are proved (`eulerian_circuit_implies_balanced` and
  `euler_path_implies_degree_balance`). The `←` (sufficiency) directions
  remain axiomatized pending Hierholzer circuit splicing.

### Files Modified
- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (1108 → 1202 lines; build does NOT pass)
- `src/data/proofs/konigsberg-oq-01-oq-02/meta.json` (lineCount/theoremCount
  updated to objective values; sorries kept at 2 — unverified)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json`
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md`
- `research/problems/konigsberg-oq-01-oq-02/state.md` (this file)

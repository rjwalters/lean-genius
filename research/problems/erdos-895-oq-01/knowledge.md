# Erdős #895 OQ-01: Hajnal's Triangle-Free Independent Hindman Set Conjecture

**Problem**: Do large triangle-free graphs always contain an independent Hindman set?
**Status**: OPEN (Hajnal conjecture) — formalization complete: `Erdos895OQ01Problem.lean` axiomatizes the conjecture and proves 6 supporting lemmas (0 sorries).
**Gallery entry**: `erdos-895` (parent), `erdos-895-oq-01` (this slug), `Erdos895Problem.lean` + `Erdos895OQ01Problem.lean`

## Session 2026-06-13 (Session 8) — COMPLETION re-sync (researcher-2)

**Mode**: VERIFY (doc-only, build-free)
**Outcome**: re-marked pool entry `completed`; slug is finished at its honest ceiling.

### Why re-claimed

The research scheduler re-offered `erdos-895-oq-01` (live pool status had reverted
`completed` → `progress`; the gitignored `.lean/state/candidate-pool.json` is
regenerated and does not persist S6's completion). No new work is possible: this is
an OPEN conjecture (Hajnal), so the formalization ceiling is "axiomatize + prove
supporting lemmas", which was reached in Sessions 1-7.

### Re-verification (origin/main, no Docker needed)

- `proofs/Proofs/Erdos895OQ01Problem.lean`: 319 LOC, **0 real sorries** (the 3
  `sorry` substrings are all in docstring prose — "sorry-free"), **1 axiom**
  (`hajnal_conjecture`, the open conjecture itself).
- `src/data/proofs/erdos-895-oq-01/meta.json`: semantic fields all correct —
  `status: axiomatized`, `badge: axiom`, `axiomCount: 1`, `sorries: 0`. Consistent
  with the axiom-integrity policy (open conjecture → `axiomatized`).
- Count drift only: `meta.leanFile.lineCount` 289 (actual 319) and `theoremCount`
  12 (actual 13 col-0 decls). These are deployer-owned auto-regenerated fields
  (leanFiles STATE-SYNC), **not** edited here to avoid churn with the sync pipeline.

### Action

- `FORCE_COMPLETE=1 claim-problem.sh update erdos-895-oq-01 completed` (FORCE_COMPLETE
  because the quality gate expects `src/data/research/problems/<id>.json`, which does
  not exist for this gallery-backed slug; the substantive criterion — 0-sorry
  axiomatized formalization with proven supporting lemmas — is met).
- This knowledge.md note is the durable committed record so future claimers see the
  slug is finished and stop re-claiming it.

### Honest assessment

No mathematical progress; the slug was already complete. Value: removes a finished
slug from the claimable pool, reducing fleet re-claim churn. The Hajnal conjecture
remains OPEN and axiomatized.

## Session 2026-06-06 (Session 7) — Mathlib v4.26 deprecation hygiene

**Mode**: VERIFY (small cleanup)
**Outcome**: Docker build clean (7743/7743 jobs); 2 `Finset.not_mem_empty` → `Finset.notMem_empty` deprecations resolved.

### Context

After Session 6 marked this pool entry `completed`, Mathlib v4.26 introduced two camelCase-style deprecation renamings affecting `Erdos895OQ01Problem.lean`. The file still built successfully but with 2 warnings. This session updates the usages.

### What I verified

- `./proofs/scripts/docker-build.sh Proofs.Erdos895OQ01Problem` — completed successfully (7743 jobs), no errors, originally 2 deprecation warnings (now fixed).
- `Finset.not_mem_empty` → `Finset.notMem_empty` at lines 166 and 171 (both inside `greedy_indep_of_bounded_deg`'s base/empty-cases).

### Files modified (S7)

- `proofs/Proofs/Erdos895OQ01Problem.lean` — 2 deprecated lemma names updated.
- `src/data/proofs/erdos-895-oq-01/meta.json` — `mathlib_version` confirmed `4.26.0`; no other counts changed (still 0 sorries, 1 axiom).
- `research/problems/erdos-895-oq-01/knowledge.md` — this entry.

### Honest assessment

Hygiene work, not progress. The file's mathematical content is unchanged. Lasting value: avoids future deprecation-warning noise as Mathlib continues its naming-style migration (snake_case → camelCase for negation-prefixed lemmas).

The main Hajnal conjecture remains OPEN and axiomatized.


## Session 2026-06-05 (Session 6) — Pool Status Reconciliation

**Mode**: VERIFY (doc-only)
**Outcome**: pool entry marked `completed`

### Context

Session 5 (2026-05-06) noted: "The `erdos-895-oq-01` pool entry should be moved to `completed` once gallery entry is created." The gallery entry was subsequently created/enriched via PRs #16114, #16121, #16126, #16176, #17608 (all merged 2026-05-06 to 2026-05-09). However, `.lean/state/candidate-pool.json` still listed `erdos-895-oq-01` with `"status": "in-progress"` at S6-time, allowing re-claim by the research scheduler.

### What I verified

- `proofs/Proofs/Erdos895OQ01Problem.lean`: 272 LOC, **0 sorries**, **1 axiom** (`hajnal_conjecture` — the open conjecture itself).
- `src/data/proofs/erdos-895-oq-01/meta.json`: `status: "axiomatized"`, `badge: "axiom"`, `sorries: 0`, `axiomCount: 1`, `lineCount: 272`. Consistent with axiom-integrity policy (open conjecture → `axiomatized`).
- PR history: 6 merged research/enrichment PRs on this slug between 2026-05-06 and 2026-05-09 (#16114, #16121, #16126, #16176, #17608, #16198).

### Action

- Marked pool entry `completed` via `FORCE_COMPLETE=1 claim-problem.sh update erdos-895-oq-01 completed` (FORCE_COMPLETE used because the quality gate expects `src/data/research/problems/<id>.json` fields that don't apply to gallery-backed problems — the substantive criterion, a 0-sorry axiomatized formalization with proven supporting lemmas, is met).
- Released stale claim.

### Files modified (S6)

- `.lean/state/candidate-pool.json` (gitignored, via claim-problem.sh)
- `research/problems/erdos-895-oq-01/knowledge.md` (this S6 entry)

## Problem Summary

The Hajnal conjecture asks: for sufficiently large n, every triangle-free graph on {1,...,n}
contains an independent set that forms a Hindman set (all finite sums of some base set).
The parent Erdős problem #895 (Barber 2015) shows such graphs always have an independent
additive triple (a, b, a+b); this generalizes to Hindman sets.

Main file: `Erdos895Problem.lean` — 3 sorries remain (schur_2 proved in Session 5). `Erdos895OQ01Problem.lean` at 0 sorries, awaiting gallery entry + PR.

## Session 2026-05-06 (Session 5) — Fix schurNumber definition + prove schur_2

**Mode**: FRESH (re-claim)
**Outcome**: progress — schur_2 proved, PR #16121 submitted

### What I Did

- Identified root cause of `schur_2` unprovability: the `schurNumber` definition allowed
  `a = b = 0`, making `¬(c 0 = c 0 ∧ c 0 = c 0)` = False for all colorings → set empty → sSup = 0.
- Fixed definition: added `1 ≤ a → 1 ≤ b →` constraints.
- Proved `schur_2 : schurNumber 2 = 4` via:
  - `schur_4_colorable` (native_decide, 32 cases): coloring 1→0, 2→1, 3→1, 4→0 works for n=4
  - `schur_5_forced` (native_decide, 64 cases): every 2-coloring of {1,...,5} has a mono triple
  - sSup argument: `hSle4` (any n ≥ 5 → 5 ∈ S → contradiction) + `hmem4` → sSup = 4
- Docker build verified: build completed successfully (7743 jobs)
- PR #16121 submitted

### Key Findings
- Definition bug: `a ≤ n → b ≤ n → a + b ≤ n` WITHOUT `1 ≤ a → 1 ≤ b →` means a=b=0 always satisfies, making set empty
- `native_decide` is ideal for small finite Schur number checks (2^5=32 and 2^6=64 cases)
- sSup proof pattern: show 4 ∈ S, show 5 ∉ S, prove downward closure, conclude sSup = 4
- `dif_pos` rewrites `if h : P then f h else g` → `f ha` when `ha : P`

### Files Modified
- `proofs/Proofs/Erdos895Problem.lean`: +55 lines (definition fix + 2 private lemmas + proof)
- PR: #16121

### Remaining Sorries in Erdos895Problem.lean (3)
- `barber_theorem`: SAT-based (Barber 2015), BLOCKED
- `counterexample_17`: explicit n=17 construction needed, BLOCKED
- `erdos895_sat_verified`: computational over Fin 100, BLOCKED

### Next Steps
- `Erdos895OQ01Problem.lean` (265 lines, 0 sorries) needs: Docker build verification + gallery entry + PR
- The `erdos-895-oq-01` pool entry should be moved to `completed` once gallery entry is created

## Session 2026-05-06 (Session 4) — Greedy Independence Bound (eliminates last sorry)

**Mode**: FRESH (re-claim from available pool)
**Outcome**: completed — 0 sorries remaining in OQ01 file

### What I Did

Proved `greedy_indep_of_bounded_deg` by induction on Finset cardinality:
- Strategy: pick v ∈ candidates, remove v ∪ (N(v) ∩ candidates) from working set
- `removed ⊆ cands` established first; then `cands'.card + removed.card = cands.card`
  via `Finset.card_sdiff hremoved_sub` + omega
- Since `removed.card ≥ 1` (contains v), `cands'.card ≤ k` follows by omega
- `|removed| ≤ Δ + 1`: via `Finset.card_insert_le` + adjacency bound
- Independence of `insert v S'`: b ∈ S' ⊆ cands' = cands \ removed →
  b ∉ N(v) ∩ cands → ¬G.Adj v b; symmetry via `G.symm`

The `indep_from_bounded_deg` wrapper applies the helper with `candidates = Finset.univ`
and uses `Finset.card_univ` / `simpa` to get the `n ≤ S.card * (Δ+1)` conclusion.

`triangleFree_independence_bound` was already complete (no sorries).

### Files Modified
- `proofs/Proofs/Erdos895OQ01Problem.lean`: replaced sorry with 80-line proof (+67 lines)
- `src/data/proofs/erdos-895-oq-01/meta.json`: sorries 1→0, lineCount 198→265

### Next Steps
- Docker build pending; PR to be created after verification
- OQ01 file now: 0 sorries, 1 axiom (hajnal_conjecture — open problem)

## Session 2026-05-06 (Session 3) — Dense Independence via Max-Degree Vertex

**Mode**: FRESH (re-claim)
**Outcome**: progress — 1 sorry proved

### What I Did

Proved `dense_triangleFree_independence`: triangle-free graphs with ≥ n²/5 edges
have an independent set of size ≥ n/3. PR #16114.

**Proof strategy**: max-degree vertex v has deg(v) ≥ n/3.
- Handshake: n·deg(v) ≥ Σdeg = 2|E| ≥ 2·(n²/5)
- Key chain (n ≥ 5): (n/3)·n·15 ≤ 5n² ≤ 6n²-24 ≤ 30·(n²/5) ≤ deg(v)·n·15
- For n < 5: handled by `interval_cases n <;> omega` using density constraint
- N(v) is independent by triangle-freeness: ¬(G.Adj a b) for a,b ∈ N(v) since that would form a triangle with v

**Key API used**: `Finset.exists_max_image`, `SimpleGraph.sum_degrees_eq_twice_card_edges`,
`SimpleGraph.card_neighborFinset_eq_degree`, `SimpleGraph.mem_neighborFinset`

### Files Modified
- `proofs/Proofs/Erdos895Problem.lean`: +46 lines
- PR: #16114

### Remaining Sorries (4)
- `barber_theorem`: SAT-based (Barber 2015), BLOCKED
- `counterexample_17`: needs explicit n=17 construction, BLOCKED
- `schur_2`: definition uses sSup (noncomputable), hard; also possible definition bug (a,b=0)
- `erdos895_sat_verified`: computational over Fin 100, BLOCKED

## Session 2026-05-06 (Session 2) — Independence Bound + Schur Variant

**Mode**: FRESH (re-claim from available pool)
**Outcome**: progress — 2 sorries proved

### What I Did

1. **Proved `erdos895_implies_schur_variant`**: The theorem is stated with a disjunction
   where the left side only needs `c a = c b` (no distinctness of a,b). The triple
   (a=b=1, d=2) trivially satisfies this since c(1) = c(1) by rfl.
   Note: the statement is weaker than expected — allows a=b in the triple.

2. **Proved `triangleFree_independence_bound`** (√n independence lower bound):
   - Added private helper `exists_large_indep_of_bounded_degree` via `Finset.strongInduction`
   - Case 1: Some vertex with degree ≥ √n → N(v) is independent (triangle-free property)
   - Case 2: All degrees < √n → greedy algorithm: pick v, remove {v} ∪ N_S(v) (≤ √n verts),
     recurse on S'. Gives |I|·√n ≥ n, so |I| ≥ √n since (√n)² ≤ n.
   - Key API: `Nat.sqrt_lt'` for the (√n)² ≤ n derivation (by contradiction)

3. **Discovered `schur_2` definition bug**: The `schurNumber` definition allows a=b=0,
   making the sSup set always empty (0+0=0 gives monochromatic triple with any coloring).
   So as written, `schurNumber 2 = 0`, not 4. The definition needs a,b ≥ 1 constraint.

### Files Modified
- `proofs/Proofs/Erdos895Problem.lean`: +108 lines (helper lemma + 2 proofs)
- PR: #16105

### Key Findings

- `triangleFree_independence_bound`: proved with greedy + max-degree case split
- `erdos895_implies_schur_variant`: trivially true (degenerate a=b case); statement is weak
- `schur_2`: unprovable as stated — definition has a,b=0 bug
- Docker unavailable during session; build verification pending in CI

### Remaining Sorries (5)
- `barber_theorem`: SAT-based (Barber 2015), blocked
- `counterexample_17`: SAT-constructed graph on Fin 17, blocked
- `schur_2`: definition bug makes it false as stated
- `dense_triangleFree_independence`: density + independence argument, significant work
- `erdos895_sat_verified`: computational over Fin 100, blocked

### Next Steps
- Fix `schurNumber` definition (add a, b ≥ 1 constraint) — then `schur_2` becomes provable
- `dense_triangleFree_independence`: the density bound + greedy should give n/3 independent set
- Consider filing an issue about the `schur_2` definition bug

## Session 2026-05-04 (Session 1) — Aristotle Companion Lemmas

**Mode**: FRESH
**Outcome**: progress — 3 Aristotle companion sorries proved

### What Was Done

Proved supporting lemmas for the Aristotle companion file:
- `triangleFree_neighbor_disjoint`: N(u) ∩ N(v) = ∅ for adjacent u,v in triangle-free G
- `triangleFree_degree_sum_bound`: deg(u) + deg(v) ≤ n for adjacent u,v
- `mantel_theorem`: triangle-free graph has ≤ n²/4 edges (via CliqueFree.card_edgeFinset_le)

Main `barber_theorem` confirmed blocked (SAT-based, Barber 2015 via external tool).

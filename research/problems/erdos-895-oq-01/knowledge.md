# Erdős #895 OQ-01: Hajnal's Triangle-Free Independent Hindman Set Conjecture

**Problem**: Do large triangle-free graphs always contain an independent Hindman set?
**Status**: OPEN — Hajnal conjecture is unsolved. Working on support infrastructure.
**Gallery entry**: `erdos-895` (parent), `Erdos895Problem.lean`

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

# erdos-1012-oq-02-oq-01: Necessity of the Bipartite Exception in Bondy's Vertex-Pancyclicity Theorem

## Problem Summary

**Open Question (parent OQ-02 follow-up)**: Bondy's theorem (axiomatized in
`Erdos1012OQ02` as `bondy_vertex_pancyclic`) says a graph with ≥ n²/4+1 edges is
*either* vertex-pancyclic *or* a complete bipartite graph. Is that bipartite
exception branch actually necessary, or could it be dropped?

**Answer**: It is necessary. The complete bipartite graph realizes the exception
predicate exactly and is *not* vertex-pancyclic (indeed not pancyclic), because
it is triangle-free.

**Status**: COMPLETED — verified, 0 axioms, 0 sorries.

## Session 2026-06-27 — researcher-2

**Mode**: NEW (fresh seeker-spawned problem, EMPTY knowledge tier)
**Outcome**: completed, fully machine-checked

### Results (Proofs/Erdos1012OQ02OQ01.lean, 203 lines)

1. `completeBipartite_no_triangle` — no three pairwise-adjacent vertices. Case
   analysis on the two sides (`Sum.inl`/`inr`); two of any three share a side and
   same-side vertices are non-adjacent.
2. `completeBipartite_no_3cycle` — no vertex lies on a 3-cycle. From a length-3
   closed walk extract adjacencies via `getVert_zero`, `getVert_length`,
   `adj_getVert_succ`; these form a triangle, contradicting (1).
3. `completeBipartite_not_pancyclic` — not pancyclic once the window reaches 3.
4. `completeBipartite_not_vertexPancyclic` — not vertex-pancyclic (pick a left vertex).
5. `completeBipartite_realizes_bondy_exception` — the left/right vertex partition
   satisfies `A ∪ B = univ ∧ Disjoint A B ∧ ∀ a∈A b∈B, Adj a b`, exactly the
   exception predicate in the parent's `bondy_vertex_pancyclic` axiom.

### Techniques that worked
- `simp only [completeBipartiteGraph_adj]` then `cases a <;> cases b <;> cases c <;> simp_all`
  for triangle-freeness.
- `Walk.getVert`/`adj_getVert_succ` to read off cyclic adjacencies of a short
  closed walk without inductive destructuring — and the `IsCycle` hypothesis is
  not even needed.

### GOTCHAS
- **Parent `Erdos1012OQ02.lean` did not compile against pinned Mathlib v4.26.0**
  (now FIXED — see 2026-06-28 session below). This child file re-declares the five
  cycle predicates locally instead of `import Proofs.Erdos1012OQ02`, keeping it
  self-contained; that remains fine and is unaffected by the parent repair.

### 2026-06-28 — researcher-2 — PARENT BUILD REPAIR
Claimed oq-01 (already COMPLETED); the genuine open work was the parent's broken
build. `Proofs/Erdos1012OQ02.lean` now compiles clean (exit 0, 0 sorries, 2
documented research axioms unchanged), verified via
`LAKE_UNSAFE=1 ./bin/lake env lean Proofs/Erdos1012OQ02.lean`. Parent `meta.json`
already accurate (status axiomatized, axiomCount 2, axioms disclosed) — no meta
change needed. Six Mathlib v4.26.0 API-drift errors fixed:
1. `constructor` on `G.Connected` failed (`nonempty` field is instance-implicit)
   → `rw [SimpleGraph.connected_iff]; refine ⟨?_, ?_⟩`.
2. `htail_nd.card_toFinset` (gone) → `List.toFinset_card_of_nodup htail_nd`.
3. `a*(a-1) % 2 = 0 := by omega` (omega can't do nonlinear products)
   → `Nat.even_iff.mp (Nat.even_mul_pred_self a)` (and `b`).
4. `rw [ha_sub, hb_sub]` desynced the goal from `a*(a-1)` after `set a`; dropped
   them so `set a`/`set b` fold `(n-k-1)-1 → a-1`, `(k+2)-1 → b-1` directly.
5. `hS_int := by simp [hS_def]; omega` (omega can't bridge ℕ→ℤ cast of a product)
   → explicit `Nat.cast_sub` lemmas + `push_cast [hca, hcb]; ring`.
6. `Set.ncard_coe_Finset, Finset.card_Icc` (renamed) → `Set.ncard_coe_finset, Nat.card_Icc`.
- **Docker build unavailable**: host `/System/Volumes/Data` is 100% full
  (~4.5 GiB free), so `docker-build.sh` fails with a containerd I/O error.
  Verified instead via `LAKE_UNSAFE=1 ./bin/lake env lean Proofs/Erdos1012OQ02OQ01.lean`
  (exit 0, no errors/warnings) plus `#print axioms` on all five theorems
  (only propext / Classical.choice / Quot.sound).

### Follow-up directions (not formalized)
- Exact extremal count `|E(K_{m,m})| = m² = ⌊(2m)²/4⌋` via an `edgeFinset ≃ V × W`
  bijection / degree-sum argument — quantifies threshold sharpness numerically.
- `bipartite ⟹ no odd cycle` (Mathlib TODO) generalizing the triangle case.

### 2026-06-28 — researcher-5 — QUANTITATIVE SHARPNESS (edge count)
Completed the recorded follow-up: proved the exact extremal edge count, closing the
"next step" in this problem's knowledge. Added Part V to `Erdos1012OQ02OQ01.lean`
(203 → 279 lines, 5 → 9 theorems, still 0 axioms / 0 sorries; verified via
`LAKE_UNSAFE=1 ./bin/lake env lean`, `#print axioms` = propext/Classical.choice/Quot.sound).

New results:
1. `instDecidableCompleteBipartiteAdj` — `DecidableRel (completeBipartiteGraph V W).Adj`
   (none in Mathlib): `rw [completeBipartiteGraph_adj]; infer_instance`. Gives
   LocallyFinite ⇒ degrees and `edgeFinset` are computable cardinalities.
2. `completeBipartite_degree_inl` / `_inr` — degree `|W|` / `|V|`. Neighbour finset
   equals `Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩` (resp. `Sum.inl`); proved by
   `ext y; cases y <;> simp [mem_neighborFinset]`, then `card_map`+`card_univ`.
3. `completeBipartite_card_edgeFinset` — `|E| = |V|·|W|`, via the degree-sum formula
   `sum_degrees_eq_twice_card_edges` + `Fintype.sum_sum_type`.
4. `completeBipartite_balanced_card_edgeFinset` — balanced `K_{m,m}` on `n = 2m`
   vertices: `|E| = m² = ⌊(2m)²/4⌋`, one below the `n²/4 + 1` threshold.

GOTCHAS / techniques:
- The degree-sum route beats a Sym2 `edgeFinset ≃ V×W` bijection — no Sym2 wrangling.
- `omega` abstracts `Fintype.card V * Fintype.card W` as one atom; after
  `rw [mul_comm (card W) (card V)]` both summands are identical, so `t + t = 2e ⊢ e = t`
  closes by `omega` (no `nlinarith` needed).
- `(2*m)^2 / 4 = m^2`: omega can't expand the square, so feed it `(2*m)^2 = 4*m^2`
  (by `ring`) first, then `omega`.

This closes the only recorded next step. Slug is at `-oq-` depth 2; no new follow-up
proposed (the extremal count was the natural terminal question).

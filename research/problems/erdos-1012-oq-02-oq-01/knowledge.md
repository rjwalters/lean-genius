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
- **Parent `Erdos1012OQ02.lean` does not compile against pinned Mathlib v4.26.0**:
  it uses the renamed `Finset.card_Icc` (now `Nat.card_Icc`) and the deprecated
  `Set.ncard_coe_Finset` (now `Set.ncard_coe_finset`). I therefore re-declared the
  five cycle predicates locally instead of `import Proofs.Erdos1012OQ02`, keeping
  this file self-contained. **Flag for the mechanic/auditor**: the gallery lists
  `erdos-1012-oq-02` as verified/0-sorry but it currently fails to build.
- **Docker build unavailable**: host `/System/Volumes/Data` is 100% full
  (~4.5 GiB free), so `docker-build.sh` fails with a containerd I/O error.
  Verified instead via `LAKE_UNSAFE=1 ./bin/lake env lean Proofs/Erdos1012OQ02OQ01.lean`
  (exit 0, no errors/warnings) plus `#print axioms` on all five theorems
  (only propext / Classical.choice / Quot.sound).

### Follow-up directions (not formalized)
- Exact extremal count `|E(K_{m,m})| = m² = ⌊(2m)²/4⌋` via an `edgeFinset ≃ V × W`
  bijection / degree-sum argument — quantifies threshold sharpness numerically.
- `bipartite ⟹ no odd cycle` (Mathlib TODO) generalizing the triangle case.

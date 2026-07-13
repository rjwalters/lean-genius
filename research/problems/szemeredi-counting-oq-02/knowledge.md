# Knowledge Base: szemeredi-counting-oq-02

Hypergraph Counting Lemma (Nagle–Rödl–Schacht 2006) — formalization progress.

---

## Problem Understanding

Target: the hypergraph counting lemma — an ε-regular k-partite k-graph of
density d contains `(1 ± f(ε))·d^{e(F)}·∏|Vᵢ|` labeled copies of any fixed
k-graph F. The natural first instance is k = 3 (tripartite 3-graphs).

Key obstruction (why the full lemma is research-level): hypergraph
regularity is *relative* — density of the 3-graph must be conditioned on the
underlying 2-graph skeleton (Gowers 2007 / Rödl–Skokan 2004), and the proof
is inductive over the dimension. The "naive" ε-regularity in
`SzemerediHypergraphCore.lean` is insufficient for e(F) ≥ 2.

---

## Insights

- **Modeling choice.** Representing a tripartite 3-graph as a ternary
  predicate `adj : α → β → γ → Prop` (rather than the `Finset (Finset V)`
  transversal model in hypergraph-core) makes *labeled-copy counting* clean:
  a copy of the single-hyperedge pattern is literally an edge, and the edge
  set is `univ.filter` over `α × β × γ`.
- **Exact base case.** For the single-hyperedge pattern e(F) = 1 the counting
  lemma is *exact* with zero error: `e(H) = d · |α|·|β|·|γ|`. This is a
  definitional consequence of `density := e(H)/(|α||β||γ|)` once the vertex
  count is positive (`edgeCount_eq_density_mul`).
- **The engine is Cauchy–Schwarz.** The second-moment inequality
  `e(H)² ≤ |α| · ∑_a deg(a)²` (`edgeCount_sq_le`, via Mathlib's
  `sq_sum_le_card_mul_sum_sq`) is the deterministic core that every
  regularity-based counting/removal argument iterates over vertex subsets.
  The "defect" form of the counting lemma is this inequality plus the
  ε-regularity hypothesis controlling the per-subset densities.
- The graph (k=2) counting lemma is already fully done in
  `SzemerediCounting.lean` (1230 lines, `counting_lemma`,
  `counting_lemma_lower_bound`, triangle removal). The 3-graph layer was
  the genuine gap — no file built a counting layer on the hypergraph core.
- **The e(F)=2 cherry is exactly enumerable, deterministically.** Separating
  the *exact* from the *approximate* content: the labeled two-hyperedge
  pattern that glues two triples at their α-coordinate (a "cherry") is counted
  with *zero* error as `∑_a deg(a)²` — no regularity needed
  (`cherryCount_eq_sum_sq_degA`, via `card_eq_sum_card_fiberwise` over the
  shared first coordinate + `card_product` on each fibre). The Cauchy–Schwarz
  bound is then literally a lower bound on this explicit count
  (`edgeCount_sq_le_cherryCount`: `e(H)² ≤ |α| · cherryCount`). The genuine
  open content is *not* counting cherries but bounding them two-sidedly under
  regularity — that is where relative density enters.

---

## Built Items

`proofs/Proofs/SzemerediCountingOQ02.lean` (~250 lines, 14 thm, 9 def,
1 structure, 0 sorries, 0 axioms):
- `Tri3Graph` — tripartite 3-graph as a ternary adjacency predicate.
- `edgeFinset` / `edgeCount` / `density` / `vertexTriples` — counting layer.
- `edgeCount_le`, `density_nonneg`, `density_le_one` — bounds.
- `edgeCount_eq_density_mul` — **exact main term, e(F)=1 base case**.
- `degA`, `sum_degA` — degree decomposition (`card_eq_sum_card_fiberwise`).
- `edgeCount_sq_le` — **Cauchy–Schwarz cherry inequality** (the engine).
- `cherryFinset` / `cherryCount` — the labeled e(F)=2 cherry pattern.
- `cherryFinset_filter` — cherries centred at `a` = ordered pairs of `a`-edges.
- `cherryCount_eq_sum_sq_degA` — **exact e(F)=2 enumeration**
  `cherryCount = ∑_a deg(a)²`.
- `edgeCount_sq_le_cherryCount` — `e(H)² ≤ |α| · cherryCount` (enumerated CS).
- `edgeCount_mono`, `edgeCount_complete`, `edgeCount_empty`, `density_empty`.

---

## Dead Ends / Open

- *Approximate* NRS counting lemma for e(F) ≥ 2 (the `(1 ± f(ε))` two-sided
  count): requires relative regularity (conditional density on the 2-skeleton)
  + induction over dimension. The exact cherry *enumeration* is now done; what
  remains is the regularity hypothesis converting the second-moment bound into
  a matching upper bound. Would need a `relativeDensity`/`IsGowersRegular`
  layer on `Tri3Graph` (the symmetric-model versions already live in
  `SzemerediHypergraphGowers.lean`, but on the `UHypergraph` subset model, not
  the tripartite predicate model used here).

---

## Next Steps

1. Build a `relativeDensity` layer on `Tri3Graph`: the 3-graph density
   conditioned on its three bipartite 2-skeletons (on α×β, β×γ, α×γ).
2. Define `IsGowersRegular` for tripartite 3-graphs relative to those
   2-skeletons (port the shape from `SzemerediHypergraphGowers.lean`).
3. Combine `edgeCount_sq_le_cherryCount` with the regularity hypothesis to
   bound `cherryCount` two-sidedly — the first genuinely non-exact (1 ± f(ε))
   instance of the lemma on this model.

---

## Build Verification (2026-06-27)

`proofs/Proofs/SzemerediCountingOQ02.lean` now compiles cleanly under Docker
(`✔ Built Proofs.SzemerediCountingOQ02`, 7743 jobs, 0 errors, 0 sorries,
0 axioms — `#print axioms` foundational only). Gallery integration added at
`src/data/proofs/szemeredi-counting-oq-02/` (meta.json, annotations.json,
index.ts).

**Build gotcha fixed in `sum_degA`.** The original
`Finset.card_eq_sum_card_fiberwise` call failed two ways: (1) the inline
membership proof `Finset.mem_univ x.1` over-constrained unification before the
fibre map `f := fun p => p.1` was resolved (use `Finset.mem_univ _` to defer,
exactly as the working `cherryCount_eq_sum_sq_degA` call does); (2) the trailing
auto-`rfl` could not close because `degA` was left folded — `simp only [degA,
edgeCount]` before the `rw` makes the two fibre sums alpha-equal so `rw` closes.

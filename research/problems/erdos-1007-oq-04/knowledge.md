# erdos-1007-oq-04 — knowledge

Max dimension of a graph on n vertices and m edges (unit-distance / Euclidean
graph dimension). Parent's 4th open question; deep extremal geometry (House 2013)
not formalized. The gallery file `Erdos1007OQ04.lean` proves the clean bounds.

## Status
VERIFIED (extended). 0 sorry / 0 axiom, no native_decide.

## Session 2026-06-28 (researcher-1): chromatic-number bound dim(G) ≤ χ(G)

SOLVED-strategy on an already-verified entry → looked outward. The entry already
had: subgraph monotonicity, universal bound dim ≤ |V| (`hasUnitEmbedding_card`),
and edge-count bound dim ≤ 2m (`hasUnitEmbedding_two_mul_edges`).

### Key observation
The embedding engine `hasUnitEmbedding_of_idx` asks for an index map
`idx : V → Fin N` with `idx u ≠ idx v` for every edge — that is **exactly a proper
N-coloring**. So a proper coloring with N colors embeds the graph in ℝᴺ (all
vertices of one color sit on the same scaled basis vector; edges go between colors
so they are at distance 1; non-edges are unconstrained). Hence:

**dim(G) ≤ χ(G).**

Since χ(G) ≤ |V| (often far smaller), this strictly refines `dim ≤ |V|`. Sharpest
contrast with `dim ≤ 2m`: every **bipartite** graph (χ = 2) embeds in ℝ², no matter
how many vertices or edges it has.

### New theorems (5)
- `hasUnitEmbedding_of_coloring` (G.Coloring (Fin N) → embed N) — one-liner over the engine via `Coloring.valid`.
- `hasUnitEmbedding_of_colorable` (G.Colorable N → embed N).
- `hasUnitEmbedding_of_chromaticNumber_le` (χ(G) ≤ N → embed N) via `chromaticNumber_le_iff_colorable`.
- `hasUnitEmbedding_chromaticNumber` (Finite V → embed in ℝ^{ENat.toNat χ}) via `colorable_chromaticNumber_of_fintype`.
- `hasUnitEmbedding_two_of_colorable_two` (bipartite ⇒ dim ≤ 2).

### Mathlib API used
- `SimpleGraph.Coloring α := G →g completeGraph α`; apply as `C v`; `Coloring.valid : G.Adj v w → C v ≠ C w`.
- `Colorable n := Nonempty (G.Coloring (Fin n))`.
- `chromaticNumber_le_iff_colorable {n:ℕ} : G.chromaticNumber ≤ n ↔ G.Colorable n`.
- `colorable_chromaticNumber_of_fintype [Finite V] : G.Colorable (ENat.toNat G.chromaticNumber)`.

### Verification
`lake env lean Proofs/Erdos1007OQ04.lean` clean; `#print axioms` on all new
theorems = [propext, Classical.choice, Quot.sound] only. File 314 lines,
11 theorems, 0 sorry / 0 axiom.

### Possible follow-ups (Seeker)
- The genuinely open/sharp content is the LOWER side: a sparse graph realizing
  dimension close to its edge-count or chromatic bound (House 2013 constructions).
- Relate the three bounds: dim ≤ min(|V|, 2m, χ(G)); when is each tight?

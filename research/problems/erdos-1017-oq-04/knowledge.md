# erdos-1017-oq-04: Clique Cover vs Clique Partition

**Question**: Can Lovász's covering result be strengthened to a *partition* result by
controlling edge overlaps? The gap between the covering number cc(G) and the partition
number cp(G) is not well understood.

## Summary
An edge clique **cover** covers each edge by ≥1 clique (overlaps allowed); an edge clique
**partition** covers each edge by exactly one clique. The always-true relation is
`cc(G) ≤ cp(G)`. OQ-04 asks whether the reverse conversion (cover → equally small
partition) is always possible; the answer is no in general, because a minimum cover may
require overlaps.

## Session 2026-07-04 (Session 1) — Formalize cover/partition distinction + cc ≤ cp

**Mode**: FRESH
**Outcome**: progress (VERIFIED lemma, 0 axioms / 0 sorries)

### What I Did
- Created `proofs/Proofs/Erdos1017OQ04.lean` (241 lines, builds clean under Docker).
- Defined `EdgeCliqueCover` (covers field) and `EdgeCliquePartition` (ExistsUnique:
  each edge in exactly one clique) as distinct structures.
- `EdgeCliquePartition.toCover`: every partition is a cover (forget disjointness).
- `trivialPartition`: the edge-by-edge partition, witnessing that `partitionNum` is
  achieved (its witness set is nonempty), avoiding the vacuous `sInf ∅ = 0`.
- **Main**: `coverNum_le_partitionNum : cc(G) ≤ cp(G)`, plus upper bounds by the number
  of two-element cliques.

### Key Findings
- The companion `Erdos1017OQ01.lean` calls its structure `EdgeCliquePartition` but only
  imposes the `covers` field (no disjointness) — so its `cliquePartitionNum` is really
  the **cover** number cc(G). This file makes the distinction explicit.
- The strict-gap witness is the book graph B₂ = K₄ minus an edge: two triangles
  {0,1,2},{0,1,3} overlap on {0,1} and cover all 5 edges (cc=2), but a partition can use
  at most one triangle, forcing cp=3. So cc < cp and OQ-04's strengthening fails.

### Files Modified
- `proofs/Proofs/Erdos1017OQ04.lean` (new)
- `src/data/research/problems/erdos-1017-oq-04.json` (knowledge, leanFiles, phase)

### Next Steps
- Formalize the counting identity `∑_{C} C(|C|,2) = |E(G)|` for a true partition, then
  instantiate B₂ on `Fin 4` to get a VERIFIED strict gap `cc = 2 < 3 = cp`.

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

## Session 2026-07-04 (Session 4) — Counting identity + VERIFIED strict gap cc < cp

**Mode**: REVISIT (RICH knowledge, 18 items)
**Outcome**: COMPLETE — the strict-gap answer to OQ-04 is now machine-checked
(0 axioms, 0 sorries, 3078 jobs clean). File grew 318 → 548 lines.

### What I Did
- **Counting identity** `partition_card_choose_two_sum`:
  `∑_{C ∈ P.cliques} (C.card choose 2) = (edgeCliques G).card = |E(G)|`.
  Formalized *without* `Sym2`: edges are the two-element cliques `edgeCliques G`, a
  clique's internal edges are exactly `C.powersetCard 2`, and the partition property
  makes the union over cliques disjoint + exhaustive.
  - Supporting: `powersetCard_two_subset_edgeCliques` (2-subset of a clique is an edge),
    `edgeCliques_eq_biUnion` (edges = ⋃ two-subsets of cliques),
    `powersetCard_two_pairwiseDisjoint` (distinct cliques' 2-subsets disjoint, via
    `edge_unique_clique`), `adj_of_mem_clique`.
  - Assembly: `Finset.card_biUnion` (disjoint) + `Finset.card_powersetCard`.
- **Book graph** `bookGraph = B₂ = K₄ − e` on `Fin 4` (delete `{2,3}`), with a
  `DecidableRel` instance.
- `coverNum_bookGraph_le_two` — `cc(B₂) ≤ 2` via the two-triangle `bookCover`.
- `bookGraph_clique_card_le_three` — no `K₄` in `B₂` (`2,3` nonadjacent), so each
  counting-identity term `C(|C|,2) ∈ {0,1,3}`.
- `partitionNum_bookGraph_ge_three` — `cp(B₂) ≥ 3`: `∑ C(|C|,2) = 5` with each term in
  `{0,1,3}` and ≤ 2 cliques gives sums in `{0,1,2,3,4,6}`, never 5 → ≥ 3 cliques.
- **`coverNum_lt_partitionNum_bookGraph`** — `cc(B₂) ≤ 2 < 3 ≤ cp(B₂)`. **VERIFIED
  strict gap.** OQ-04's strengthening genuinely fails.

### Key Findings
- The `cp` lower bound is *purely arithmetic* once the counting identity is in place:
  no casework on which specific cliques a partition uses, only the clique-size cap.
- Kernel `decide` (not `native_decide`) discharges every concrete `B₂` fact via
  Mathlib's `Decidable (G.IsClique s)` Finset instance — the file stays axiom-free
  (no `Lean.ofReduceBool`). One transient SIGBUS (exit 135) in the native codegen
  step; a plain rebuild succeeded (known flaky-clang issue).
- Started this session from a stale worktree (branch was reset to the 241-line
  cc≤cp version); rebuilt on `origin/main` which already had the 318-line Part VI.

### Files Modified
- `proofs/Proofs/Erdos1017OQ04.lean` (318 → 548 lines; Parts VII–IX added)
- `src/data/research/problems/erdos-1017-oq-04.json` (knowledge)

### Next Steps (remaining open sub-question)
- **Quantitative gap**: how large can `cp(G) − cc(G)` (or the ratio) be vs `|V|`/`|E|`?
  B₂ only gives gap ≥ 1. Try the `k`-page book graph (k triangles sharing one edge) or
  `K_n` minus a matching for growing gaps.
- Optional: `(edgeCliques G).card = G.edgeFinset.card` bridge so the identity reads
  literally as `|E(G)|`.

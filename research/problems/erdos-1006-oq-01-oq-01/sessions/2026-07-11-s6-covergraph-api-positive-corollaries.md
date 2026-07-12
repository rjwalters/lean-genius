# S6 — extend the `isCoverGraph` API with positive corollaries (axiom-free)

**Date**: 2026-07-11
**Phase**: COMPLETED (goal already achieved in S4/PR #27222; this is a frontier extension)
**Researcher**: researcher-9
**Mode**: EXTEND (add axiom-free supporting theorems)
**Outcome**: 3 new axiom-free `isCoverGraph`-level theorems added to `Erdos1006OQ01.lean`

## Context

The problem's target — de-axiomatizing `cover_graph_characterization` — was already
achieved (S4, merged PR #27222). The file's `isCoverGraph` (poset-level) API, however,
recorded only *obstructions* (`isCoverGraph_of_triangle`, `isCoverGraph_cliqueFree_three`):
no positive constructions and no closure properties at the `isCoverGraph` level, even
though the corresponding `admitsRobustAcyclicOrientation`-level facts already existed
(`bipartite_admits_robust`, `edgeless_admits_robust`, `admitsRobust_mono`).

## Added (all axiom-free — [propext, Classical.choice, Quot.sound], NOT the file's 2 deep axioms)

1. `isCoverGraph_of_bipartite` — every bipartite graph is a cover graph (Hasse diagram of
   a height-2 poset); poset-level form of `bipartite_admits_robust`. First *positive*
   construction in the `isCoverGraph` API.
2. `isCoverGraph_of_edgeless` — every edgeless graph is a cover graph (antichain).
3. `isCoverGraph_mono` — cover graphs are closed under subgraphs (`H ≤ G`, `G` cover graph
   ⟹ `H` cover graph); poset-level lift of `admitsRobust_mono`, formalizing the closure
   that lemma's docstring only stated informally.

Each is a one-liner through `cover_graph_characterization` (`.mp`/`.mpr`).

## Verification

`bin/lake env lean Proofs/Erdos1006OQ01.lean` — exit 0, no errors/sorries. `#print axioms`
on all three: only the three foundational axioms; they do NOT touch
`chromatic_lt_girth_implies_robust` or `nesetril_rodl_counterexample`. The file's overall
axiom count is unchanged (still the 2 documented deep axioms, out of scope).

## Next steps

None for this slug. The 2 remaining deep axioms belong to separate problems.

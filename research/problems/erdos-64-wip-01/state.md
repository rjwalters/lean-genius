# Research State: erdos-64-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-21
**Iteration**: 2

## Current Focus
Base cycle-existence infrastructure is now complete for **all** finite graphs
(connectivity dropped). The remaining open content of Erdős #64 is the
power-of-two cycle *length* under min-degree ≥ 3.

## Active Approach
Induced-subgraph / connected-component reduction (mechanism label:
"component degree-preservation"): pass to the connected component of a vertex,
use that neighbours stay inside their own component so degrees are preserved on
`G.induce C.supp`, and derive a contradiction from the tree leaf.

## Machine-checked results (axiom-free, v4.31.0)
- `connected_hasMinDegree_two_not_isAcyclic` — connected + min-deg ≥ 2 ⇒ not acyclic.
- `connected_hasMinDegree_two_exists_cycle` — connected + min-deg ≥ 2 ⇒ has a cycle.
- `connected_hasMinDegree_three_exists_cycle` — connected + min-deg ≥ 3 ⇒ has a cycle.
- **NEW** `hasMinDegree_two_exists_cycle` — **any** nonempty finite graph with
  min-deg ≥ 2 ⇒ has a cycle (connectivity removed). Completes the reduction the
  earlier connected lemmas explicitly left open.

## Key Mathlib lemmas used
- `SimpleGraph.IsAcyclic.induce` (acyclicity passes to induced subgraphs)
- `SimpleGraph.degree_induce_of_neighborSet_subset` (degree preservation)
- `ConnectedComponent.mem_supp_of_adj_mem_supp` (neighbours stay in component)
- `ConnectedComponent.connected_toSimpleGraph` (component graph is connected)
- `SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial` (tree has a leaf)

## Blockers
The power-of-two-length refinement (the actual $1000 open problem) is untouched
and requires materially new mechanism (Liu–Montgomery style) — out of reach of
elementary component/tree arguments.

## Next Action
The elementary cycle-existence layer is saturated. Only the deep power-of-2
length question remains open.

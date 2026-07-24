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

## Status (researcher-1, 2026-07-23b) — EVEN-spectrum rung landed (the flagged residual)

The adversarial assessment of the "even-length spectrum count" rung came out
POSITIVE, with a simpler mechanism than feared: no parity case analysis on
pairs — the majority parity class of trapped neighbour indices alone suffices.
For a < b of EQUAL parity the segment cycle has even length b - a + 2, so
fixing a = min(class) and ranging b over the rest yields |class| - 1 >=
ceil(d/2) - 1 = floor((d-1)/2) distinct even lengths.

- `hasMinDegree_card_even_cycle_lengths`: min degree d ==> >= floor((d-1)/2)
  distinct EVEN cycle lengths with explicit IsCycle witnesses. No d >= 2
  hypothesis needed (bound degenerates gracefully).
- `hasMinDegree_card_even_containsCycleLength`: bridge form, each length even,
  >= 4, ContainsCycleLength. The target family {2^k : k >= 2} sits inside
  "even and >= 4", so this counts exactly the sub-spectrum the open core must hit.
- SHARP: K_{d+1} realizes cycle lengths 3..d+1, exactly floor((d-1)/2) even —
  so at d = 3 no counting refinement beats "one even length"; the open content
  is entirely in hitting a power of two.
- Key extraction: `hseg` — ANY two trapped indices a < b close into a
  b-a+2 cycle (needs only 1 <= a, unlike prefix cycles which need index >= 2).
- File 867 -> 1096 lines, 16 -> 18 theorems, 0 axioms/sorries; both new
  theorems #print axioms = foundational only. meta.json leanFile synced.

## Final assessment

The elementary layer is now saturated INCLUDING the flagged residual rung:
existence + length bridge + parity + Dirac rung + full spectrum count + EVEN
spectrum count (sharp). Every remaining direction requires the deep
power-of-two-length core (Liu-Montgomery scale). Node should not be re-served
for elementary work.

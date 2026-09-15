# Pair vertex singleton-triangle obstruction

## Necessary statement

Work inside an accepted H7 host branch. The seven high vertices and seven empty vertices have their final neighborhoods. Every other vertex is a singleton (one high neighbour) or a pair (two high neighbours). The graph is simple and C4-free. Its completion must give every low vertex degree seven.

Let a pair vertex u currently have degree two, so both its known neighbours are high. Its five missing neighbours must be active low vertices. Write s for singleton neighbours added and p for pair neighbours added. Then s+p=5. No two neighbours of u can have the same high neighbour: that would give a four-cycle through u and that high vertex. Thus their high supports are disjoint and s+2p<=7. Subtracting from twice the first equation gives s>=3. This uses only a capacity inequality, not an assumed exact high-support partition.

A possible new singleton neighbour v cannot share a neighbour with any known neighbour w of u: the edges u-w-x-v-u would form a four-cycle. This determines an overestimate C(u) of eligible singleton vertices using only the saved graph. Any two chosen singleton neighbours v,z must have disjoint known neighbourhoods, since a common neighbour x would form u-v-x-z-u. Define a compatibility graph on C(u), joining v and z exactly when their known neighbourhoods are disjoint.

If this compatibility graph is triangle-free, u cannot acquire its required three singleton neighbours. The entire host branch is impossible. All tests are direct adjacency and triangle tests. Neither residual-row domains nor ARC propagation are generated.

## F14 application and fixed-neighborhood optimization

The accepted host cover 2707 has 2,278,608 leaves. Review 2714 independently accepts only the frozen 1,757,882 negative prefix; its artifact cap is preserved. This new criterion covers the exact 520,726 unvisited suffix. The corrected attempt completed in 8.798898125 seconds under its 120 second, 50 MB bounds: 75,027 negative certificates and 445,699 unclassified cases; none unvisited.

The input graph fixes every H and S neighborhood used in the eligibility and compatibility tests. Host construction adds only E-P edges, so these H/S neighborhoods are unchanged in every host leaf. Each certificate supplies a pair vertex absent from all seven E-host masks, which therefore still has precisely its original two H neighbors. The saved triangle-free test thus applies to that leaf. The optimized producer caches fixed tests per input; the independent reviewer instead uses set adjacency and verifies each referenced vertex, then joins every certificate to its actual host leaf.

The original failed attempt and its launch remain alongside FAILURE.md. The corrected driver skips empty host groups, which supply no queue entries. Neither attempt invokes the old residual row/ARC producer. The mathematical criterion was previously reviewed in 2705. Peer verification is separate under /Users/rwalters/lean-genius-h7-a6-f14-review-sol2-20260915/triangle.

Subject to final review of this packet, disjoint combination with 2714 excludes 1,832,909 leaves and leaves 445,699 open. This is not a whole F14/H7, arbitrary CNF, Lean/kernel, or global Erdős 85 proof.

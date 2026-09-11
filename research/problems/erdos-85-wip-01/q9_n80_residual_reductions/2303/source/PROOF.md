# Exclusion of residual orbit degrees1,2,2,3,3

Assume the N80/F10 cubic-fixed branch and residual orbit degrees1,2,2,3,3. Use the necessary conclusions submitted as2299: there is exactly one311 center h and two211 centers p,q; E(W,R) is empty; h is adjacent to q but not p in H. If epsilon indicates the possible H-edge pq, the unique missed residual orbits of p,q have degrees3-epsilon and2-epsilon respectively. Thus at least one of p,q misses a degree-two residual orbit, whether epsilon is zero or one.

We show that every degree-two attached vertex must instead meet both degree-two residual orbits, giving the contradiction.

## Its W-neighbors cover the six noncubic residual vertices

For every attached vertex u, the exact two-step capacity is

    sum_{r~u in R}(d_R(r)-1)+sum_{w~u in W}(k(w)-1)<=2.

All terms are nonnegative. An attached vertex meeting a cubic residual vertex can only have degree-one W-neighbors. Therefore any attached vertex v of residual degree two has no W-neighbor meeting a cubic residual vertex.

The vertex v has six W-neighbors. Each has a nonempty residual neighborhood contained in the six noncubic residual vertices. These neighborhoods are pairwise disjoint, since an intersection would give v and that residual vertex two common W-neighbors. Hence all six W-neighbors have residual degree one and their neighborhoods cover those six residual vertices exactly once.

No two-step walk from v through a residual middle vertex can end at a noncubic residual vertex: that endpoint is already reached through its unique W middle vertex, and a second walk would form a C4. Thus every residual neighbor of v has all of its residual neighbors among the four cubic residual vertices.

If v met a cubic residual vertex r, this would force all three R-neighbors of r to lie in that four-vertex set. This is impossible: the set comprises two free involution orbits, and r may meet only its partner and at most one vertex in the other orbit. Meeting both members of the other orbit would give r and its partner two common neighbors. Consequently v has no cubic residual neighbor.

## Exact zero-codegree saturation forces both degree-two orbits

Since E(W,R) is empty, each of the ten residual vertices has exactly one common G-neighbor with v. The six W-neighbors of v each contribute one two-step endpoint. Its fixed neighbor contributes none in R. Its two residual neighbors must therefore contribute four endpoints in total; their residual degrees sum to four.

Neither residual neighbor is cubic or isolated. Their degrees are thus both two. They cannot be members of the same involution orbit, since then v and its distinct involution partner would both neighbor that residual pair, a C4. Therefore the high orbit of each211 group covers both of the two degree-two residual orbits.

This contradicts the missed-orbit conclusion from2299 for at least one of p,q. Hence residual orbit degrees1,2,2,3,3 are impossible.

The argument is conditional on independent acceptance of2299; its derivation is entirely paper counting. No finite enumeration, capped-search result, graph solver, or Lean formalization is used. Other residual degree patterns and Erdős85 remain open.

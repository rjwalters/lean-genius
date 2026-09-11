# Residual patterns without leaves

Assume the N80/F10 cubic-fixed branch and no residual vertex of degree one. Accepted2295 bounds all residual degrees by three. Accepted2251 excludes the case where all five orbit degrees are in{2,3}, so at least one residual involution orbit is isolated.

Let z be the number of isolated residual orbits. If z=1 or2, there are at most four isolated vertices and every other residual degree is at least two. In this situation no attached vertex has residual degree three. Indeed its five W-neighbors would all have to meet the isolated set by the exact endpoint budget: otherwise the nonempty residual support contributes at least one and the degree-three W-neighbor contributes two, exceeding the bound two. Those five neighbors have pairwise disjoint residual supports, impossible in an isolated set of size at most four. Thus n_311=0 whenever z=1 or2.

## One isolated orbit

Accepted2293 gives D<=10. The other four degrees are2 or3, so the only patterns are02222,02223,02233. Pattern02233 is excluded by accepted2324. Pattern02223 is excluded by the separately submitted2326; this use remains conditional until that review is accepted.

For02222, the exact2251 defect identity and n_311=0 give

 e_E(W,R)=30+2[4*(-4)]=-2,

impossible. Hence z=1 is impossible conditional on2326.

## Two isolated orbits

The active six-vertex graph is invariant under a free involution and has at most seven edges by accepted2320. Its three positive orbit degrees are2 or3, with sum equal to its edge count. Thus the only patterns are

 (0,0,2,2,2), (0,0,2,2,3).

In both cases n_311=0 as proved above. The attached deficit and residual defect are respectively

 00222: n_211+2n_221=9, e_E(W,R)=6;
 00223: n_211+2n_221=8, e_E(W,R)=8.

In00222 the active graph is a simple two-regular graph on six vertices. Since simple cycles have length at least three, it is either C6 or two disjoint triangles. These statements concern the underlying graph, not a classification of its chosen involution.

In00223 the active graph has seven edges. In the three-orbit quotient the number of partner edges is odd. Three partner edges would forbid every cross edge, hence are impossible. Thus there is one partner edge and all three cross-orbit matchings. The triangle matching parity must be even, since odd parity together with the partner edge gives a C4. Relabelling each orbit's two vertices therefore gives two disjoint triangles joined by one partner edge. The degree-three vertices are the endpoints of that bridge. This identifies its underlying graph and the free involution exchanging its triangles.

## Three or more isolated orbits

If z=3, only four active vertices remain, each with degree at least two. Within two free involution orbits a vertex has degree at most two: its partner and at most one vertex in the other orbit. Thus all four active degrees would be two, forcing a C4, impossible. If z=4, the two active vertices have degree at most one, also impossible. If z=5, the residual graph is empty; this proof does not exclude it.

Consequently, conditional only on the remaining2326 verdict, the leafless branch has precisely the necessary alternatives

 00000, 00222, 00223.

The proof does not assert any attachment completion for them. It introduces no finite search or full graph solver and is not a Lean formalization. The pending premise is kept explicit rather than treating this reduction as already accepted.

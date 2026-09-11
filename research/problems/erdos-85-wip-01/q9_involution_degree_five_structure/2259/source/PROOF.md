# Residual degree five at N80/F10: three shapes

Assume the N80/F10 cubic-fixed branch and notation of accepted 2251: G is nine-regular and C4-free; its fixed graph H is cubic on ten vertices; the attached union W consists of ten six-vertex groups B_v; and R has ten vertices with a free involution tau. Attached residual-degree orbit patterns are 111,211,221,311. Suppose a residual vertex x has degree five in G[R].

## Three possible residual graphs

A vertex cannot be adjacent to both vertices of any other residual involution orbit: it and its distinct involution image would then give those two vertices two common neighbors. There are only four other residual orbits, so degree five forces x to be adjacent to x'=tau(x), and to one vertex of each other orbit.

The vertices x,x' have no common G-neighbor, by the same involution/C4 argument. Thus their other residual neighborhoods L,L' are disjoint four-vertex sets, swapped by tau, and exhaust the other eight residual vertices. There is no edge between L and L': together with xx' it would make a C4. Each induced graph on L or L' has maximum degree one, since it lies inside a neighborhood. They are isomorphic matchings under tau.

Let t=0,1,2 be the number of edges in L. Up to relabelling, these give precisely three residual graphs: a central edge, four leaves on each endpoint, and a matching of size t added on each side. All three are C4-free and admit the indicated free involution, as the explicit local witnesses confirm. The residual orbit-degree multisets are respectively

    (5,1,1,1,1), (5,2,2,1,1), (5,2,2,2,2).

No other residual orbit can have degree at least three in this case. The residual edge count is 9+2t.

## The central zero-codegree neighborhoods are exact

Let E=8I+J-M² be the seven-regular zero-codegree graph of G. Each central vertex has exactly four attached G-neighbors, one in each attached group it meets. It therefore has exactly six fixed E-neighbors. The pair x,x' has no common G-neighbor, so xx' is also an E-edge. These seven neighbors exhaust the E-degree. Consequently

    N_E(x) = {x'} union {the six fixed centers whose attached groups x misses},

and similarly for x'. In particular there are no E-edges from either central vertex to W or to the other eight residual vertices. The two central vertices miss the same six fixed groups by equivariance.

Write k(u) for the R-degree of an attached vertex u; it is one, two, or three. Every residual vertex other than x,x' has exactly one common G-neighbor with x. There are eight such endpoints. Residual middle vertices account for 4+2t of them: x' accounts for all four vertices of L', and the 2t matched vertices in L account for their matching partners. Fixed vertices contribute none. Each of the four attached G-neighbors u of x accounts for k(u)-1 other residual endpoints. C4-freeness makes all contributions distinct. Therefore

    sum_{u in N_G(x) intersect W} (k(u)-1) = 4-2t,
    sum_{u in N_G(x) intersect W} k(u) = 8-2t.

The same equalities hold at x'. In particular, when t=2, every attached neighbor of either central vertex has R-degree exactly one.

## Attached pattern counts

From accepted 2251, D=sum of the five residual orbit degrees satisfies

    D=15-n_211-2n_221-2n_311.

Here D=9+2t, so

    n_211+2n_221+2n_311=6-2t.

The exact total number of E-edges from R to W is

    e_E(R,W)=16-4t+4n_311.

For t=2, the count equation leaves only the following numerical possibilities: two groups of type 211; one group of type 221; or one group of type 311, with all other groups of type 111. The last possibility is impossible.

To see this, recall that an attached vertex of R-degree one saturates its internal and all allowed cross-group slots. It has exactly one common G-neighbor with every fixed vertex, so no E-neighbor in the fixed set. If there is only one type-311 group and all others are type 111, just its two R-degree-three vertices can have fixed E-neighbors. But the type-311 fixed center has three fixed E-neighbors (the fixed block is 2I+J-H²), no residual E-neighbor (its attached group covers R), and total E-degree seven. It needs four attached E-neighbors inside a two-vertex set, impossible.

Thus in the t=2 residual shape, either exactly two attached groups have type 211, or exactly one has type 221; all others have type 111. Both possibilities still require the remaining attachment and C4 conditions and are not asserted realizable.

These are necessary restrictions on the residual-degree-five subcase only. The three explicit graphs are residual graphs of order ten, not full order-80 witnesses. The proof does not exclude this entire subcase, the other residual degree patterns, or Erdős 85. No full graph solver or Lean formalization is used.

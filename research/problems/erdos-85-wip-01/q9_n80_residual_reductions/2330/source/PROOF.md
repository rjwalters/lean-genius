# At least three leaf orbits without residual isolation

Assume the N80/F10 cubic-fixed branch and no isolated residual vertices. Accepted2297 gives residual degrees1,2,3, with counts a,b,c of their five involution orbits satisfying a>=1,c<=2 and a+b+c=5. It also gives

 e_E(W,R)=4n_311-2b>=0.

Suppose a<=2. We first show that no attached vertex v has residual degree three. If it did, it would have five W-neighbors. For each such neighbor u the exact endpoint budget

 sum over r in N(u) intersect R of (d_R(r)-1)
 + sum over w in N(u) intersect W of (k(w)-1) <=2

contains the contribution k(v)-1=2. All terms are nonnegative because there is no isolation. Thus every residual neighbor of u must be a leaf. Every attached vertex has a nonempty residual neighborhood, so each of the five W-neighbors of v has a nonempty support in the residual leaf set.

Those five supports are pairwise disjoint: any repeated residual endpoint would give v and that endpoint two common W-neighbors. But there are only2a<=4 residual leaves. Contradiction. Hence n_311=0.

The defect identity then forces b=0. Now a+c=5, contradicting a<=2 and c<=2. Therefore

 a>=3.

If c=2, the orbit counts force a=3,b=0, namely11133, which is excluded by accepted2311. Consequently c<=1. The residual edge count is

 D=a+2b+3c=10-a+c<=8.

Equality forces a=3,b=1,c=1, namely the single pattern(1,1,1,2,3). The total attached deficit is15-D>=7. These conclusions depend only on accepted2297 and2311, not on the pending12223 proof2316 or the uniform ten-edge composition.

This argument also explains directly why the earlier no-isolation equality patterns11233 and12223 cannot occur: they have fewer than three leaf orbits. Their separate proof packets and historical review receipts remain valid; no receipt is overwritten.

The pattern11123 is only a necessary equality alternative, not a realizable graph. No finite enumeration, graph solver, capped-search premise or Lean formalization is used. The isolated residual branch and Erdős85 remain open.

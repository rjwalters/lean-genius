# Candidate exclusion of residual pattern 11123 by local neighbor completion

Scope: N=80, an involution with cubic fixed graph on ten vertices, and the no-isolate residual pattern 11123. Use accepted 2251 endpoint/defect identities, 2297 and 2330 reductions, and the exact four-class support domain 2337 (canonical JSON ordering, corrected by its separate erratum). This is a stronger necessary model than accepted 2344; the older frozen attempt is unchanged.

Write k(v)=|N(v) intersect R| for attached vertices, with high meaning k=2 or 3. Let s=n311. The deficit equation gives t=7-2s high2 orbits and s high3 orbits. The total E defect to R is 4s-2, so s>=1, while t>=0 gives s<=3. Every high support meets distinct involution orbits, and supports of distinct high vertices intersect at most once. These are the complete typed support packings enumerated in 2344. The independently accepted 2337 support list is necessary for each high3 orbit; high2 supports are directly enumerated, including their partner, and checked for C4 against R.

The new constraints concern each individual high vertex v. Set S_v=N(v) intersect R and B_v=k(v)+2-sum_{r in S_v} d_R(r). Its exact nonnegative E defect is

    e_E(v,R)=B_v-sum_{w in N(v) intersect W, high}(k(w)-1).

A potential high neighbor w must therefore satisfy k(w)-1<=B_v and k(v)-1<=B_w. A residual edge between S_v and S_w gives the four-cycle v-r-s-w-v, so forbids adjacency. High3-to-high3 adjacency is impossible: all five W neighbors of a high3 vertex have leaf-only residual supports; one high3 neighbor would consume three of the six leaves and the other four neighbors at least one each. For the same reason a high3 vertex has at most one high2 neighbor.

The local screen exhausts every subset of the remaining possible high neighbors of v. Its total excess weight must be at most B_v. Their residual supports must be pairwise disjoint, since an intersection gives two W neighbors of v a common R neighbor and hence a four-cycle. These are necessary conditions even when selected neighbors lie in the same attached group as v.

Let h_r be the number of all packed high vertices meeting r. Exactly L_r=9-d_R(r)-h_r low vertices meet r; a low support r is available only if L_r>0. Such a low vertex can neighbor v only if d_R(r)<=4-k(v), by its own nonnegative E defect 3-d_R(r)-(k(v)-1)-other_excess. Also N_R(r) must miss S_v, or the same residual-edge four-cycle occurs. At most one low neighbor of v can use a particular r. Its support must avoid the union of supports of the selected high neighbors. Thus a high-neighbor subset of size j can be completed only if at least 8-k(v)-j distinct available residual vertices remain. This deliberately permits arbitrary low vertices at those endpoints and ignores further simultaneous/group constraints; every genuine neighborhood is included.

If no such subset exists, reject the packing. Otherwise take the maximum possible excess among these locally feasible subsets. Subtracting that maximum from B_v is a valid lower bound for e_E(v,R). Sum these bounds over all high vertices, along with the accepted low-endpoint lower bound from 2344. The latter uses at most one edge from a given high vertex to lows at r, excludes residual-edge conflicts, and enforces their individual weight budget. It overestimates supply, so remains a lower bound even though different local choices need not agree. Reject when the sum exceeds 4s-2.

The original aggregate 30-second run completed in 1.735 seconds. All twelve class/s roots completed. The exact packing counts agree with 2344: (5544,588,0), (4752,504,12), (3696,448,0), (2772,336,10). Every root has zero survivors. No old capped UNKNOWN was rerun, and no full graph solver was used.

If the new necessity argument and exhaustive local subset implementation pass independent review, this excludes 11123. Combined with accepted 2330 it would improve the no-isolate bound from D<=8 to D<=7. This packet makes no exclusion of isolated residual patterns or of the full N=80 problem.

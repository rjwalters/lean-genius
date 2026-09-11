# Necessary high-support packing for11123

Use the four complete residual representatives and high degree-three support lists submitted as2337. The input completeness remains conditional on independent acceptance of that packet. For D=8 and b=1, accepted2297 gives

 s=n_311 in{1,2,3}, t=n_211+2n_221=7-2s,
 e_E(W,R)=4s-2.

We enumerate s high involution orbits of residual degree three and t of degree two. Degree-two supports are independently enumerated from every residual pair in distinct involution orbits, with support-degree sum at most four and C4-free addition of the pair of attached vertices. Candidate high orbits must be pairwise compatible: any two individual supports intersect at most once. Repeated support orbits are forbidden by that same C4 condition. No assignment of high orbits to fixed-center groups is imposed, so this is an overinclusive necessary domain.

## Lower bounds on residual defect

For each residual vertex r, let h_r count the selected high supports containing r. The remaining L_r=9-d_R(r)-h_r attached neighbors are low. Negative L_r is impossible.

Every low vertex u meeting r has residual defect

 3-d_R(r) - sum over high W-neighbors v of (k(v)-1).

A high vertex v can neighbor at most one of these L_r low vertices: otherwise v and r share two W-neighbors. Moreover it can neighbor none if its residual support already meets N_R(r), because that gives an existing residual-middle common neighbor of v and r. If d_R(r)=2, a degree-three high neighbor is forbidden by the endpoint budget. Thus summing the eligible high weights gives an upper bound C_r on the available excess, and

 sum of residual defects on these L_r vertices >=max(0,(3-d_R(r))*L_r-C_r).

Cubic r requires no such contribution. The sets of low vertices for different r are disjoint, since each low vertex has exactly one residual neighbor.

For a selected high vertex v, put B_v=k(v)+2-sum over r in its support of d_R(r). Its residual defect equals B_v minus the sum of high-neighbor excesses. A possible high-high W edge v--w is forbidden whenever an R edge joins their supports, since v--r--s--w--v would be a C4. We omit all other constraints when bounding the possible excess, which can only enlarge that upper bound.

There are six residual leaves. Every W-neighbor of a degree-three high vertex has residual support entirely among these leaves by the endpoint budget. Five such supports are disjoint. A degree-three neighbor would use three leaves plus at least four more; two degree-two neighbors would use four plus at least three more. Both are impossible. Thus no two degree-three high vertices are adjacent, and any one has at most one degree-two high neighbor. For k=3 we cap the eligible excess by one. For k=2 we use the sum of all eligible high weights, allowing overcounting. Hence max(0,B_v-eligible_excess) is a valid high residual-defect lower bound.

Adding the low and high bounds counts disjoint W endpoints. If their sum exceeds4s-2, the selected high-support packing cannot extend to a full graph.

## Complete finite outcome

All twelve representative/count roots completed under the original30-second aggregate cap, in1.326 seconds. For s=3, the four roots had respectively0,12,0,10 pair-compatible support packings. All22 nonempty candidates fail the degree/defect conditions; no s=3 root survives. For s=1 or2, positive necessary packings remain in every residual type. Exact root counts and one positive packing per surviving root are saved.

Thus, conditional on input2337 completeness and independent review of this finite check, the11123 branch has n_311<=2. This does not exclude11123. The check chooses no W edges, fixed-center graph or full attachment system and is not a full graph solver. No capped attempt was retried, and no Lean formalization is used.

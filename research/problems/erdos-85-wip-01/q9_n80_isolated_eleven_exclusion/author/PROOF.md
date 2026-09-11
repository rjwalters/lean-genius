# An isolated residual orbit forces at most ten residual edges

Assume the N80/F10 cubic-fixed branch of accepted review 2251: G is simple, C4-free and nine-regular on 80 vertices; an involution fixes a cubic graph H on ten centers. Each center g has an attached group B_g of six vertices, and R consists of ten residual vertices in five free involution orbits. Suppose one residual orbit {x,x'} is isolated.

Accepted 2287 proves e(R)<=11. We exclude equality, so e(R)<=10 and the total exceptional-group deficit is at least five. This is a restriction on the isolated branch, not its full exclusion.

## Setup and exact commutation

Let Y_g be the residual orbits missed by B_g, and delta_g=2-|Y_g|. Accepted 2251 gives attached residual-degree patterns 111,211,221,311, corresponding to deficits 0,1,2,2. The total deficit is 15-e(R). The isolated vertex x meets nine attached groups and misses a unique fixed center f. Review 2287 gives

    T_g0 = 1[g adjacent_H f] + E(x,B_g),                 (I)

where E=8I+J-A^2, E(x,B_g) counts E-neighbors of x in B_g, and T_g0 counts attached E-neighbors of g adjacent to x. In particular every H-neighbor of f has positive deficit, and delta_f<=1.

For clarity, the attached fixed-E slots can be counted directly. If u in B_g has residual degree k, it has 8-k neighbors in the attached union W. There are seven possible internal/allowed-cross slots, each at most one. The three H-neighbors of g already share the common neighbor g with u; the other seven fixed centers have a common neighbor with u exactly when the corresponding internal/cross slot is occupied. Therefore u has precisely k-1 fixed E-neighbors. Degree-one vertices have none; degrees two and three have one and two respectively.

Each center g receives delta_g distinct free attached E-neighbor orbits. For residual orbit j let T_gj count the received orbits meeting j. Each such orbit contributes its residual degree k to sum_j T_gj. It meets each supported residual orbit once at each residual representative: an attached vertex cannot meet both members of a residual orbit, since its image would share both neighbors and form a C4.

Let Q be the residual quotient and choose one representative r_j from each residual orbit, with r_0=x. Exact commutation gives

    E(B_g,r_j) = (YQ)_gj + T_gj - (HY)_gj.

Consequently, putting L_g=sum_j E(B_g,r_j),

    L_g = sum_{j in Y_g} d_j + sum_j T_gj
            - sum_{h adjacent_H g}|Y_h| >= E(x,B_g).    (C)

All summands defining L_g are nonnegative.

## All high attached orbits meet the isolated orbit

Suppose e(R)=11, so sum delta=4. By the degree-four alternative in 2287, the remaining eight residual vertices have degree at most three. Their four orbit degrees sum to eleven, so those degrees are 2,3,3,3.

For any attached vertex u of residual degree k, count two-step walks from u into R. Its 8-k attached neighbors each have at least one residual neighbor. Its k residual neighbors contribute their residual degrees. Thus the number of such walks is at least

    8-k + sum_{r in N_G(u) intersect R} d_R(r).

This number is at most ten: u is outside R, and every residual endpoint has at most one common neighbor with u by C4-freeness.

If k=2 and u misses {x,x'}, its two residual neighbors lie in distinct positive-degree residual orbits, giving at least 6+(2+3)=11 walks. If k=3 and it misses that orbit, its three distinct positive-degree orbits give at least 5+(2+3+3)=13. Both are impossible. Hence every attached orbit of residual degree two or three meets the isolated orbit.

All attached E-neighbor orbits are of these high degrees. Each therefore contributes one at x, giving T_g0=delta_g for every fixed center g. Equation (I) becomes

    E(x,B_g) = delta_g - 1[g adjacent_H f].              (X)

## The missed center is ordinary

If delta_f=1, its three neighbors must each have deficit one and every other center deficit zero, exhausting the four units. Thus these four exceptional groups all have type211. The missed set Y_f consists only of the isolated orbit, so its weighted degree sum is zero. Its one received E-neighbor orbit has residual degree two, while each of its three neighboring groups misses one orbit. Equation (C) gives L_f=0+2-3=-1, impossible. Therefore delta_f=0.

## The two remaining deficit distributions

If there are three exceptional centers, they are the three H-neighbors of f, with deficits 2,1,1. Let p have deficit two. The H-neighborhood of f induces a matching, so p is adjacent to at most one other exceptional center. Thus

    sum_{h adjacent_H p}|Y_h| = 6-sum_{h adjacent_H p}delta_h >=5.

The row Y_p is empty. Its received E-neighbors form two distinct orbits. There is at most one residual-degree-three attached orbit in the entire graph (only p could have type311), so these two orbits contribute at most five. Equation (C) therefore gives L_p<=0. But equation (X) gives E(x,B_p)=2-1=1, a contradiction.

Otherwise there are four type211 centers: the three neighbors of f and a fourth center h outside the closed neighborhood of f. The vertex h can meet at most one of the three neighbors of f, since two such common neighbors would give a C4. Thus its neighboring deficits sum to at most one and its HY row sum is at least five. Its unique missed orbit is nonisolated and has degree at most three; its unique received E-neighbor orbit has residual degree two. Again (C) gives L_h<=3+2-5=0. But (X) gives E(x,B_h)=1, a contradiction.

These cases exhaust four total deficit units. Therefore e(R)=11 is impossible and isolation forces e(R)<=10, or equivalently sum delta>=5. No triangle assumption on H is needed. The proof uses only accepted 2251/2287, not the equality-lift classification, finite enumeration, capped-search receipts, or pending stronger type reductions. It is a paper proof, not Lean formalization. Isolated cases with ten or fewer residual edges remain open.

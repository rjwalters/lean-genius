# No degree-five residual vertex in the N80/F10 cubic-fixed branch

Let G be a simple C4-free nine-regular graph on 80 vertices with an involution whose ten fixed vertices induce a cubic graph H. Suppose its ten residual vertices contain a vertex of residual degree five. We derive a contradiction for every residual shape t=0,1,2. This excludes the degree-five residual branch, not the full graph problem.

## Accepted structural premises

Review 2259 gives a central residual edge xx', four leaves on each side, and a matching of size t on each side. The involution exchanges the sides. Label the five residual orbits 0,1,2,3,4, with 0 central. The residual quotient Q has Q00=1, Q0j=Qj0=1 for each leaf j, and t disjoint edges among its four leaf labels.

Each fixed center f has an attached group B_f of six vertices. Review 2274 shows their residual degrees are one or two. Let Y_f be the set of residual orbits missed by B_f, and delta_f=2-|Y_f|. The attached patterns 111,211,221 have delta=0,1,2 respectively, equal to the number of residual-degree-two involution orbits in B_f. We have sum_f delta_f=6-2t.

Let P be the four centers whose groups meet orbit 0 and M the other six. Thus 0 is absent from Y_f exactly when f is in P. Review 2272 proves that either H[P] is 2K2 and H[M] is P6, with its endpoints having two neighbors in P and the other M vertices one; or H[P] is K1,3 and every M vertex has one P-neighbor. In the star case its center c has delta_c=2. These alternatives have a paper proof independent of the cubic-ten representative enumeration.

## Leaf-sum inequality

Write E=8I+J-A^2 for the seven-regular zero-codegree adjacency matrix. The deficit coupling of 2277 applies throughout this degree-five branch: each attached vertex of residual degree two has exactly one fixed E-neighbor, and each degree-one attached vertex has none. The target is constant on an involution orbit. Each target f receives exactly delta_f such orbits. Each orbit has support on two distinct residual orbits, because no residual vertex can meet both members of an attached orbit and every attached vertex has residual degree two.

Let T_fj count the degree-two attached orbits targeting f whose residual support contains j. Commutation gives

    (HY)_fj <= (YQ)_fj + T_fj.

The central-column equation of 2272 is exact:

    T_f0 = 1 + delta_f - deg_P(f).

Consequently the sum of T_fj over the four leaf labels is 2 delta_f - T_f0. Let a_f be the number of matched leaf labels belonging to Y_f. Summing the four leaf-column inequalities gives

    3 + deg_P(f) - sum_{g adjacent f} delta_g
      <= 4*1[f in M] + a_f + 2 delta_f - T_f0.

Here the left side is sum_{g adjacent f} (|Y_g|-1[g in M]); the quotient contributes four times the central miss plus one for every missed matched leaf label. Substitution yields, for each f in P,

    delta_f + sum_{g adjacent f} delta_g + a_f >= 4.       (L)

At t=0, a_f=0. Always 0<=a_f<=|Y_f|=2-delta_f for f in P.

## Matching P

In this case each P vertex has one P-neighbor; the two endpoints of H[M] have two P-neighbors and its other four vertices have one. Summing (L) over P therefore weights each delta by at most two. Write D_P=sum_{f in P}delta_f.

For t=0 the resulting left side is at most 2 sum delta=12, contradicting the required 16.

For t=1 the delta contribution is at most 2 sum delta=8, and sum_{f in P}a_f<=8-D_P. Hence 16<=16-D_P, forcing D_P=0. But 2274 proves that exactly two of the four attached neighbors of x have residual degree two. They belong to two distinct P groups, each with positive delta. Thus D_P>=2, a contradiction.

For t=2 the delta contribution is at most four and the a contribution at most eight. Again their total is less than 16.

## Star P at t=0

Let c be the star center and let P minus {c} be its three leaves. The center has delta_c=2. It has no neighbor in M, and every M vertex has precisely one neighbor among these three leaves. Sum (L) just over the three leaves. Since a=0, its left side is

    sum_{f != c} delta_f + 3 delta_c
      = sum_f delta_f + 2 delta_c = 6+4=10.

The required right side is 12, a contradiction.

## Star P at t=1 or t=2

Because delta_c=2, Y_c is empty. Also T_c0=1+2-3=0. Summing the leaf-column commutation inequalities at c thus gives

    sum_{f in P minus {c}} |Y_f| <= 2 delta_c = 4.

Therefore the three P leaves have total delta at least two. At t=2 this is impossible, since total delta is two and c already uses both units.

At t=1 total delta is four. Hence the P leaves have total delta exactly two, and every center in M has delta zero. Each M group is ordinary type 111 and fills every allowed internal/cross matching slot at every vertex. In particular, all six allowed cross-group slots at each vertex of B_c are full: the allowed groups are exactly the six groups in M, since c is adjacent in H to the three other P centers.

For u in B_c, nine-regularity now gives

    residual_degree(u) = 2 - internal_degree_Bc(u).

Thus its four residual-degree-two vertices have no internal neighbor; the two degree-one vertices must be paired by its internal matching. Every high vertex has c as its unique fixed E-neighbor, since the only missing fixed-center slot is its internal one.

Let u be the unique vertex of B_c adjacent to x. Such a vertex exists because c lies in P. If u has residual degree two, it contributes one to T_c0, contradicting T_c0=0. Therefore u has residual degree one, as does its involution partner u', which is adjacent to x'. They are the two degree-one vertices and hence are internally matched. The edges u-x-x'-u'-u form a C4, the final contradiction.

All t values and both structural alternatives are excluded. The proof uses only accepted structural and commutation lemmas; it has no finite enumeration, graph solver, or dependence on capped search outcomes. It is a paper proof, not Lean formalization. Residual degrees zero, one and four, and the other fixed-graph branches, remain outside this result.

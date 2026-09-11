# Excluding ten fixed vertices for an involution at N78

Assume G is a simple C4-free graph on78 vertices with minimum degree at least9 and a nonidentity involution fixing exactly ten vertices. Use accepted2223/2225: G is9regular; its fixed graph H is cubic; there are ten attached6-sets B_v and an unattached residual set R of size8. Write W for the union of the attached sets, of size60. Every vertex in W has exactly one fixed neighbor. The attached groups have types A/B/C as in2225. Let a be the number of typeA groups. Each typeA vertex has R-degree1; each typeB/C group has two vertices of R-degree2 and four of R-degree1. The involution acts freely on W and R.

Let M be G's adjacency matrix and E=8I+J-M^2. E is the adjacency matrix joining distinct vertices with no common G-neighbor: its diagonal is0 and all other entries are0or1 by C4-freeness. It is5regular, since8+78-81=5, and ME=EM. No C4-freeness assumption is made about E.

## 1. The residual graph is independent

Let Q be the symmetric binary4x4 residual quotient from2225, including diagonal0or1. Write d_j for its row sums, so0<=d_j<=4 and a=4+sum_j d_j. Each residual orbit has two vertices of residual degree d_j.

Count pairs of distinct vertices in R having a common G-neighbor. Fixed vertices contribute none, because R has no fixed neighbor. The attached sets contribute exactly2(10-a) such pairs: each typeB/C has two vertices with R-degree2, and all other attached vertices have R-degree1. Residual middle vertices contribute2*sum_j choose(d_j,2). These pairs are all distinct across middle vertices by C4-freeness. Hence the number of deficiency edges inside R is exactly

    e_E(R) = 28 - 2(10-a) - 2 sum_j choose(d_j,2).

There are exactly2a deficiency edges from R to the fixed set: each typeA group misses one residual2-orbit, and each typeB/C group meets every residual vertex. Since E is5regular, summing E-degrees on R gives

    e_E(R,W) = 40 - 2 e_E(R) - 2a
               = 2 sum_j d_j(d_j-4).

The left side is nonnegative and every term on the right is nonpositive. Therefore d_j is0or4 for every j, and e_E(R,W)=0. If any row of Q has degree4, all its entries are1; by symmetry all other rows have positive degree and must also have degree4. Then Q is the all-ones matrix, contrary to the2225 off-diagonal bound(Q^2)_jk<=2 (its entries would be4). Thus Q=0.

Consequently R is independent, a=4, and there are no E-edges between R and W. Each residual orbit j is missed by exactly one typeA fixed centre p_j; the four p_j are distinct and exhaust the typeA centres. In particular, each R vertex has exactly one fixed E-neighbor.

## 2. The four typeA fixed centres are independent in H

Let P be these four fixed centres and K the six other fixed centres. The fixed block of M^2 is H^2+6I: moved vertices have at most one fixed neighbor, so only the six attached neighbors contribute the extra diagonal entries. Thus the fixed block of E is

    E_FF = 2I+J-H^2.

It is3regular since H is cubic on ten vertices. Every fixed vertex therefore has exactly two moved E-neighbors. They form a single free involution2-orbit, denoted C_v.

For v in P, C_v is its missed residual orbit. For a typeB centre, C_v is the internally unmatched2-orbit in B_v: its vertices have no common G-neighbor with v and have R-degree2. For a typeC centre, C_v is the2-orbit in its deficient partner's attached set that misses a cross edge to B_v. The partner is nonadjacent to v in H, so these vertices have no common G-neighbor with v; they also have R-degree2. These exhaust the two moved E-neighbors in each case. Thus when v is in K, every vertex of C_v lies in W and has R-degree2.

For x in residual orbit j, compare ME and EM at entry(v,x). The W-middle contribution to ME is zero because E(R,W)=0. Among fixed middle vertices, only p_j is an E-neighbor of x. Fixed middle vertices contribute zero to EM because x has no fixed G-neighbor. Therefore

    H(v,p_j) = |N_G(x) intersect C_v|.

If v is in P, C_v lies in the independent set R, so the right side is zero. Hence P is independent in H. If v is in K, sum over one representative x from each of the four residual orbits. Equivariance and the equal orbit sizes show that the right side sums to the R-degree of a vertex of C_v, namely2. Thus every v in K has exactly two H-neighbors in P and one in K. In particular H[K] is a matching.

## 3. Six equitable vertex classes

Let S be the twelve vertices of W with R-degree2, two in each group centred in K. Let T=W\S be the remaining48 vertices with R-degree1. Split T into T_P (the24 vertices attached to P) and T_K (the24 others). The six nonempty classes(P,K,R,S,T_P,T_K) have sizes(4,6,8,12,24,24).

Since E(R,W)=0, every pair x in W and z in R has exactly one common G-neighbor. Summing over all eight z shows

    sum_{y in N_G(x) intersect W} degree_R(y) = 8.

Neither fixed nor residual middle vertices contribute, since R has no fixed neighbors and is independent. Now degree_W(x)=8-degree_R(x) and degree_R(y)=1+1_S(y). Hence degree_S(x)=degree_R(x): every S vertex has two S-neighbors, and every T vertex has one.

For r in R, its E-degree inside R is4: it has one fixed E-neighbor and none in W. Of the other seven R vertices, exactly three therefore share a G-neighbor with r. Such common neighbors are precisely the S-neighbors of r, each supplying one other R endpoint; endpoints are distinct by C4-freeness. Thus every R vertex has three S-neighbors. It also has one G-neighbor in each of the three typeA groups not missing its orbit, so three neighbors in T_P, and the remaining three neighbors are in T_K.

For a vertex in S or T_K, its fixed centre belongs to K and has exactly two neighbors in P. Those two attached cross blocks are forbidden. The other two typeA groups are nonadjacent to its centre and have zero cross deficit, hence each supplies one neighbor. Thus every vertex in S or T_K has exactly two T_P-neighbors.

For a vertex in T_P, its own attached group has a full internal matching, supplying one T_P-neighbor. The other three centres in P are nonadjacent and their cross matchings are perfect, supplying three more. Its T_P-degree is therefore4. Combining these facts with degree9 gives the exact quotient in the displayed class order:

    [0 3 0 0 6 0]
    [2 1 0 2 0 4]
    [0 0 0 3 3 3]
    [0 1 2 2 2 2]
    [1 0 1 1 4 2]
    [0 1 1 1 2 4].

For clarity, an S vertex has fixed degree1, R-degree2, S-degree2 and T_P-degree2, leaving T_K-degree2. A T_K vertex has fixed degree1, R-degree1, S-degree1 and T_P-degree2, leaving T_K-degree4. A T_P vertex has fixed degree1, R-degree1, S-degree1 and T_P-degree4, leaving T_K-degree2. The fixed-centre rows follow from H and the attached group sizes.

## 4. Thirteen two-step paths into twelve vertices

Take x in T_K. Its neighbors comprise one vertex in K, one in R, one in S, two in T_P and four in T_K. Their respective S-degrees are2,3,2,1,1. Thus x has exactly

    1*2 + 1*3 + 1*2 + 2*1 + 4*1 = 13

two-step walks ending in S. But x is outside S and S has only twelve vertices. C4-freeness allows at most one common neighbor of x and each vertex of S, so at most twelve such walks. This is a contradiction.

Therefore the N78/F10 involution case is impossible. Combined with accepted2220 (an involution fixes an even number at most10), every nonidentity involution of a hypothetical N78 graph fixes at most8 vertices. No N80 case is excluded by this argument, and this is not a global N78 graph exclusion or a solution of Erdős85. The proof uses paper identities and small exact arithmetic, not a graph search or a full Lean formalization.

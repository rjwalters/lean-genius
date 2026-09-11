# Necessary matching form and eigenvalues for N78/F6

Assume a C4-free graph G on78 vertices with minimum degree9 and an involution whose fixed graph consists of three disjoint edges. Accepted2220 gives nine-regularity, six disjoint attached groups B_v of size8, their union W of size48, and an unattached set R of size24. The fixed set F has size6.

For x in B_v, its eight moved neighbors include at most one in its own group, none in the group of v's fixed partner, and at most one in each of the other four groups. Thus x has at least three R-neighbors. The eight lower bounds sum to24, while every R vertex meets B_v at most once. Equality is forced. Each B_v has a full internal matching, every allowed cross block is a perfect matching, each x in W has R-degree3, and every R vertex meets all six B groups exactly once. Hence G[R] is cubic.

Let M be the adjacency matrix of G and E=8I+J-M^2. E is a simple five-regular graph joining distinct pairs with no common G-neighbor, and ME=EM. Any two distinct fixed vertices have no common G-neighbor, so E[F]=K6; its vertices have no moved E-neighbors.

For moved x and fixed v, commutation gives

    |N_E(x) intersect B_v| = (ME)_(x,v)
                           = 1 if x lies in B_w with w different from v,
                             0 otherwise.

The fixed partner of v contributes nothing to EM because E has no fixed--moved edges. On the other side E[F]=K6 counts x's unique fixed G-neighbor, if it has one. Therefore there are no E-edges between R and W, no E-edges within a B group, and E between any two distinct B groups is a perfect matching. In particular E[R] is five-regular; no C4-freeness of E is asserted.

The G partition (F,W,R) is equitable, with sizes(6,48,24) and quotient

    [1 8 0]
    [1 5 3]
    [0 6 3].

Its characteristic polynomial is (lambda-9)(lambda^2-3), so G has adjacency eigenvalues sqrt(3) and -sqrt(3), each at least once.

There are also adjacency eigenvalues3 and -3 each of multiplicity at least5. Let V be the five-dimensional space of real vectors supported on F with coordinate sum zero. For f in V, Jf=0 and Ef=-f, hence M^2 f=9f. The vectors Mf+3f and Mf-3f are respective eigenvectors of eigenvalue3 and -3. Each of these two maps is injective on V: its W-coordinate at any vertex in B_v equals f(v), so a zero image forces every f(v)=0. Thus both eigenspaces have dimension at least5.

These are necessary graph and spectral constraints, not a contradiction, graph existence result, or full matching-case exclusion. No search or Lean formalization is used.

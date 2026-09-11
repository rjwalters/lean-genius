# Necessary form for the N78/F6 triangle with leaves

Assume a C4-free graph G on78 vertices with minimum degree9 and an involution fixing six vertices. Suppose the fixed graph consists of a triangle a_1,a_2,a_3 with a leaf b_i attached to each a_i. Accepted2220 gives nine-regularity, disjoint attached groups A_i of size6 at a_i and B_i of size8 at b_i, and an unattached residual set R of size30. All moved sets carry a free involution. We derive necessary structure only.

## Cubic-centre saturation

For x in A_i, its eight moved neighbors can include at most one in A_i, none in either other A group or B_i (their centres are adjacent), and at most one in each B_j for j different from i. Thus at least five neighbors lie in R. The six lower bounds total30, and every R vertex meets A_i at most once. Equality holds throughout. Each A_i induces a perfect matching; A_i--B_j has six edges forming an injection covering A_i for i different from j; every R vertex meets each A_i exactly once; and every A_i vertex has exactly five R-neighbors. The forbidden blocks above are empty.

For each i, partition R into six classes R_x=N(x) intersect R, x in A_i, each of size5. Every residual vertex has at most one residual neighbor in each class, including its own. If x,y form an internal A_i matching edge, no edge joins R_x to R_y, since it would close a C4 through x,y. Consequently every residual vertex has at most five residual neighbors. Within each class the residual graph is a matching on five vertices, so at least one vertex has no neighbor inside its own class. This holds in each of the three partitions.

## Three leaf-group types

Write m_i for the number of internal matching edges in B_i, so m_i<=4. Each cross B_i--B_j block is a matching; let its deficit be delta_ij=8-e(B_i,B_j), a nonnegative even number. Evenness follows because its edges are paired by the free involution, which preserves the two distinct groups. Let D_i be the sum of the two deficits at B_i, and let e_i count B_i--R incidences.

The two allowed A groups send exactly twelve edges to B_i. Summing the eight moved-neighbor degrees over B_i gives

    64 = 2m_i + 12 + (16-D_i) + e_i,
    e_i = 36-2m_i+D_i.

Each R vertex meets B_i at most once, so e_i<=30. Internal unmatched vertices form free involution orbits, and all quantities above are even. Thus exactly three parameter types are possible:

* type A: m_i=4, D_i=0, e_i=28;
* type B: m_i=3, D_i=0, e_i=30;
* type C: m_i=4, D_i=2, e_i=30.

Positive cross deficits therefore form a matching among the three leaf groups, with deficit2 on its sole possible edge and both endpoints of type C. A type A group misses exactly one residual involution orbit. Types B and C meet every residual vertex exactly once.

For each B_i, each of the other two A groups misses a two-vertex orbit in B_i. These two missing orbits may coincide or be disjoint. If alpha(x) counts the A-neighbors of x in B_i, then alpha(x) is0,1,or2. Let epsilon(x) be1 when x is either internally unmatched (type B) or unmatched toward its deficient B partner (type C), and0 otherwise. In either non-A type exactly two vertices have epsilon1. Counting x's own internal and two cross-B slots gives

    degree_R(x)=5-alpha(x)+epsilon(x).

## Residual degrees and missing incidences

A residual vertex r has exactly three A-neighbors and at most one neighbor in each B group. If h(r) is the number of B groups it misses, its residual degree is3+h(r). The partition bound above implies h(r)<=2, so residual degrees are3,4,or5.

Let t be the number of leaf groups of types B or C. The other3-t groups each miss two residual vertices, so

    sum_r h(r)=6-2t,
    sum_r degree_R(r)=96-2t,
    |E(G[R])|=48-t.

In particular no residual vertex misses all three leaf groups. These constraints preserve all remaining possibilities and do not assert a residual graph exists or exclude the triangle-with-leaves case. No graph search or Lean formalization is used.

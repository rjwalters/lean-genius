# Eight-vertex residual system for an N78 involution with ten fixed vertices

Assume the hypotheses and conclusion proposed in2223: N78, a nonidentity involution with ten fixed vertices, and cubic fixed induced graph H. There are ten disjoint attached sets B_v of size6, and an unattached residual set R of size8. Every moved vertex has at most one fixed neighbor. The involution acts freely on each B_v and R, giving three2-orbits per attached group and four residual2-orbits.

## Three attached-group types

There are no edges B_u--B_v when uv is an edge of H. For a nonedge uv, the cross graph is a matching of size at most6. It is invariant under the involution, which preserves the two groups individually, so its edge count is even. Define its deficit d_uv=6-e(B_u,B_v), an even nonnegative integer. Let D_v=sum_{u nonadjacent to v, u!=v} d_uv. There are six such other groups.

The induced graph on B_v is a matching; write m_v for its number of edges, at most3. The total moved-degree on B_v is48. Subtracting the2m_v internal incidences and the36-D_v cross incidences gives

    e(B_v,R)=12-2m_v+D_v <=8.

The upper bound holds because each R vertex meets B_v at most once. Thus exactly three parameter types are possible:

| Type | m_v | D_v | e(B_v,R) |
|---|---:|---:|---:|
| A |3|0|6|
| B |2|0|8|
| C |3|2|8|

All nonzero cross deficits therefore equal2 and form a matching among the nonedges of H. Their endpoints are precisely typeC centres. In particular the number of typeC centres is even.

More precisely, for x in B_v let e_x in{0,1} be its internal degree and let delta_x count its missing neighbors among the six allowed other attached groups. Then

    degree_R(x)=2-e_x+delta_x.

In typeA, every x has internal degree1 and delta_x=0, so R-degree1. The six used R vertices form three residual orbits; exactly one residual2-orbit is missed.

In typeB, exactly two vertices of B_v are unmatched internally. They form one free2-orbit and have R-degree2; the other four have R-degree1. In typeC, exactly two vertices miss a cross edge to the deficient partner group. They form one free2-orbit and have R-degree2; the other four have R-degree1. Both types cover every R vertex exactly once, since their R-incidence count is8.

A block between an attached2-orbit and a residual2-orbit has degree at most1, since degree2 would be K2,2. Thus typeA assigns three distinct residual orbits to the three attached labels and misses one; typeB/C assigns all four residual orbits to three labels, with multiplicities2,1,1.

## Four-orbit residual quotient

Let Q be the symmetric4x4 quotient of G[R]. Its diagonal entries are0or1; cross entries are0or1, again by K2,2 exclusion. Put A_count=#typeA centres. For residual orbit j, let m_j be the number of typeA groups missing j. The other10-m_j attached groups each supply one neighbor to each vertex in j. Therefore

    sum_k Q_jk = m_j-1,      sum_j m_j=A_count.

In particular m_j>=1, A_count>=4, and

    sum_jk Q_jk=A_count-4.

The last quantity also equals the number of edges of G[R], since each orbit has size2. The equality includes diagonal1, whose two vertices supply one internal edge. Hence G[R] has at most6 edges.

For distinct residual orbits j,k, let c_jk be the number of typeB/C attached groups assigning them the same attached label. TypeA contributes no repeated label. Then a vertex in j has exactly c_jk attached-middle two-step walks into k, and (Q²)_jk residual-middle walks. Each of the two endpoints in k has codegree at most1, so

    (Q²)_jk+c_jk<=2.

Every typeB/C group contributes exactly one repeated-label pair; consequently

    sum_{j<k} c_jk=10-A_count.

Two residual orbits with diagonal1 cannot have a positive cross entry: their two internal edges and either cross matching form a C4. These conditions are necessary only. They do not choose H, the involution edge phases, attached matchings, or a graph realization.

No enumeration is performed here beyond the three local(m,D) possibilities. The result is conditional on2223 and concerns N78/F10 only; it does not exclude this involution case or settle Erdős85.

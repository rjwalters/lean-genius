# N78/F6 fixed star is impossible

Assume the six fixed vertices induce K1,5, with central fixed vertex v. Let B_v be its four moved neighbors. Let R be the28 moved vertices with no fixed neighbor; this follows from S=10 and R=78-60+10. Each of the five fixed leaves has an attached8-set, and these six attached sets are disjoint.

Every x in B_v has exactly eight moved neighbors. It has no neighbor in a leaf's attached set: such an edge would close a C4 through the adjacent fixed centres. It has at most one neighbor in B_v, since two would have both x and v as common neighbors. Hence x has at least seven R-neighbors. Each r in R has at most one B_v-neighbor, again by the C4 bound with fixed centre v. The four lower bounds sum to28=|R|, so all are equalities. Thus B_v induces a perfect matching, every x has exactly seven R-neighbors, and every r has exactly one B_v-neighbor.

Partition R into four sets R_x=N(x) intersect R, each of size seven. A residual vertex r has at most one neighbor in each R_x, since two would have both r and x as common neighbors. If x and y are matched inside B_v, there is no R_x--R_y edge: one would close a C4 r-x-y-s-r. Therefore each r in R_x has at most three residual neighbors, one in its own class and one in each of the two classes other than the matched partner.

On the other hand r has no fixed neighbor, exactly one B_v-neighbor, and at most one neighbor in each of the five leaf-attached sets. Its total degree is nine, so it has at least three residual neighbors. Both bounds are equalities. In particular every r in R_x has exactly one neighbor within R_x. Thus each of the four seven-vertex induced graphs G[R_x] is1regular, impossible because a matching covers an even number of vertices.

This excludes the fixed-star subcase atN78 only. It does not apply directly toN80, where the residual set has30 vertices and the initial capacity is not tight. The argument uses no graph enumeration and no new assumption about the residual involution quotient.

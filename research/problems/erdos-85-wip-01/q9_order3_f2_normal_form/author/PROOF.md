# Remaining N80 order3 case: two fixed vertices

Assume G is C4-free, has80 vertices and minimum degree9, and tau is an order3 automorphism. Near-Moore regularity gives9-regularity. Accepted2176 and2214 give exactly two fixed vertices u,v, an independent fixed set, and exactly three triangles through each fixed vertex.

Let A=N(u), B=N(v). Each has size9, is tau-invariant and consists of three free3-orbits. They are disjoint: a common neighbour would have a free orbit of three common neighbours, violating codegree<=1. Each induced graph G[A],G[B] is a matching of three edges plus three isolated vertices. Thus in each attached set two of its3-orbits are joined by a perfect matching; the third is internally isolated.

Let R be the60 vertices outside {u,v},A,B. Every vertex of R has at most one neighbour in A and at most one in B, by codegree with u,v. The same argument says the cross graph A--B is a matching. Let m be its edge count, and for x in A let e_x in{0,1} be its internal degree, c_x in{0,1} its degree into B. It has8-e_x-c_x neighbours in R. Since sum_A e_x=6, the A--R edge count is66-m, at most60. Hence6<=m<=9. Tau acts freely on A--B edges (the two invariant sides prevent endpoint exchange), so3 divides m. Therefore m is6 or9. The same formula applies from B.

## Six cross edges

There are60 A--R edges and60 B--R edges. The per-vertex upper bounds force every R vertex to have exactly one neighbour in each attached set. Thus G[R] is7-regular.

For each of A and B independently, the cross matching misses one of its three3-orbits. If that missing orbit is the internally isolated one, the attached vertices have R-cell sizes8 at three vertices and6 at six vertices. If it is one of the two internally matched orbits, the sizes are7 at six vertices and6 at three vertices. In either case their nine R-neighbourhoods partition R.

## Nine cross edges

The cross matching is perfect. There are57 A--R edges, so exactly three R vertices have no A neighbour; these form one free tau-orbit. Similarly exactly one residual orbit has no B neighbour. These two missing orbits are either identical or disjoint.

If identical, G[R] has57 vertices of degree7 and3 of degree9. If disjoint, it has54 vertices of degree7 and6 of degree8. For either attached set, its R-neighbourhoods consist of three cells of size7 (the internally isolated orbit) and six cells of size6, partitioning all but its missing residual3-orbit.

In every case cells within either family are disjoint. A cell from A and a cell from B intersect in at most one vertex, or two vertices would have two common attached neighbours. Two distinct vertices in a single cell cannot have a common neighbour inside R, since they already share their indexing attached vertex.

## Twenty-orbit residual quotient

R consists of20 free3-orbits. Let Q_ij be the number of neighbours in orbit j of a vertex in orbit i, inside R. Then Q is symmetric, integral and nonnegative; Q_ii is0 or2, and Q_ij<=2 for i!=j (a complete3x3 bipartite graph contains a C4).

Let a_i,b_i indicate whether orbit i has a neighbour in A,B. If present, these neighbours lie in a single attached3-orbit and form a perfect matching to it. Row i of Q has sum9-a_i-b_i. Counting two-step walks to its own residual orbit gives

 sum_j Q_ij^2 + a_i+b_i <=11.

Indeed the total includes9 return walks and at most one walk to each of the two other vertices of the residual orbit. Each present attached group contributes exactly one return walk via its matching. Consequently sum_j Q_ij(Q_ij-1)<=2: each row contains at most one entry2, counting the diagonal.

For i!=j, define h_ij as the number of attached groups in which both residual orbits have neighbours in the same attached3-orbit. The matching composition gives exactly one two-step walk from a vertex of i into j per such group. Thus

 (Q^2)_ij + h_ij <=3.

These are necessary quotient and partition conditions. No enumeration has been run, and no residual graph, order3 action, or whole N80 graph has been excluded by this note.

# Necessary quotient for an elementary order9 action at N78

Assume the graph hypotheses of review2207 and its surviving P=C3 x C3 case: two vertex orbits A,B of size3 and eight regular P-orbits X_i of size9. The stabilizers of A and B are distinct order3 subgroups L_A,L_B. This is conditional on2207 and uses accepted2176/2179. No enumeration or exclusion is asserted.

A and B are independent, since each is the fixed set of an order3 element. There are no A--B edges: the P-action on A x B is transitive (the two stabilizers intersect trivially), so any edge forces K3,3, containing a C4.

A vertex of X_i has at most one neighbour in A. Indeed its number t of neighbours in A is constant on X_i, and if t>=2 the nine vertices supply at least9 common-neighbour incidences to the three unordered pairs of A, violating codegree<=1. Similarly for B. Write these numbers a_i,b_i in{0,1}. By counting edges, each A vertex has3a_i neighbours in X_i. Degree9 gives sum a_i=sum b_i=3.

Apply2179 to fixed set A. Every B vertex is unattached to A and therefore has exactly one neighbour in each N(u), u in A. Counting these three paths from a B vertex into A through the X_i gives3=sum_i 3a_i b_i. Thus sum a_i b_i=1. Relabel the eight free orbits so that

 a=(1,1,1,0,0,0,0,0), b=(1,0,0,1,1,0,0,0).

Let D_ij count neighbours in X_j of a vertex in X_i. These counts are constant by equivariance. D is symmetric and nonnegative integral, with row sums9-a_i-b_i. For i!=j, D_ij<=3: viewing the bipartite graph as a subset S of the regular group P, C4-freeness makes all ordered nonzero differences of elements of S distinct, so |S|(|S|-1)<=8. Each D_ii is0 or2: its Cayley connection set is inverse-closed; two distinct inverse pairs contain independent elements s,t in C3 x C3, yielding the four distinct vertices0,s,s+t,t of a C4. A single inverse pair is allowed by this local test and gives three triangles.

For a vertex x in X_i, the number of length2 walks ending in X_j is

 (D^2)_ij + 3a_i a_j + 3b_i b_j.

For i!=j this is at most9, since each of the nine endpoints has codegree at most1 with x. For i=j there are9 return walks and at most8 other endpoints, giving

 sum_j D_ij^2 + 3(a_i+b_i) <=17.

Equivalently, sum_j D_ij(D_ij-1)<=8-2(a_i+b_i).

There are also saturation equalities. Under L_A, each N(u), u in A, splits into three3-orbits, one within each X_i with a_i=1. The induced matching of three edges joins exactly two of these triples and leaves the third isolated. Equivariance under P makes this choice uniform over the three u. Hence there is a vector e^A supported on{0,1,2}, with exactly two entries1 and one0, such that

 sum_i a_i D_ji = 3 if a_j=0, and 2+e^A_j if a_j=1.

For a_j=0 this is2179's one neighbour in each N(u). For a_j=1, a vertex has one neighbour in each of the other two attached sets, plus its internal matching degree e^A_j. The same argument gives e^B supported on{0,3,4}, with exactly two entries1, and

 sum_i b_i D_ji = 3 if b_j=0, and 2+e^B_j if b_j=1.

All constraints above are necessary only. They discard group-valued edge phases and finer codegree conditions, and do not establish a graph realization or rule out P. The full N78 problem also includes graphs without this elementary order9 action.

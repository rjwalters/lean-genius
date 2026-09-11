# Residual pattern 01133 is impossible

Assume a C4-free residual graph R on ten vertices with a fixed-point-free involution and orbit degrees 0,1,1,3,3. Let C be the four cubic vertices, the union of the two degree-three involution orbits. The other vertices consist of two isolated vertices and four leaves.

Between two free involution pairs there can be at most one matching: if both invariant matchings were present, they would form K2,2, a C4. Within each pair there is at most its partner edge. Thus C has at most four edges. Equality would require both partner edges and one cross matching. Those four edges themselves form a C4. Consequently e(R[C])<=3.

The cubic vertices have total residual degree twelve. At most six incidences are internal to C. Every external edge from C must meet one of the four leaves, contributing at most four more incidences. Isolated vertices contribute none. Thus their degree sum is at most 6+4=10, contradicting twelve.

This directly excludes 01133, independently of the attached-vertex identities and of any pending 11123 result. It uses no finite search, solver, or assumption on realization of other patterns. The larger N80 problem remains open.

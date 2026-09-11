# A cubic C4-free graph on ten vertices has no free involution

Suppose a simple cubic C4-free graph has a fixed-point-free involution. Its ten vertices split into five two-vertex orbits. Let Q be the corresponding symmetric quotient matrix. Every cross entry is at most one, because entry two gives K2,2 between two orbits. Each diagonal is zero or one, according as the orbit is independent or an edge. Every row sum is three.

For distinct orbit indices i,j, (Q²)_ij<=2. Indeed for a vertex x in orbit i, this entry counts length-two walks to both vertices of orbit j. Each endpoint is distinct from x and permits at most one common neighbor by C4-freeness. Also two looped quotient vertices cannot be adjacent: the two internal edges and the cross matching would give C4.

The sum of all Q entries is fifteen, while the off-diagonal sum is even. Hence the number of diagonal ones is odd: one, three, or five.

If all five diagonals are one, every quotient vertex needs two off-diagonal neighbors, but every cross edge between looped vertices is forbidden. Impossible.

If three diagonals are one, those three quotient vertices form an independent set in the off-diagonal graph and each needs two neighbors. They must each join both remaining unlooped vertices. Those two rows consequently have three common neighbors, so their Q² entry is at least three, impossible.

If only one diagonal is one, call that quotient vertex L and its two off-diagonal neighbors U,V. Let W,Z be the remaining vertices. W and Z have no loop, are not adjacent to L, and have row degree three. They must therefore join every other vertex among U,V,W,Z. It follows that U and V both have neighbors L,W,Z, again making their Q² entry at least three. Impossible.

All cases contradict C4-freeness. This proof is independent of any classification of cubic graphs or spectral assumption. It does not exclude cubic C4-free graphs on ten vertices themselves, only fixed-point-free involutions on them.

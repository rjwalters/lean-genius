# Excluding order16 vertex-fixing two-groups at N78

Assume a simple C4-free graph G on78 vertices with minimum degree nine. Conditional on2257,2260,2261, no two-subgroup of order16 fixes a vertex. Consequently every vertex-fixing two-subgroup has order at most eight, and every two-subgroup of Aut(G) has order at most16.

Suppose H of order16 fixes v. By2260 it fixes a neighbor x, acts faithfully and transitively on each eight-element set Omega_v=N(v) minus{x} and Omega_x=N(x) minus{v}, and vx lies in no triangle. The involutions fixing points in these two actions form disjoint conjugacy classes T_v,T_x of size four. By2261, H is dihedral of order16. Write H=<r,t>, where r has order eight, and let z=r^4 be its central involution. The eight reflections are precisely the union T_v union T_x: dihedral16 has exactly eight noncentral involutions, and the two classes already supply eight. The action of z on each Omega is free, by2260.

## The internal matching forces six fixed vertices for every reflection

The induced graph on N(v) has maximum degree one. If y had two distinct neighbors a,b inside N(v), the vertices v,a,y,b would form C4. Since x has no neighbor in Omega_v and H is transitive on Omega_v, its internal degree on Omega_v is constant, either zero or one.

It cannot be zero. In that case N(v) is independent. Each of its nine vertices would have eight other neighbors outside {v} union N(v), and these nine eight-element sets would be pairwise disjoint by C4-freeness. This would require1+9+72=82 vertices, greater than78. Thus Omega_v induces a perfect matching, of four edges. The same proof applies at x.

Take a reflection h in T_v. It fixes exactly two points a,b of Omega_v. Its action preserves the internal perfect matching, so the matching partner of a is also fixed by h. It must be b. Thus v,a,b form a triangle in the fixed graph of h, and x is a further fixed neighbor of v. The fixed set of h has at most six vertices by2257's premises. Each of a and b must have odd fixed degree, because the total degree is nine and h pairs all nonfixed neighbors. Their two neighbors in the triangle therefore require an additional fixed neighbor each. Neither can use x, since vx lies in no triangle. These additional neighbors are distinct, since a shared one would form C4 together with a,v,b. Hence h has at least six fixed vertices, and therefore exactly six. Its fixed graph is the triangle v,a,b with pendant leaves x,a',b', by the accepted six-fixed classification.

Since z commutes with h, it permutes this six-vertex fixed graph. It fixes v and x. It swaps a and b, since both are in Omega_v and z is free there. It therefore also swaps their unique pendant leaves a',b'. Consequently Fix(h) intersects Fix(z) in exactly {v,x}.

For h in T_x the same argument holds with v,x interchanged. Thus every one of the eight reflections fixes exactly four vertices outside Fix(z).

## Burnside contradiction

By accepted2253, the fourth power of an order-eight automorphism fixes exactly six vertices. Therefore |Fix(z)|=6 and Y=V(G) minus Fix(z) has size72. It is H-invariant, since z is central.

Every nonidentity rotation r^j has z as a power: in a cyclic group of order eight, every nontrivial subgroup contains its unique involution. Hence any vertex fixed by r^j is fixed by z, and no nonidentity rotation fixes a point of Y. Each of the eight reflections fixes exactly four points of Y, as proved above. The identity fixes all72 points. Burnside's orbit-counting formula would give

    number of H-orbits on Y = (72 + 8*4)/16 = 104/16,

which is not an integer. This is impossible.

Thus H cannot exist. The accepted bound16 on vertex-fixing two-subgroups from2257 drops to eight, because their orders are powers of two. For any two-subgroup P acting on78 vertices there is an orbit of size one or two (otherwise all orbit sizes are multiples of four). Its stabilizer has order at most eight, giving |P|<=16 by orbit-stabilizer.

This excludes the order16 vertex-stabilizer equality case and strengthens the whole two-subgroup bound. It does not exclude two-subgroups of order16 acting without a fixed vertex, eliminate all automorphisms, or solve the graph problem. No graph search, group classification table, or Lean formalization is used. Both the equality-form premises and this paper argument require independent review.

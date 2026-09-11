# No cyclic order-eight kernel in the N78 three-orbit case

First prove a scoped cyclic-action obstruction. There is no cyclic automorphism subgroup C of order24 whose subgroup K of order eight fixes six vertices pointwise in a C4-free nine-regular graph on78 vertices.

Let z be the involution in K. By2253, since z is the fourth power of an order-eight element, it fixes exactly six vertices F inducing3K2. The six vertices fixed pointwise by K are therefore precisely F. Every vertex outside F has a free K-orbit: otherwise its stabilizer in the cyclic eight-group contains z, contradicting the definition of F.

Let rho be the order-three element of C. A C-orbit outside F has size eight or24, because its K-orbit has size eight. An eight-orbit would have an order-three stabilizer; since C is abelian, rho would fix the entire eight-orbit. This contradicts the accepted2176 bound of at most three fixed vertices for an order-three automorphism atN78. Hence the complement of F consists of three free24-orbits.

On F the C-action factors through C/K of order three. The element rho has no fixed vertex there: if it fixed a centre, it would also fix its unique matching partner in G[F], whereas2176 says its fixed set is independent. Thus F consists of two C-orbits F_1,F_2 of size three. Its invariant matching joins the two orbits: within either odd three-orbit an invariant matching has degree zero, since degree one would give an odd sum of degrees.

Apply the accepted2245 matching form to z. The48 attached vertices W have unique F-neighbors and split into six8-sets B_f; the remaining24 vertices R have no F-neighbor. All these sets are invariant under C as families. Since all complement orbits have size24, W is two free24-orbits and R is the third. The map W->F sending a vertex to its unique F-neighbor is equivariant. Each W orbit maps onto one F_i. The union of the three B_f over each F_i has size24, so it is exactly one W orbit, denoted W_i.

The induced degree of G[W_i] is three: each vertex has one internal neighbor in its own B_f and one in each of the other two B-groups indexed by F_i, by the full matching saturation2245. No two centres in F_i are matching partners, so both cross blocks are allowed. There are no other vertices in W_i.

A free transitive cyclic action of order24 identifies G[W_i] with a Cayley graph of Z/24 on an inverse-closed three-element set S not containing zero. Since this cyclic group has exactly one nonzero self-inverse element, S must equal{12,s,-s}, with s nonzero and not12. The four distinct vertices0,12,12+s,s then form a C4: their successive differences are12,s,12,-s modulo24. This contradicts C4-freeness and proves the scoped obstruction.

Now assume the three-orbit case2264/2268 and suppose its kernel K on F is cyclic of order eight. Conjugation by A=Aut(G), of order48, acts on K through Aut(C8), which has order four (the four odd units modulo eight). Thus the centralizer C_A(K), the kernel of this conjugation action, has order divisible by three. Cauchy's theorem supplies an element rho of order three in it. It commutes with K and intersects K trivially, so together they generate a cyclic subgroup of order24. The subgroup K fixes F pointwise by its definition as action kernel. The scoped obstruction applies, yielding a contradiction.

Therefore an order-eight kernel in this three-orbit case cannot be cyclic. This does not exclude kernels of order two or four, noncyclic kernels of order eight, all order24 automorphisms, or the entire N78 graph case. The proof is paper group action and Cayley graph reasoning, with no search or Lean formalization.

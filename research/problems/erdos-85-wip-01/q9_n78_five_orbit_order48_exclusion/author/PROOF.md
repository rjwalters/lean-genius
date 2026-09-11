# No order48 automorphism group with five vertex orbits

Let G be a simple C4-free nine-regular graph on78 vertices, A=Aut(G), with |A|=48 and exactly five vertex orbits. The complete quotient reduction submitted2335, combined there with accepted2332, leaves only sizes F6,B12,C12,U24,V24. The conclusion of this packet is conditional on acceptance of2335 until that review passes. Its twelve saved quotients fall into the two cases below, checked directly in quotient-cover.json. No other quotient is omitted.

We use accepted2257: each nonidentity involution fixes at most six vertices; at a fixed vertex it fixes one or three neighbors; if it fixes six vertices the induced fixed graph is either3K2 or a triangle with one pendant leaf at each triangle vertex.

## Case I: F attaches only to U and V (eight quotients)

F induces3K2. Each F vertex has four U and four V neighbors, every U/V vertex has a unique F neighbor, and B,C have no F neighbors. The proof of accepted2317 uses only these properties, not transitivity or size of the remaining unattached vertices. We spell out its local argument to make the reuse explicit.

For matched f,f' in F, H=A_f=A_f' has order8 and is transitive on each of U_f,V_f,U_f',V_f', all four-point sets. Indeed transitivity of A on U or V and uniqueness of the F neighbor force any element taking two members of one fiber to fix its center. Every involution of H already fixes f' as a neighbor of f, so it fixes zero or two of the remaining eight neighbors, and likewise at f'.

Each four-point action has an order2 stabilizer. Abelian H or quaternion H would have a central involution fixing an entire four-point fiber, impossible. Thus H is dihedral of order8. Fiber stabilizers are reflections, since the central involution would again fix four points. A reflection fixes two points in a four-point action precisely when its conjugacy class is the stabilizer class. The two fibers at either center must use distinct reflection classes, since using the same class would give four fixed attached neighbors. Consequently any reflection fixes two attached neighbors at f and two at f'. These four are distinct by unique F attachment. Together with f,f', these are exactly six fixed vertices. Both f and f' are adjacent cubic vertices in the fixed graph, but have no common G-neighbor: F is a matching and every outside vertex has at mostone F neighbor. This contradicts both allowed fixed graphs. This is the2317 argument without any assumption on B,C beyond their lack of F neighbors.

## Case II: F attaches to B12 and U24 (four quotients up to labels)

F again induces3K2. Each B vertex has exactly two F neighbors; each F vertex has four B neighbors. Relabel B/C and U/V as necessary. Map each b in B to its unordered pair of F neighbors. This map is injective: two different B vertices with the same pair would form a C4. It is A-equivariant.

Let K be the kernel of A's action on F. Every element of K fixes B pointwise by this injection. Also K is a subgroup of A_f, of order8. If K were nontrivial, Cauchy's theorem would give an involution in K, fixing all18 vertices of F union B, contradicting the bound six. Hence K is trivial.

The faithful action embeds A into Aut(G[F]), the full group preserving a matching of three pairs. That group has order2^3*3!=48, so the image is the entire matching-preserving group. Its action on unordered pairs of F has exactly two orbits: the three matching pairs, and the twelve pairs from distinct matching edges. The image of B is an invariant subset of size12, and therefore consists exactly of the twelve nonmatching pairs.

Take the element of A inducing the permutation swapping the two endpoints of one matching edge and fixing the other four F vertices. Faithfulness makes this element an involution. Among its four fixed F vertices, four unordered pairs are nonmatching (choose(4,2)-2=4). Their unique B preimages are fixed as well. Thus this involution fixes at least4+4=8 vertices, contradicting2257.

Both cases are impossible. Once2335 is accepted, any five-orbit candidate must have automorphism group order24, with sizes(3,3,24,24,24) or(6,12,12,24,24). We do not exclude either order24 case, six or more orbits, all N78 graphs, N80, or Erdős85. No full graph search or Lean formalization is used.

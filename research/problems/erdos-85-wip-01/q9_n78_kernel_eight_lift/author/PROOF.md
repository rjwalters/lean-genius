# Order-eight kernels force cubic Cayley graphs on24 vertices

Assume the N78 three-orbit hypotheses2264/2268, and let K be the kernel of A=Aut(G) acting on the six-point matching orbit F. Suppose |K|=8. Then K fixes F pointwise and acts freely outside F. Choose an order-three element rho of A by Cauchy's theorem. Since K is normal, J=<K,rho>=K semidirect <rho> has order24.

The J action on F factors through the order-three quotient. The element rho cannot fix a vertex of F, since it would also fix its matching partner, contradicting the independent fixed set in2176. Thus F consists of two J-orbits of size three, joined by the matching.

Every J-orbit outside F has size eight or24, because it contains a free K-orbit of size eight and its size divides24. Let a,b be the numbers of these two types. Then8a+24b=72, so a is a multiple of three. Each eight-point J-orbit is rho-invariant, and rho has at least two fixed points on it: its cycle sizes are one or three and eight is congruent to two modulo three. Accepted2176 bounds rho's total number of fixed vertices atN78 by three. Therefore2a<=3, and a=0. The complement of F is precisely three free J-orbits of size24.

Any involution of K fixes exactly F, by freeness outside F. Apply the six-fixed matching form2245: the48 attached vertices W have unique F-neighbors, all permitted group matchings are full, and the remaining24 vertices have no F-neighbor. The two J-orbits of W map equivariantly onto the two three-point orbits of F. Each is the union of the three attached8-sets over its target orbit. Since matching partners in F lie in different three-orbits, each W orbit has induced degree three: one within its own attached group and one to each of the other two. Thus each induced graph is a cubic Cayley graph of J, under its free transitive action.

## Two elementary Cayley obstructions

A simple cubic Cayley graph on an abelian group always contains C4. Its inverse-closed three-element connection set either consists of three involutions, or of one involution z and a pair a,a^-1. In either case it contains distinct commuting elements u,v with v!=u^-1. The vertices1,u,uv,v are distinct and form a C4.

The same conclusion holds for any finite group with a unique nonidentity involution z. That involution is central (conjugation preserves its uniqueness). Every inverse-closed three-element connection set must contain z and one inverse pair, so the same four-cycle applies.

## Consequences for K

If K is cyclic of order eight, its automorphism group has order four. Conjugation by rho is therefore trivial, since its order divides both three and four. J=K times C3 is abelian, and the first obstruction applies.

If K is C4 times C2, its automorphism group has order eight. Indeed an order-four generator has four possible images, and the independent order-two generator has two possible involution images outside the chosen cyclic subgroup. Every such pair defines an automorphism, giving4*2=8. Again rho centralizes K and J is abelian, impossible.

If K is quaternion of order eight, it has a unique involution z. Every involution of J maps trivially to J/K of order three and hence lies in K, so J also has z as its unique involution. The second obstruction applies regardless of how rho acts on K.

Therefore the order-eight kernel cannot be C8, C4 times C2, or Q8. This argument does not exclude elementary abelian order-eight or dihedral order-eight kernels, kernels of order two or four, or all three-orbit/N78 graphs. No classification of groups of order24, graph enumeration, or Lean formalization is used. The bridge2268 remains a required premise until independently accepted; this proof must be reviewed separately.

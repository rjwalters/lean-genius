# Large-prime automorphisms of hypothetical q9 witnesses

For a C4-free graph on N=78 or80 with minimum degree9, accepted2140 gives degree exactly9 at every vertex. Apply its elementary component bound inside any connected component: the component has at least1+(9-1)9=73 vertices. Since2*73>80, the graph is connected.

Let g be an automorphism of prime order p>9. If g fixes a vertex v, it permutes the9 neighbours of v. Every orbit of that permutation has size1 or p, and p>9, so every neighbour is fixed. Connectedness propagates this to all vertices, contradicting the exact order p of g. Thus g has no fixed vertices; all its vertex orbits have size p, and p divides N.

At N=80 no prime greater than9 divides N, so no such automorphism exists. At N=78 the only possible prime greater than9 is13. Accepted2153+2161+2162 excludes a free Z13 action, so that case also cannot occur.

Consequently, a hypothetical witness on either78 or80 vertices has no automorphism of prime order greater than9. Equivalently, by Cauchy's theorem for its finite automorphism group, all prime divisors of the group order belong to{2,3,5,7}. This does not exclude automorphisms at those primes, asymmetric graphs, or arbitrary witnesses. The strengthened N78 conclusion follows from the reviewed m13 exclusion; this note does not supply an independent full N78 proof or any Lean result.

# Every remaining order24 full automorphism group is S4

Let G be simple, C4-free and nine-regular on78 vertices, with full automorphism group A of order24. Accepted2385 excludes a normal Sylow3 subgroup, so A has four Sylow3 subgroups. Accepted2357 gives at least seven vertex orbits, accepted2315 bounds vertex stabilizers by8, accepted2257 bounds involution fixed counts by6, and accepted2207 gives order3 fixed counts0 or3. We prove A is isomorphic to S4.

## No central involution

Suppose z is a central involution. There are exactly eight order3 elements. Multiplication by z gives eight distinct elements of order6, disjoint from the order3 elements. Every such order6 element fixes at most three vertices, because a power is an order3 element. Every other nonidentity element fixes at most six vertices, by taking a prime-order power (the only primes dividing24 are2 and3). Burnside's lemma, with r the number of vertex orbits, yields

 24r <=78+16*3+7*6=168.

Since r>=7, equality is necessary in every term. In particular z fixes six vertices, every order3 element rho fixes three, and rho*z fixes three. Because rho and z commute and have coprime orders, a vertex is fixed by rho*z exactly when it is fixed by both rho and z. Hence Fix(rho) is contained in Fix(z).

The set F=Fix(z) is A-invariant, since z is central, and has size6. Every A orbit has size at least3 by the stabilizer bound8. The possible sizes at most6 dividing24 are3,4,6; a disjoint union totaling6 can only be one orbit of size6 or two of size3. Stabilizers of vertices in these orbits have orders4 or8 and contain no order3 element. Thus rho has no fixed vertex in F, contradicting the three fixed vertices already shown to lie there. No central involution exists.

## The Sylow action is faithful

Let A act by conjugation on its four Sylow3 subgroups, with image B<=S4 and kernel K. The action is transitive, so |B| is divisible by4 and |K|<=6. If3 did not divide |B|, every order3 element of A would belong to K. Then K would contain all four distinct Sylow3 subgroups, whose union has1+4*2=9 elements, impossible. Therefore |B| is divisible by12; since it divides24, it is12 or24.

If |B|=12, K has order2 and its nonidentity element is central in A, because conjugation acts trivially on a group of order2. This contradicts the preceding paragraph. Thus |B|=24, K is trivial, and B=S4. Hence A is isomorphic to S4.

This is a global restriction under the assumption |Aut(G)|=24. It excludes the other groups of order24, including the nonnormal-Sylow central extensions, without invoking a classification of groups of order24. It does not exclude S4 itself, smaller automorphism groups, or N78 existence. All listed inputs are independently accepted; there is no finite enumeration, capped-domain replay, or Lean formalization in this proof.

# No C4-free minimum-degree-8 graph on 63 vertices admits a free cyclic action of order 21

Author: codex-sol-2, 2026-09-11. Proposed paper proof for independent squad review. This concerns the specified positive-control class, not all graphs on 63 vertices. No solver result is used.

## 1. The three-orbit quotient

In any C4-free graph of minimum degree at least d, a vertex of degree D has at least `1+(d-1)D` vertices in its closed two-step neighbourhood: its D neighbours induce a matching plus isolates, each has at least d-2 neighbours outside the closed neighbourhood, and those outside sets are pairwise disjoint. For N=63,d=8 this gives D<=8. Hence the graph is 8-regular.

A free cyclic action of order 21 has three vertex orbits, each of size 21. Their internal graphs are odd-order circulants of degree 0 or 2. An internal degree at least 4 supplies two distinct noninverse shifts u,v, and `0,u,u+v,v` is a C4. Let internal degrees be a,b,c and cross degrees x,y,z. Regularity gives

`a+x+y=b+x+z=c+y+z=8`.

Counting common-neighbour pairs within the first orbit gives

`a(a-1)+x(x-1)+y(y-1)<=20`,

and similarly for the other orbits. Up to permutation, internal degrees 000,002,022 respectively give cross degrees 444,533,442 and violate this bound (24,26,24 at an orbit of degree zero). Thus only internal degrees 222 and cross degrees 333 remain. This recovers the sol3 quotient diagnostic independently.

For a fixed vertex in one orbit, the number of length-two walks to a different orbit is `2*3+3*2+3*3=21`. All endpoints are distinct by C4-freeness. Consequently **every pair of vertices in different orbits has exactly one common neighbour**.

## 2. Fourier adjacency blocks

Label each orbit by Z/21Z so the action adds one. Its internal shifts are ±s_i with s_i nonzero modulo 21. The three offsets from orbit i to orbit j form a three-element set B_ij; put B_ji=-B_ij. At any 21st root z define the Hermitian matrix H(z) with diagonal

`a_i(z)=z^s_i+z^(-s_i)`

and off-diagonal entry

`b_ij(z)=sum(z^t : t in B_ij)`.

The cross-orbit common-neighbour equality implies that the off-diagonal entries of H(z)^2 are zero for every nontrivial 21st root z: their underlying circulant blocks are all-ones matrices, whose nontrivial Fourier values vanish. In particular,

`(a_i+a_j)b_ij + b_ik*b_kj = 0` for distinct i,j,k.

Three complex unit vectors can sum to zero only when their directions are separated by 120 degrees. (Taking the squared modulus of the sum of two gives their real inner product -1/2.) Therefore b_ij(z) cannot vanish when z has order 7. When z has order 21, vanishing would require B_ij to be `{t,t+7,t+14}`. That offset set gives a K3,3 between suitable triples in the two orbits, contradicting C4-freeness. Thus **all off-diagonal entries are nonzero at roots of order 7 or 21**.

At those roots H^2 is diagonal and commutes with H. Its three diagonal entries must therefore agree; write H^2=lambda I. Since off-diagonal entries are nonzero, lambda>0. The Hermitian eigenvalues are ±sqrt(lambda). They cannot all have the same sign, since then H would be scalar. In dimension three this gives `(tr H)^2=lambda` and hence

`K(z):=tr(H(z)^2)-3(tr H(z))^2=0`.

## 3. At a cube root

Let omega be a primitive cube root. Each a_i(omega) is either 2 or -1, and each squared modulus `|b_ij(omega)|^2` is in `{0,3,9}`. The latter follows by distributing the three offsets among the three residue classes modulo 3: multiplicities 111,210,300 give these three values.

All sums a_i+a_j lie in `{4,1,-2}`, so none is zero. If one off-diagonal entry vanishes, the three off-diagonal equations for H^2 force all three to vanish. If none vanishes, combining the equations gives

`|b_ij|^2=(a_i+a_k)(a_j+a_k)`.

The possible right-hand sides are `{16,4,1,-2}`, disjoint from the possible nonzero squared moduli `{3,9}`. This is impossible. Therefore all b_ij(omega) vanish.

If r of the three internal shifts are divisible by 3, then r diagonal values equal 2 and the other 3-r equal -1. Thus

`K(omega)=(3+3r)-3(3r-3)^2`.

For r=0,1,2,3 these values are **-24, 6, -18, -96**, respectively. None is divisible by 7.

## 4. Integral-polynomial contradiction

K is an integer Laurent polynomial: explicitly it is the sum of the three squared diagonal polynomials and twice the three products b_ij(z)b_ij(z^-1), minus three times the squared sum of the diagonals. Reduce its exponents modulo 21 to obtain an integer polynomial P of degree at most 20 with the same values at all 21st roots.

Section 2 says P vanishes at every root of order 7 or 21. These are exactly the 18 roots of

`F(z)=1+z^3+z^6+...+z^18=(z^21-1)/(z^3-1)`.

Since F is monic, division gives `P(z)=F(z)Q(z)` with Q an integer polynomial of degree at most 2. One can see this without any irreducibility premise: monic long division over the integers leaves a remainder of degree below 18; it vanishes at 18 distinct roots and is therefore zero.

At omega, F(omega)=7. Write Q=A+Bz+Cz^2. Then

`K(omega)=7[(A-C)+(B-C)omega]`.

The left-hand side is a rational integer. Since omega is nonreal, B=C; hence K(omega) is divisible by 7. This contradicts all four values in Section 3. The presumed graph does not exist.

## Scope

If independently accepted, this proves the requested N63/d8/m21 class cannot serve as a positive control. The m63 option is already excluded by the elementary circulant C4 argument. An existing solver run must still be accounted for and its terminal status preserved. This proof does not authorize substituting m7/m9, changing a live CNF, restarting a run, or bypassing the two-control gate. It proves neither a q9 witness nor global nonexistence at N78/N80, and is not a Lean formalization.

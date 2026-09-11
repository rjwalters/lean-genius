# No order-seven automorphism at N=78 or 80

Assume G is C4-free with N=78 or 80 and minimum degree 9. Below-square regularity (accepted 2140) gives degree exactly 9. Suppose g is an automorphism of exact prime order 7. Let F be its fixed vertex count and M=N-F its moved vertex count. M>0 is divisible by 7; F>0 since neither N is divisible by 7.

A moved vertex has at most one fixed neighbour: two fixed neighbours would have its whole seven-element orbit as common neighbours. Thus the moved induced graph has minimum degree 8 and M>=57 by the elementary C4-free bound 1+d(d-1). Hence F<=N-57.

A fixed vertex has induced fixed degree 2 or 9. In particular F>=3. Let b count those of induced degree 2. The boundary has 7b edges, giving 7b<=M. The ordered pair common-neighbour count in the fixed induced graph gives 72(F-b)+2b<=F(F-1). Thus F(73-F)<=70b<=10(N-F), or F(83-F)<=10N. Check F>=3, F<=N-57, F congruent to N modulo 7: at N78 only F8 survives; at N80 only F3 or F10 survive. For F3 and F8, all fixed induced degrees are 2 since F<10. For F10, the inequalities give b>=9 and b<=10, and the fixed induced degree sum 90-7b must be even, forcing b=10. Therefore in every case the fixed induced graph is 2-regular.

Each fixed vertex u has exactly seven moved neighbours, forming one g-orbit O_u. These attached orbits are distinct because a moved vertex has at most one fixed neighbour. Let k=M/7 be the number of moved orbits. Each vertex of O_u has exactly one fixed neighbour, namely u, and thus eight moved neighbours.

The attached orbit O_u is independent. Indeed, every x in O_u has at most one neighbour in O_u: two would be common neighbours of x and u. The induced graph on the orbit is regular by g-transitivity, and a 1-regular graph on seven vertices is impossible by degree parity. Hence its degree is zero.

For any other moved orbit P, a vertex x of P has at most one neighbour in O_u, since all these neighbours are common neighbours of x and u. By transitivity and equality of orbit sizes, every vertex of O_u also has at most one neighbour in P. Furthermore if fixed vertices u,v are adjacent, there are no edges between O_u and O_v: for x in O_v, v is already a common neighbour of x and u, so a neighbour in O_u would give a second.

Each u has two distinct fixed neighbours, giving two other attached orbits with no edges to O_u. Together with its independent own orbit, this limits the moved degree of a vertex in O_u to k-3. Since that degree is eight, k>=11. This excludes N78,F8 (k10) and N80,F10 (k10).

The final case N80,F3 has k11, with the three fixed vertices forming a triangle. Its three attached orbits have no edges within or between them. Each attached orbit must have crossdegree exactly one to each of the other eight moved orbits to achieve moved degree eight. Fix x in one attached orbit O_u and consider another attached orbit O_v. Through each of the eight unattached orbits there is exactly one two-step walk from x ending in O_v: its first step is unique and so is the second. These eight walks have distinct middle vertices but only seven possible endpoints in O_v. Two walks share an endpoint, giving a C4 (the four vertices lie in distinct attached endpoints and distinct middle orbits). Contradiction.

Thus no exact-order-seven automorphism exists at either order. This proof does not assume a free action and uses no quotient search. Combined with accepted large-prime restriction2163, prime divisors of Aut(G) at either order lie among 2,3,5. If the separate order-five proof is accepted, at N78 they lie among 2,3 only, whereas at N80 order-five elements act freely. These group restrictions do not exclude asymmetric graphs or globally rule out either order. No Lean claim.

# Three-subgroup restrictions at orders78 and80

Assume a finite simple C4-free graph G of minimum degree at least9 and order N in{78,80}. Accepted near-Moore regularity gives degree exactly9. Use accepted review2176: every nonidentity automorphism of order3 has independent fixed set; if it fixes v, exactly three triangles contain v. Its fixed count is0 or3 at78, and2 or5 at80.

## Local lemma: any3-subgroup fixing a vertex has order at most3

Let H be a nontrivial3-subgroup fixing v. For any neighbour x of v, its stabilizer H_x is trivial: otherwise this nontrivial3-group contains an element of order3, which fixes adjacent v,x, contradicting independence of its fixed set. Hence H acts freely on the nine neighbours of v.

Choose an element of order3 in H. Since it fixes v, there are exactly three edges in the induced graph on N(v), corresponding bijectively to the three triangles through v. H permutes these three edges. The setwise stabilizer in H of any such edge is trivial: its action on the two endpoints has image of order dividing both a power of3 and2, so fixes both endpoints, and a neighbour stabilizer is trivial. Therefore the action on these three edges is free, and |H| divides3. This lemma applies to every vertex stabilizer in any3-subgroup of Aut(G).

## Order80

For any3-subgroup P, its vertex orbits have powers of3 as lengths, so the number of global fixed vertices is80 modulo3, hence nonzero. Applying the local lemma to P at one such vertex yields |P| at most3. In particular9 does not divide |Aut(G)|, and there is no automorphism whose order is divisible by9.

## Order78

Let P be a3-subgroup of order3^a with a>=1. By the local lemma every vertex stabilizer has order1 or3. All vertex orbit lengths are therefore3^a or3^(a-1). Consequently3^(a-1) divides78, implying a<=2. Thus27 does not divide |Aut(G)|.

If |P|=9, it is abelian and each vertex orbit has size3 or9. Write their counts as A and B, so A+3B=26. For a size3 orbit, its stabilizer L has order3 and, because P is abelian, L fixes all three vertices of that orbit. The fixed set of a generator of L has exactly3 vertices by2176. Thus different size3 orbits have different stabilizer subgroups, and each order3 subgroup contributes at most one such orbit.

If P is cyclic of order9, it has only one order3 subgroup, so A<=1, inconsistent with A congruent2 modulo3. Hence no cyclic order9 subgroup exists.

Otherwise P is C3 x C3 and has four order3 subgroups. Now A<=4 and A congruent2 modulo3 give A=2, B=8. Exactly two order3 subgroups have fixed vertices (three each, in disjoint orbits); the other two act freely. In particular a Sylow3 subgroup of order9 is elementary abelian, with two vertex orbits of size3 and eight of size9. There is no automorphism of order divisible by9 at order78 either.

## Combined scope

Combining the separately accepted prime-support and5-subgroup bounds with the full order7 exclusion: at78, |Aut(G)|=2^a*3^b with b<=2, and its3-subgroups have exponent3; at80, |Aut(G)|=2^a*3^b*5^c with b,c<=1. These statements place no bound on a and do not exclude graphs with small or trivial automorphism group. They are conditional symmetry restrictions, not a solution of Erdős85 or a global exclusion at either order.

No graph enumeration, numerical solver, bounded search retry, or new computational assumption is used.

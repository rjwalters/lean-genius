# Complete order-24 group and center-action cover for four orbits

Assume the accepted four-orbit quotient reduction 2314 and |A|=24. Then F,U,V,R have sizes 6,24,24,24, and A acts regularly on U,V,R. The induced R graph is cubic, so it is a cubic Cayley graph of A. The two attached orbits have equal internal degree a in {1,4}, cross degree 5-a, and three neighbors per vertex in R. We give a complete finite group and center-action cover for this case, without running the resulting graph check.

## Elementary Cayley obstructions

A cubic undirected Cayley connection set has three distinct nonidentity elements and is inverse-closed. On an abelian group it contains distinct commuting u,v with v not u^-1, yielding the four-cycle 1,u,uv,v. If the group has a unique involution z, then z is central, the connection set must include z and an inverse pair, and the same four-cycle applies. These are the accepted 2278 elementary obstructions. Therefore neither an abelian group nor a group with a unique involution can realize the present A action.

## Normal Sylow-three subgroup

The number of Sylow-three subgroups divides eight and is one modulo three, so is one or four. If it is one, let N=C3 be the normal subgroup. A Sylow-two subgroup P has order eight, intersects N trivially and satisfies A=NP. Hence A=C3 semidirect P, determined by a homomorphism chi:P->Aut(C3)=C2. In additive notation the product is

    (c,p)(d,q)=(c+(-1)^chi(p) d, pq).

Use each of the five order-eight groups C8, C4 x C2, E8, D8,Q8 and every character, including zero. Their character counts are respectively 2,4,8,4,4: these follow directly from their abelianizations C8, C4 x C2, E8, V4,V4. Thus 22 labelled product tables cover all groups in this case, with duplicates allowed. Some tables are already ruled out by the elementary Cayley obstructions; retaining them only enlarges the necessary domain.

## Four Sylow-three subgroups

Suppose there are four. Conjugation gives a transitive permutation action on those four subgroups, with image in S4 and kernel T. Its image contains an element of order three. Otherwise an entire Sylow-three subgroup would lie in T, and normality would put all four such subgroups in T, giving at least nine elements. But transitivity gives image order at least four and hence |T|<=6, a contradiction.

The image order is therefore divisible by both four and three and divides 24, so is 12 or 24. In the latter case T is trivial and A=S4. In the former case the image is A4: it is an index-two subgroup of S4, and the only nontrivial homomorphism S4->C2 sends all conjugate transpositions to one and equals permutation sign. Then T has order two and is central.

Let P be the inverse image of the normal Klein four subgroup of that A4 image. It is a normal subgroup of order eight. Choosing rho of order three yields A=P semidirect <rho>. Its conjugation action on P is nontrivial, since its induced action on P/T=V4 is the nontrivial order-three action in A4.

Among the five groups of order eight, only E8 and Q8 can have an automorphism of order three: Aut(C8), Aut(C4 x C2), Aut(D8) have orders four,eight,eight respectively, as proved in accepted 2278/2298. If P=Q8, every involution of A lies in P because A/P has odd order, and P has a unique involution. This is impossible by the cubic Cayley obstruction. If P=E8, the nontrivial order-three linear action is a fixed line plus the irreducible two-dimensional plane (the cyclic-basis proof in accepted 2298). Therefore A is C2 x (V4 semidirect C3)=C2 x A4.

Thus the 22 normal-C3 tables, together with S4 and A4 x C2, form a complete overinclusive list of 24 labelled group models for this graph problem. No classification of groups of order 24 has been assumed as a black box.

## Complete center action and matching domain

For each group model, enumerate every subgroup H of order four. Every transitive action of A on six centers is its action on left cosets A/H for some point stabilizer H. No faithfulness of this center action is required; its kernel may be nontrivial.

An A-invariant matching is determined by the partner aH of H. This coset must differ from H and be fixed by H, equivalent to a normalizing H. Equivariance makes the partner of gH equal to gaH, and applying the map twice is identity precisely when a^2 belongs to H. Conversely any a in N_A(H) with a not in H and a^2 in H defines a fixed-point-free involution of the coset set and hence the required matching. Enumerate distinct such cosets aH, retaining duplicates between isomorphic actions if convenient. This covers every possible center action and matching.

Choose the origins in both regular attached orbits U,V over H; this is possible because each orbit maps onto all six centers and has four vertices over each. Then a vertex g in either copy attaches to gH. Write S_U,S_V for the inverse-closed internal connection sets, of size a=1 or4, and T for the U-to-V connection set, of size 5-a. Reverse cross connections use T^-1.

The combined elements in S_U and T must project to the five distinct cosets other than the matching partner aH, once each. Likewise S_V and T^-1 must project to those five cosets once each. The identity is forbidden in internal connection sets; no inversion closure is imposed on T. These conditions precisely express the saturated five allowed attached-center slots and the canonical quotient. They are necessary, and further C4 conditions must still be checked.

For a later necessary residual-incidence check, the regular residual identity has six attached neighbors, one over each center and three in each of U,V. All other residual neighborhoods are its left translates. Any two chosen attached neighbors with an existing common neighbor forbid that choice; any nonidentity translate intersecting the base neighborhood in two vertices also forbids it. These conditions omit all residual internal edges and are only necessary for a full graph.

This packet establishes complete group and action parameters, not an enumeration outcome or a four-orbit exclusion. It uses accepted 2314 but not the pending order-48 exclusion 2317; it applies directly under the stated |A|=24 hypothesis. No graph solver or Lean formalization is used, and Erdős85 remains unresolved.

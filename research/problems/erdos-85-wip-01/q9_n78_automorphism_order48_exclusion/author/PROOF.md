# The full automorphism group of an N78 candidate cannot have order48

Let G be a simple C4-free nine-regular graph on78 vertices and A=Aut(G). Accepted2264 gives |A| dividing48, accepted2315 bounds every vertex stabilizer by8, and accepted2357 proves that A has at least seven vertex orbits. Accepted2257 bounds the fixed vertices of every nonidentity involution by six; accepted2207 and its uses in2332 give zero or three fixed vertices for every nonidentity order3 element. We show |A| is not48.

Assume |A|=48. Every nonidentity g in A fixes at most six vertices: some power of g has prime order2 or3, and every vertex fixed by g is fixed by that power. Write r for the number of vertex orbits. Burnside's lemma gives

    48r = 78 + sum_{g!=1} |Fix(g)|.

Let s be the number of Sylow3 subgroups of A. Each has order3, so s is1,4 or16, and precisely2s elements have order3. Bounding their fixed counts by3 and all remaining nonidentity elements by6 gives

    48r <= 78 + (47-2s)*6 + (2s)*3 = 360-6s.

## Sixteen Sylow3 subgroups

For s=16, this yields r<=264/48=5.5, contrary to r>=7.

## Four Sylow3 subgroups

For s=4, the bound gives r<=336/48=7. Since r>=7, equality is necessary in every summand. In particular every nonidentity element not of order3 would have to fix exactly six vertices.

Take a Sylow3 subgroup P=<rho>. Its normalizer has order48/4=12. Conjugation on P maps that normalizer into Aut(C3), of order2, so the centralizer C_A(P) has order6 or12. It therefore contains an involution t, by Cauchy's theorem. The commuting product rho*t has order6, and every vertex fixed by it is fixed by its square, a nonidentity element of P. It has at most three fixed vertices, contrary to the equality requirement of six. Thus s=4 is impossible.

## A normal Sylow3 subgroup

For s=1, let P=<rho> be the normal order3 subgroup. Its fixed set Fix(P) is A-invariant and has size zero or three. Every A vertex orbit has size at least48/8=6 by2315, so an invariant set of size3 is impossible. Thus P acts freely on vertices.

Let C=C_A(P). Conjugation A->Aut(P) has kernel C, so |C| is24 or48. Let T be a Sylow2 subgroup of C, of order |C|/3, hence at least8. Since P is central in C, P and T commute, intersect trivially, and their product has order |C|. Thus C is their direct product.

For every t in T, both rho*t and rho^2*t have a power equal to a nonidentity element of P: if t has order2^a, raise the product to2^a. Since P is free, each such element fixes no vertex. They are2|T| distinct nonidentity elements, at least16. Bounding all other nonidentity elements by six now gives

    48r <= 78 + (47-16)*6 =264,

again contradicting r>=7.

All three Sylow possibilities are impossible. Therefore |Aut(G)| is not48. Combined with2264, the remaining possible orders are the proper divisors of48, all at most24; order16 is not excluded by this corollary, so we do not claim that the order divides24.

This is a global restriction on the full automorphism group of every N78 candidate, not merely on an assumed seven-orbit case. It does not exclude smaller automorphism groups, asymmetric candidates, N78 existence, N80 or Erdős85. It uses no new finite search or Lean formalization.

# Six nonfree vertices for a locally regular order-eight stabilizer

Assume G is simple, C4-free, has78 vertices and minimum degree nine. Let H be an order-eight automorphism subgroup fixing adjacent vertices v,x. Assume H acts regularly (freely and transitively) on A=N(v) minus{x} and B=N(x) minus{v}. Then exactly six vertices of G have nontrivial H-stabilizer. They are v,x and an H-invariant four-element set U. The remaining72 vertices form nine free H-orbits. Moreover, with R the56 vertices outside {v,x},A,B,U:

* A and B are disjoint eight-element sets inducing perfect matchings, with no edges between them or from either to U.
* Every vertex of R has exactly one neighbor in A and exactly one in B.
* For the five-regular deficiency graph E, N_E(v)={x} union U and N_E(x)={v} union U.
* For r in R, its number of G-neighbors in U equals its number of E-neighbors in A and also in B. In particular it has at most two G-neighbors in U.

These conclusions are conditional on the two regular neighborhood actions. No exclusion or completed graph is claimed.

## Nonfree vertices

First vx has no common neighbor: if x meets one vertex of A, transitivity makes it meet all eight, giving two vertices with common neighbors v,x. Thus A and B are disjoint. Let y outside{v,x} have nontrivial stabilizer H_y. It is in neither A nor B, whose actions are free, so it is adjacent to neither v nor x. If y had a common neighbor a with v, uniqueness of that common neighbor would force every member of H_y to fix a. This neighbor lies in A, because x is not adjacent to y. Freeness on A contradicts H_y nontrivial. The argument at x is identical.

Near-Moore regularity makes G nine-regular. Its deficiency graph E joins distinct vertices with no common G-neighbor and is five-regular (E=8I+J-M^2). Hence every such y is an E-neighbor of v and of x. The pair v,x is also an E-edge. At most four nonfree vertices can therefore lie outside{v,x}. The total number of nonfree vertices is at most six and congruent to78 modulo eight, because all other H-orbits have size eight. It must equal six. Let U denote the four additional vertices. The deficiency neighborhoods follow by exhausting degree five.

## Saturation of A and B

The induced graph on N(v) has maximum degree one by C4-freeness. The vertex x is isolated there. By transitivity, the internal degree on A is constant zero or one. Zero would make N(v) independent, requiring1+9+9*8=82 distinct vertices within distance two of v; distinct first neighbors cannot share an outside second neighbor. This exceeds78. Thus A is a perfect matching, and so is B.

An A--B edge together with vx would make a C4. There are no A--U or B--U edges by the common-neighbor argument above. Each vertex of A therefore sends its remaining seven edges to R, giving56 A--R edges. Each vertex of R has at most one neighbor in A by its codegree with v. Since |R|=56, all these bounds are saturated. The B conclusion is identical. R is H-invariant and is the union of seven free H-orbits.

## Deficiency commutation

Write M for G adjacency. Regularity implies ME=EM. At(v,r) for r in R, the left side counts E-neighbors of r in A, because N_G(v)={x} union A and E(x,r)=0. The right side counts G-neighbors of r in U, because N_E(v)={x} union U and G(x,r)=0. The equation at(x,r) similarly gives the count in B. Since A and B are disjoint and E has degree five, twice this nonnegative integer is at most five; it is at most two.

## Abelian order-eight stabilizers satisfy the hypothesis

If H is abelian of order eight and fixes v, it fixes a neighbor x by the odd size nine. By2257 it acts faithfully on the remaining eight neighbors and each involution fixes zero or two of them. An orbit of size four would have a stabilizer of order two, which by commutativity fixes the entire orbit, contradicting the involution bound. If no orbit has size eight or four, all orbits have size one or two. Faithfulness then embeds H into the independent swaps of at most four disjoint pairs, an elementary abelian binary code. Every nonzero codeword must swap at least three pairs. The length-four minimum-weight argument of2257 bounds this subgroup by two, contrary to |H|=8. Thus the action is regular on all eight. Applying the same argument at x gives regularity on B. Consequently this normal form applies to every abelian order-eight subgroup fixing a vertex.

The proof uses the accepted graph and local-action premises of2257. It does not rely on a classification of two-groups, enumerate extensions, or supply Lean formalization.

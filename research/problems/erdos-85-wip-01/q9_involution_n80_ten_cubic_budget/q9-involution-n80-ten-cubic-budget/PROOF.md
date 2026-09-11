# Residual degree restriction in the N80/F10 cubic-fixed branch

Assume a simple C4-free graph G on 80 vertices has minimum degree nine and an involution fixing ten vertices, and assume its fixed graph H is cubic. The cubic hypothesis specifies one of the two fixed-degree branches retained by accepted 2223; the other branch is not addressed here. Accepted 2220 gives nine-regularity and disjoint attached groups B_v, each of size six. The unattached residual set R has size 10. The involution is free on the attached union W and on R.

## Four attached residual-degree patterns

For x in B_v, at most one moved neighbor lies in B_v, no neighbor lies in an attached group whose fixed center is adjacent to v in H, and at most one lies in each of the six other groups. Its eight moved neighbors therefore require at least one in R. Every residual vertex meets B_v at most once, so the total B_v--R incidence count is at most ten.

The three free involution orbits inside B_v have positive integral R-degrees k_1,k_2,k_3 with k_1+k_2+k_3<=5. Their unordered possibilities are exactly

    111, 211, 221, 311.

Let n_111,n_211,n_221,n_311 count the ten groups of these types. Let Q be the quotient of G[R] on its five involution orbits, and d_j its row degrees. Every Q entry is zero or one: a cross entry two would produce K2,2, and a diagonal entry records the optional edge in a two-vertex orbit. Thus 0<=d_j<=5. Write D=sum_j d_j.

A residual vertex in orbit j has 9-d_j attached neighbors, one per attached group it meets. Consequently exactly 1+d_j fixed centers have no common G-neighbor with that vertex. Counting attached/residual edges gives

    D=15-n_211-2n_221-2n_311.

## An exact zero-codegree identity

Let E=8I+J-M², where M is the adjacency matrix of G. This is the simple seven-regular zero-codegree graph, and ME=EM. A pair of residual vertices can have a common neighbor only in W or R. Attached vertices contribute

    2C, where C=n_211+2n_221+3n_311=15-D+n_311,

to the count of unordered residual pairs with a common neighbor. This follows by summing choose(k,2) for the three orbit degrees in each attached group, then multiplying by two. Residual middle vertices contribute sum_j d_j(d_j-1). C4-freeness makes all these pairs distinct. Therefore

    e_E(R)=45-2C-sum_j d_j(d_j-1).

There are 10+2D E-edges from R to the fixed set, by the missing-center count above. Summing all 70 E-degrees on R now gives

    e_E(R,W)=70-2e_E(R)-(10+2D)
             =30+2 sum_j d_j(d_j-4)+4n_311.

This nonnegative integer yields the necessary bound

    sum_j (d_j-2)^2 + 2n_311 >= 5.

In particular the residual graph cannot be two-regular: then D=10, incidence counting gives n_211+2n_221+2n_311=5 and hence n_311<=2, while the displayed bound requires n_311>=3.

## Stronger conclusion when residual degrees are only two or three

Suppose every residual degree is two or three. Let j be the number of residual orbits of degree three. Then D=10+j. Substituting into the exact identity and incidence equation gives

    e_E(R,W) = -2n_211-4n_221.

Hence n_211=n_221=0 and E(R,W) is empty. Moreover 2n_311=5-j. The only numerical possibilities are

    (j,n_111,n_311)=(1,8,2), (3,9,1), (5,10,0).

We exclude the first two without a graph search.

The fixed block of E is 2I+J-H², since each fixed vertex has six attached neighbors and distinct fixed vertices share no moved neighbor. This block is three-regular. A type-111 fixed center misses four residual vertices and therefore has four E-neighbors in R and none in W. A type-311 center covers R and consequently has four E-neighbors in W.

Let S be the attached vertices with R-degree three; there are 2n_311 of them. Every other attached vertex x has R-degree one. The original local capacity bound is then tight at x: it has an internal matching neighbor and one neighbor in every allowed cross group. It follows that x has exactly one common G-neighbor with every fixed center (internal neighbor for its own center, the fixed neighbor itself for an adjacent center, and an attached cross neighbor for every other center). Thus no fixed vertex has an E-neighbor outside S in W.

If n_311=1, a type-311 center would need four distinct E-neighbors inside S of size two, impossible. This excludes j=3.

If n_311=2, there is only one residual orbit of degree three. Let P be the eight type-111 centers. Each v in P misses two distinct residual orbits, say s and t. Sum ME=EM at (v,r) over all r in R. Since E(W,R) is empty and v has no attached E-neighbor, this gives

    4 |N_H(v) intersect P| = 2(d_s+d_t).

If v misses the unique degree-three orbit and a degree-two orbit, the right side is ten, not divisible by four. Thus no center in P can miss the degree-three orbit. But every vertex in that orbit must miss exactly 1+3=4 attached groups, all necessarily of type 111 because type 311 covers R. This is a contradiction. It excludes j=1.

Therefore, if all residual degrees lie in {2,3}, they must all equal three and all ten attached groups must have pattern 111. Equivalently, any remaining case outside this uniformly cubic residual form must contain a residual vertex of degree 0, 1, 4, or 5.

## Excluding the uniformly cubic case

The companion self-contained lemma in cubic-ten-free-involution/PROOF.md shows that a cubic C4-free graph on ten vertices cannot carry a free involution. It uses the binary symmetric five-orbit quotient with row sums three, the off-diagonal Q² bound two, and the prohibition on adjacent looped vertices. The odd number of loops is one, three, or five; each case immediately contradicts those bounds.

The residual graph here inherits C4-freeness and a free involution. Therefore the uniformly cubic possibility is impossible as well. We conclude that in this N80/F10 cubic-fixed branch, the residual graph must have at least one vertex of degree 0, 1, 4, or 5. It cannot have all its degrees in {2,3}.

This excludes a family of residual-degree patterns, not the whole N80/F10 branch. No exceptional residual-degree case is asserted realizable or excluded. No full graph solver or Lean formalization is used, and Erdős 85 remains unresolved.

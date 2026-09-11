# A four-cycle fixed count excludes one S4 action pattern

Let G be simple, C4-free and nine-regular on78 vertices with A=Aut(G) isomorphic to S4 and orbit sizes(4,6,6,6,8,24,24). Suppose an element g corresponding to a four-cycle in S4 fixes six vertices. This is impossible.

The four-orbit F carries the natural S4 action. To see this, its stabilizer H has order6 and a unique Sylow3 subgroup P, since the number of Sylow3 subgroups divides2 and is1 modulo3. Hence H lies in N_A(P). A natural three-cycle has one fixed point, and its normalizer is precisely the order6 stabilizer of that point. Thus H is a natural point stabilizer. In particular g has no fixed vertex in F. The graph on F is empty: transitivity on unordered pairs permits only the empty graph or K4, and K4 has a C4.

The stabilizers in the eight- and24-orbits have orders3 and1, respectively. None contains an element of order4, so g has no fixed vertices in those orbits either. All six of its fixed vertices therefore lie in the three six-orbits.

A six-orbit has a stabilizer K of order4. If K has no element of order4 it contributes no g-fixed vertices. If it has one, K is cyclic of order4 and contains precisely two four-cycles. The centralizer of a four-cycle in S4 has order4: a commuting permutation is uniquely determined by the image of one point on its full four-point cycle. The fixed coset formula therefore gives exactly4*2/4=2 fixed vertices in this six-orbit. Since g fixes six vertices altogether, all three six-orbits must have cyclic order4 stabilizers.

Fix f in F and let H=A_f be its natural S3 stabilizer. The intersection of H with any conjugate cyclic order4 subgroup is trivial. Such a subgroup has exactly one involution, a double transposition, which fixes no point in the natural four-point action and hence cannot belong to H. Its other nonidentity elements have order4 and also fix no natural point. Thus every H orbit in each of the three six-orbits has size6.

In the eight-orbit every point stabilizer has order3, so its intersection with H has order1 or3 and the H orbit sizes are6 or2. In either regular24-orbit all H orbits have size6. Therefore every H orbit outside F has even size. The neighbor set of f is H-invariant and contains no vertex of F, so it has even cardinality. This contradicts degree9.

This paper excludes only the displayed orbit-size pattern combined with four-cycle fixed count six. It does not exclude the same sizes with other fixed counts. It assumes these conditions directly and uses no finite character enumeration, fixed-point classification, or capped graph computation. No Lean formalization or global N78 exclusion is claimed.

# The elementary abelian two-rank is at most four at N78

Let G be a simple C4-free graph on78 vertices with minimum degree9. Accepted2220,2236,2237 imply that every nonidentity involution fixes at most six vertices. We prove that Aut(G) has no elementary abelian subgroup of order32; consequently its elementary abelian two-rank is at most4.

Suppose A is an elementary abelian group of order32 acting as automorphisms. Regard A as a five-dimensional vector space over F2. For an A-orbit O with nontrivial point stabilizer H, any nonidentity t in H is an involution and fixes the whole orbit, since A is abelian. Hence |O|<=6. The only possible nonfree orbit sizes are therefore1,2,4, while every free orbit has size32.

Let S be the union of the nonfree orbits. The number of singleton orbits is even, because78 and every other orbit size are even. Pair the singleton orbits into two-element units. Together with the genuine orbits of sizes2 and4, these form units of sizes2 or4 partitioning S.

If |S|>=8, select units of total size exactly8. This is always possible with units of sizes2 and4: choose two four-units if available; otherwise choose one four-unit and two two-units, or four two-units. For a genuine orbit of size2 or4, its stabilizer has codimension1 or2 in A. A paired singleton unit has stabilizer A, of codimension0. Thus the intersection K of the stabilizers of the selected units has codimension at most4, since the total selected size is8 and each unit's stabilizer codimension is at most half its size.

The five-dimensional vector space A therefore contains a nonzero element t in K. This is a nonidentity involution fixing all eight selected vertices, contradicting the bound of six. We conclude |S|<=6.

But78-|S| is a multiple of32, because all remaining orbits are free. It follows that |S| is congruent to14 modulo32, impossible for0<=|S|<=6. This contradiction excludes A.

An elementary abelian two-group of larger rank contains a subgroup of order32, so those are excluded too. The conclusion is a rank bound only: it does not bound the order of arbitrary nonabelian two-subgroups by16 and does not exclude elementary abelian subgroups of rank4. This paper group-action argument uses no graph search or Lean formalization.

# The locally regular H8 case has a six-centre matching structure

Use accepted2263. Let H have order8, fix adjacent vertices v,x, and act regularly on A=N(v) minus{x} and B=N(x) minus{v}. The nonfree set is S={v,x} union U with|U|=4. The remaining72 vertices are free H-orbits; A and B are two such orbits, and R is the union of the other seven. The sets A,B induce perfect matchings, have no edges between them or to U, and every vertex of R meets A and B once. Every r in R has at most two U-neighbors.

## The four nonfree vertices induce two disjoint edges

The number q of U-neighbors is constant on each free H-orbit in R. If q=2 on one such orbit, its eight vertices yield eight unordered pairs of U-neighbors. These pairs must be distinct by C4-freeness, but U has only six pairs. Thus every q is0or1.

Let s be the number of the seven R-orbits with q=1. There are exactly8s edges from U to R. There are no edges from U to A,B,v,x, so nine-regularity gives

    36 = 2 e(G[U]) + 8s.

A C4-free graph on four vertices has at most four edges: any five edges form K4 minus one edge and contain a four-cycle. Hence0<=e(G[U])<=4, and the equation forces e(G[U])=2 and s=4.

A four-vertex graph with two edges is either a matching or a path on three vertices plus an isolated vertex. In the latter case, its unique isolated vertex u is fixed by all of H, because U and its induced graph are invariant. All nine neighbors of u lie in R. Its neighbor set would be a union of free H-orbits of size8, impossible. Therefore G[U]=2K2.

Let T be the four R-orbits with q=1, of total size32, and let Z be the other three, of size24. Then S induces3K2. Put W=A union B union T, of size48. Every W vertex has exactly one S-neighbor, and every Z vertex has none. Every s in S has eight W-neighbors, forming six disjoint groups B_s of size8.

## Full matching saturation

For w in B_s, at most one W-neighbor lies in its own group, none lies in the group of s's matching partner, and at most one lies in each of the four other groups. These are the standard C4 common-neighbor and adjacent-centre exclusions. Hence degree_W(w)<=5 and degree_Z(w)>=3.

Each z in Z meets each B_s at most once, so degree_W(z)<=6. Counting W--Z edges gives

    48*3 <= e(W,Z) <= 24*6.

Both sides are144, so all inequalities are equalities at every vertex. Thus each B_s has a full internal matching, all permitted cross-group matchings are full, W-to-Z degree is3, Z-to-W degree is6, and G[Z] is cubic. The quotient in the order(S,W,Z) is

    [1 8 0]
    [1 5 3]
    [0 6 3],       with sizes(6,48,24).

This recovers the saturated six-centre matching structure without assuming a common involution fixes S pointwise.

For completeness, E=8I+J-M^2 has E[S]=K6: distinct S vertices share no G-neighbor, since G[S] is a matching and each W vertex has one S-neighbor. This exhausts deficiency degree5, so E has no S--moved edges. Commutation at a moved vertex w and a centre s gives |N_E(w) intersect B_s| equal to1 if w has an S-neighbor different from s, and0 otherwise. Hence E(Z,W) is empty, every cross B_s--B_t deficiency block is a perfect matching, and E[Z] is five-regular.

## A group-action dichotomy

Consider the action of H on U, now a matching of two edges. If its kernel is nontrivial, that kernel contains a nonidentity involution tau. It fixes S pointwise and fixes no vertex outside S, since all outside H-orbits are free. Thus tau fixes exactly these six matching centres.

If the kernel is trivial, H embeds into Aut(2K2), which has order8 and is dihedral: its generators swap inside each of the two pairs and exchange the pairs. Since |H|=8, the image is the whole dihedral group of order8. This is the alternative where H acts faithfully on U. In particular an abelian H cannot take this alternative, so every abelian order8 vertex stabilizer contains an involution fixing precisely S.

This is a necessary structure and a dichotomy, not an exclusion of either alternative or an extension witness. It applies under the local regularity hypothesis of2263, which that accepted result proves for every abelian order8 vertex stabilizer. No graph or group search and no Lean formalization is used.

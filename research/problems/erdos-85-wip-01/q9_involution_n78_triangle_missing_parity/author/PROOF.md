# The triangle case has an odd missing-pair permutation

Use accepted2243 for the N78/F6 triangle-with-leaves case. Its three cubic attached sets A_1,A_2,A_3 have size6. Each residual vertex r has exactly one neighbor in each A_i, giving a triple of labels. Each label occurs in five triples. No pair of labels from two different A sets occurs twice, since the two residual vertices would give those labels two common neighbors. Thus the30 residual triples project injectively to each pair of label sets, missing precisely a perfect matching of six pairs. Denote the missing bijections by

    P12:A_1 -> A_2, P13:A_1 -> A_3, P23:A_2 -> A_3.

All three commute with the respective free involution actions, by uniqueness of the missing partner. We prove that the permutation

    pi = inverse(P13) composed with P23 composed with P12

of A_1 is odd. In particular the three missing bijections cannot be mutually compatible.

## A parity lemma for invariant triple systems

Let X,Y,Z each have2m labels with a free involution. Choose an index and a bit0/1 for each label orbit, so the involution flips the bit. Suppose a set of triples is invariant, its projection to each pair of label sets is injective, and each projection contains all pairs except a perfect matching. Let these three missing equivariant bijections be Pxy,Pxz,Pyz.

Each triple orbit has two triples. Choose the representative whose X-bit is0, and write its Y-bit t and Z-bit s. Its projections contribute the following bits when represented with the first coordinate's bit0:

* XY contributes t;
* XZ contributes s;
* YZ contributes t+s modulo2.

For an equivariant bijection P, let epsilon(P) be the sum modulo2 of its output bits at the bit0 representatives of its input label orbits. For all pairs between two complete label sets, each of the m^2 blocks of two label orbits contains two pair orbits, with bits0 and1. Thus the sum of projection bits over the complete pair set is m^2 modulo2. Removing the missing matching removes epsilon(P). Because pair projections are injective and equivariant, their pair orbits correspond exactly to the occupied triple orbits. Consequently

    sum t     = m^2 + epsilon(Pxy),
    sum s     = m^2 + epsilon(Pxz),
    sum(t+s)  = m^2 + epsilon(Pyz)       (modulo2).

Adding the first two and comparing with the third yields

    epsilon(Pxy)+epsilon(Pxz)+epsilon(Pyz) = m modulo2.

To identify this with a permutation sign, order each label set by its m pairs and then by the two bits. Any equivariant bijection permutes whole pairs and optionally flips the two elements within pairs. A permutation of whole pairs is even, whereas each internal flip is odd. Its sign in these ordered coordinates is therefore (-1)^epsilon(P). Taking the product for the composition inverse(Pxz) P yz Pxy gives

    sign(inverse(Pxz) composed with Pyz composed with Pxy) = (-1)^m.

This sign is independent of the chosen pair indices and bits, since the composition is a permutation of X. This proves the lemma.

## Consequences for the N78 triangle case

Here m=3, so pi is odd. Relabel A_2 and A_3 by P12 and P13; then those two missing bijections become identities, the involution actions agree on all three label sets, and the third missing bijection becomes pi. It must commute with the free involution on six labels and must be odd.

The centralizer of a free involution on six labels has size2^3*3!=48: it freely permutes the three label pairs and independently flips each pair. Exactly24 of these permutations are odd, because exactly half of the eight flip choices have odd parity. Thus only24 normalized missing-pair permutations survive this necessary parity test. No claim is made that any of those24 admits the residual triples or a full graph.

The identity composition is excluded. Equivalently, if all three missing matchings were compatible, filling the six missing triples would create a Latin square of order6 invariant under a free involution on rows, columns, and symbols; the same bit-sum calculation on a full triple system would force m even. This is impossible for m=3.

This is a paper parity obstruction to part of the triangle-with-leaves case. It is not a full exclusion of that case, of F6, or of N78. No graph search or Lean formalization is used.

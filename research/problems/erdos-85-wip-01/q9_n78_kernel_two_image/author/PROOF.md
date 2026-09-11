# The order-two kernel has the rotational S4 image

Assume the N78 three-orbit action of accepted2264/2268. Write A=Aut(G), so |A|=48 and its vertex orbits F,W,R have sizes6,48,24. The six fixed centers F induce three matching edges. Suppose the kernel K of the action on F has order two. Then K is central in A and B=A/K is a transitive subgroup of the signed matching-permutation group V semidirect S3, where V=F2^3, of order24.

We prove B is the determinant-positive signed-permutation subgroup, isomorphic to S4. Its point stabilizers on F are cyclic of order four. Consequently every center stabilizer H in A is abelian, of type C8 or C4 times C2.

## Residual stabilizer images

Choose r in R. Its stabilizer is L={1,ell} of order two. Accepted2268 says K acts freely outside F, so ell is not in K. The image of ell in B is a nonidentity involution fixing no center: a center fixed by ell would have a stabilizer acting nonfreely at r, contrary to2268.

We will also use the accepted2220 bound of at most ten fixed vertices for any involution in the N78 graph. For the transitive R orbit, the number of points fixed by ell is

    |C_A(ell)| / 2.

Indeed identify R with A/L. A coset aL is fixed precisely when a^-1 ell a belongs to L, hence equals ell. There are |C_A(ell)| such representatives and two per coset.

## The edge image cannot have order three

Let pi:B->S3 permute the three matching edges, and D=B intersect V. Edge transitivity makes |pi(B)| equal to three or six. If it is three, D=V and B is the full preimage V semidirect C3. An involution of B must lie in V. The only nonidentity flip vector fixing no center is z=(1,1,1), the global flip. Therefore ell maps to z, which is central in B.

Every conjugate of ell in A consequently belongs to the two-element coset ell K. Its conjugacy class has size at most two, so its centralizer has order at least24. It fixes at least12 points of R by the preceding formula, contradicting2220. Thus pi(B)=S3 and |D|=4.

## Exactly one parity subgroup survives

The invariant two-dimensional subspace D of V must be the even-weight plane. A codimension-one invariant subspace is the kernel of an invariant nonzero linear functional, since F2 has only one nonzero scalar; invariance under all coordinate permutations forces that functional to be coordinate sum.

The quotient (V semidirect S3)/D is C2 times S3, with first coordinate the parity of the flip vector. The subgroup B/D has order six and projects isomorphically to S3, so it is the graph of a homomorphism S3->C2. The two possibilities are the zero map and permutation sign: three-cycles must map to zero and all transpositions have the same image.

The zero-map subgroup has no fixed-point-free involution on F. To see this, write an element as (v,sigma), with signed action sending (i,b) to (sigma(i), b+v_sigma(i)). If sigma is identity, an even flip vector has weight zero or two and fixes a matching edge. If sigma is a transposition, being an involution requires v=sigma(v), so its two swapped coordinates agree. Even parity then forces the coordinate fixed by sigma to be zero, again fixing both centers of that edge. No other permutation part is possible for an involution. This contradicts the image of ell.

Therefore

    B = { (v,sigma) : sum_i v_i = sign(sigma) in F2 }.

This is exactly the determinant-positive signed-permutation subgroup.

## Identification and center stabilizers

The full signed-permutation group acts on the four antipodal pairs of cube diagonals, represented by sign vectors (plus/minus1,plus/minus1,plus/minus1) modulo simultaneous negation. The kernel of this action is precisely {identity,global flip}. In fact, fixing the all-positive diagonal forces all coordinate signs to agree. After a possible global flip the element is a pure coordinate permutation; fixing the other three diagonal pairs, each represented by its unique negative coordinate, forces that permutation to be identity.

The global flip is absent from B because its flip parity is odd and its permutation sign is even. Thus B embeds faithfully into S4 and, having order24, is isomorphic to S4.

A stabilizer of one of the six oriented coordinate axes has order four. Fix axis i and its positive endpoint. Let sigma exchange the other two coordinates, set v_i=0 and choose different flip bits on the two exchanged coordinates. This signed permutation belongs to B, fixes the chosen endpoint, and its square flips those other two coordinates. It has order four. The entire point stabilizer is therefore cyclic C4.

For a center stabilizer H in A, H/K is this cyclic C4. Since K has order two it is central. A lift h of a quotient generator together with K generates H, and both commute, so H is abelian. The order of h is four or eight. In the latter case H=C8. In the former, its cyclic subgroup intersects K trivially because hK has order four, giving H=C4 times C2.

These are necessary restrictions on the order-two-kernel subcase. They do not classify all central extensions A, exclude K2, or solve the three-orbit or full Erdős85 problem. This is a paper proof without finite enumeration or Lean formalization.

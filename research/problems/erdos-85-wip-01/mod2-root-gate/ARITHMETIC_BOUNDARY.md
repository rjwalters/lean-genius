# The modular controls fail the determinant test uniformly

Status: elementary derivation for independent review. This describes the
family of CONTROL.md, not arbitrary defect graphs.

Use q=2^k, k>=3, s=q²/4, t=q/4-1, T=Cay(Z/sZ,{plus/minus1,...,t}),
H=K2 Cartesian T, D=H[K2]. Here matrices are over the integers and
M=(q-1)I+J-D, in contrast with the mod-2 calculations in CONTROL.md.

Split by the two eigencharacters of the internal K2 of the lexicographic
product. On the minus sector D acts as -I, so M acts as qI, contributing
q^(2s) to its determinant. On the plus sector D acts as I+2H. Splitting
further by the Cartesian K2 character, the remaining eigenvalues are

    q-4-2lambda_j(T),    q-2lambda_j(T),

except that the principal zero in the first list is replaced by q²
because of the J term. At the cyclic trivial and order-two characters,

    lambda_0(T)=2t=q/2-2,    lambda_(s/2)(T)=-2,

where the latter uses odd t. The four exceptional M eigenvalues are thus
q²,4,q,q+4. The cyclic modes j and s-j have the same eigenvalue.

The product of one eigenvalue from every remaining pair is an integer
in each of the two lists: restrict q-4-2T and q-2T to the reflection-minus
lattice spanned by e_j-e_(s-j), 1<=j<s/2. This is an invariant integer
lattice, with precisely one copy of every remaining paired eigenvalue.
Let the two determinants be P_plus and P_minus. Therefore

    det M = q^(2s) * q² * 4 * q * (q+4) * (P_plus P_minus)²
          = q(q+4) * (2 q^(s+1) P_plus P_minus)².

None of these factors vanish: D is connected and (q-1)-regular, so
M=L_D+J is positive definite over the reals. The Laplacian is positive
on the orthogonal complement of 1, and J is positive on the constant space.

The integer q(q+4) is not a square for any k>=3. If k is odd, its
2-adic valuation is k+2, which is odd. If k is even, q is a square and
q+4 lies strictly between q and (sqrt(q)+1)² (q>=16), so q+4 is not a
square. Hence det M is not a square.

In particular there is no integer matrix A with A²=M, nor a rational
matrix X with X transpose X=M. The mod-2 root explicitly constructed in
CONTROL.md cannot lift to such an integer solution. This family therefore
demonstrates a strict limitation of the modular-root predicate alone;
it provides no survivor of the already available determinant-square test.
No candidate search or large determinant computation is needed for this
uniform conclusion, and no general arithmetic obstruction is inferred.

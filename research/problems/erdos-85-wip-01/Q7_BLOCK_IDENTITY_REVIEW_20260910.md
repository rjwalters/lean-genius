# Independent review of q7 block identities — 2026-09-10

Reviewer: codex-sol-2. Subject: sol1/sol3 room derivations42530–42547.
Status: paper derivation checked, small symbolic checks passed; no Lean proof,
no excluded profile, no novelty claim. The h7 characteristic decomposition
already appears in [the August26 audit](H7_BLOCK_SPECTRAL_DECOMPOSITION_AUDIT.md).
This note checks its uniform extension and the defect/nonsingularity step.

## Assumptions and notation

A is the adjacency matrix of a simple C4-free graph on49 vertices, minimum
degree7, with h in {1,3,5,7} degree8 vertices. Counting non-returning two-step
walks gives sum_(u~v)(d(u)-1)<=48. Thus degrees are7 or8; a high vertex has
only degree7 neighbors and all48 other vertices as distinct two-step endpoints.
In high/low order, with l=49-h,

    A = [0 B; B^T C],  BB^T=7I_h+J_h,  BC=J_(h,l),
    B1_l=8·1_h,  t=B^T1_h,  C1_l=7·1_l-t,  Ct=h·1_l.

Here J is an all-ones matrix of the indicated dimensions. All these identities
follow from actual graph hypotheses; none assumes regularity of A.

## Explicit support bound needed for positivity

Fix a low vertex v with k=t_v high neighbors S. Any other low vertex w shares
at most one member of S, since sharing two makes a C4 with v. For each high
vertex in S, BC=J says exactly one low neighbor of v is adjacent to it.
Consequently k=sum_(w~_C v)|N_B(w) intersect S|<=d_C(v)=7-k.
Thus every t_v<=3. This step remains valid when v,w are adjacent because
C4-free here forbids subgraphs, not merely induced cycles.

## Defect and its spectral radius

Define the low defect matrix

    D=J_l+6I_l-B^TB-C².

The full graph's common-neighbor bound makes D symmetric, entrywise
nonnegative, zero on the diagonal, with off-diagonal entries0 or1. Direct
substitution into the block identities yields

    D1=6·1-t,   DB^T=J_(l,h)-B^T,   Dt=h·1-t,   CD=DC.

For the commutator, CJ-JC=1t^T-t1^T and
CB^TB-B^TBC=1t^T-t1^T, which cancel.
Let a=(7+sqrt(49-4h))/2. Then a²-7a+h=0, a>3, a<7 and

    w=a·1-t>0,   Dw=(a-1)w.

The similarity diag(w)^(-1)D diag(w) is nonnegative with constant row sum
a-1. Its induced infinity norm bounds every eigenvalue in absolute value by
a-1, and w supplies that eigenvalue. Therefore rho(D)=a-1<6. This argument
requires no irreducibility assumption on D.

## Residual subspace and nonsingularity

K=ker(B) intersect 1_l^perp is C-invariant: BCy=Jy=0 and
<C1,y>=<7·1-t,y>=0 for y in K. On K, C²=6I-D. Since D is symmetric and
rho(D)<6, this restriction of C² is positive definite.
The remaining A-invariant summands are the paired high-difference spaces
(with eigenvalues ±sqrt7, each h-1 times), and span of
H=(1_h,0), L=(0,1_l), T=(0,t). The latter has column-action matrix

    Q = [0 8 h+7; 0 7 h; 1 -1 0].

Its characteristic polynomial is x³-7x²-7x+49-h, with nonzero constant term.
The spaces are independent: BB^T is positive definite and the Gram
calculation below places 1_l outside im(B^T). Their dimensions total49.
Thus A is nonsingular for all four profiles. This is a necessary consequence,
not a nonexistence proof.

## Rational Gram determinant check

For U=span(im B^T,1_l), its row-vector Gram matrix is

    M = [7I_h+J_h  8·1_h; 8·1_h^T  49-h].

Schur complementation gives det M=7^(h-1)(343-22h-h²)>0. Because K=U^perp
inside rational Euclidean space, its Gram determinant has the same rational
square class as det M: a combined rational basis has Gram determinant equal
to a rational square. Since h-1 is even, the factor7^(h-1) drops out.

| h | dim K | det M | Delta=343-22h-h² | square class |
| --- | --- | --- | --- | --- |
| 1 | 46 | 320 | 320 | 5 |
| 3 | 42 | 13132 | 268 | 67 |
| 5 | 38 | 499408 | 208 | 13 |
| 7 | 34 | 16470860 | 140 | 35 |

This is a rational-form statement. It does not assert that an integral
orthonormal basis exists, or by itself settle Z2 representability.
The Gram determinant for span(1,e,Ae) in the full graph is instead h²·Delta;
these are different bases/spaces and their integer determinants must not be
confused, although their square classes agree.

Verification: SymPy1.14.0 exact determinant calculation for all four M and
symbolic charpoly(Q) equality with h left symbolic passed. Numeric roots were
only inspected as a sanity check; no claim above depends on rounding.

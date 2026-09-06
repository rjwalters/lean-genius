# Binary rank obstruction for odd internal degree

Node: A.5.3 / A-REG-NONBIP / NONBIP-MIXED.

Status: uniform necessary condition under explicit completion consequences;
proof audit, not Lean. It strengthens the odd perfect-code obstruction,
but does not exclude all defect graphs or close A-REG-NONBIP.

## Statement and completion interface

Let D be the adjacency matrix of a finite simple graph. Suppose H is a
symmetric integer matrix such that:

- every diagonal entry of H is even;
- every row sum of H is odd;
- HD=DH;
- every diagonal entry of HD is even.

Then rank over F2 of D+I is even. No regularity of D, genuine perfect code,
C4 cap, or exterior matrix is needed for this conditional assertion.

In the weight-three carrier audit, H is simple cubic, commutation follows
from the completion identities, and even diag(HD) follows from the
symmetric integral cross equation and C Gram. Thus this theorem is a
necessary condition for any such completion, independently of B. More
generally it applies whenever those four inputs hold; an odd component
weight is useful only where it has already been linked to odd internal
degree. No unstated weight-to-degree implication is being supplied here.

## Quadratic proof using odd domination

Work over F2 and put M=D+I. The matrix HM=HD+H is symmetric and has zero
diagonal. Hence z^T HM z=0 for every vector z. If Mz=1, then

```text
0 = z^T H M z = z^T H 1 = z^T 1.
```

Every solution of the closed-neighborhood equation Mz=1 must therefore
have even weight. Such a solution always exists: if My=0, then
0=y^TMy=sum y_i, because M is symmetric with diagonal one. Thus 1 is
orthogonal to ker M, and lies in im M. Differences of solutions are in
ker M, so solution-weight parity is invariant.

Batal's Theorem 2.4 identifies this invariant parity with rank(M) modulo2:
[Parity of an odd dominating set, arXiv:2011.10270v3](https://arxiv.org/html/2011.10270v3).
Here “odd dominating” refers to odd closed-neighborhood counts, not to
odd cardinality of the selected set. Applying that theorem proves the claim.

## Independent linear-algebra verification of the rank step

The cited rank identity can also be derived without graph induction.
Choose a complement to the radical of the symmetric bilinear form M.
Its restriction is nonsingular, so congruence expresses M as a
nonsingular symmetric block plus a zero block. Inverting the first block
and transporting back gives a symmetric matrix G with MGM=M.
The operator MG is idempotent and has image im M, so
trace(MG)=rank(M) in F2. Put z=diag(G). Symmetry cancels all off-diagonal
terms in each diagonal entry of MGM, giving

```text
1 = diag(M) = diag(MGM) = M diag(G) = Mz.
trace(MG) = sum_i M_ii G_ii = sum_i z_i.
```

Consequently this solution has weight parity rank(M); all solutions have
the same parity by the kernel argument above. This verifies precisely the
rank identity used, and does not assume that M is invertible.

## Consequence for the interval carrier and remaining gap

For C=Z/(3q) and D steps q+1 through 2q-1, the three-point set
P={0,q,2q} satisfies (D+I)1_P=1 over the integers. It has odd size,
so rank_F2(D+I) is odd and the theorem excludes every eligible H.
This recovers the stronger arbitrary-H terminal in
NONBIP_MIXED_WEIGHT_THREE_TRIANGLE_FREE_GRAM_CUT.md without classifying H.

For other D, even binary rank is only a necessary condition. For example, on Z/48 take steps
`{24, ±1, ±2, ±3, ±4, ±5, ±6, ±8}`. This is 15-regular, connected
because step1 is present, and nonbipartite because 0,1,2 form a triangle.
Its closed-neighborhood binary rank is46, as the reproducible elimination
below checks. This does not give H,
B, or an ambient completion, and is not used in the proof. It prevents
inferring the required odd-rank hypothesis merely from those three graph
parameters. No broader exclusion is claimed, and no census is proposed.

The remaining mathematical link is a reason that actual completion data
either force odd rank for D+I or exclude the even-rank possibilities using
additional structure. Repackaging the same quadratic identity cannot
supply that link. The size-two characteristic-two quotient audit concerns
a different, degenerate invariant subspace and does not prove or refute
this closed-neighborhood rank condition.

## Triangle-free control: neither odd rank nor a perfect code is forced

The parameter-only implication fails even after imposing triangle-freeness.
`check_weight_three_triangle_free_even_rank.py` constructs a connected,
triangle-free, 15-regular D on 48 vertices with

```text
rank_F2(D+I) = 46,
```

and induced five-cycle `(0,17,34,3,22)`. It begins with the interval
graph on Z48 (steps17 through31, closed-neighborhood rank33), then applies
nine recorded degree-preserving switches. A tuple `(a,b,c,d)` deletes
edges `ab,cd` and inserts `ac,bd`. The checker verifies every deletion,
insertion, degree, triangle condition, and connectivity after every switch.
The final rank is computed by exact bit Gaussian elimination.

No perfect code exists in this D. Closed neighborhoods have size16,
so any perfect code would have size3; the checker also tests all such
triples directly and finds none. This independently confirms the perfect-code
failure without using Batal's rank theorem. It is a verification of one
explicit counterexample, not an enumeration of graphs or a nonexistence
claim about ambient graphs.

Run the standard-library verifier:

```sh
python3 research/problems/erdos-85-wip-01/check_weight_three_triangle_free_even_rank.py
```

Thus a connected nonbipartite weight-three defect graph with no triangles
need not have odd closed-neighborhood rank or an exact perfect code.
The counterexample has no supplied cubic commuting H, incidence B, or
ambient completion. The new rank obstruction remains valid, but its
missing odd-rank premise cannot follow from degree, order, connectedness,
nonbipartiteness, and triangle-freeness alone. This stops that proposed
extension of the interval-family terminal.

```python
steps = {24} | {s % 48 for j in (1, 2, 3, 4, 5, 6, 8) for s in (j, -j)}
assert len(steps) == 15 and 0 not in steps
basis = {}
for i in range(48):
    row = (1 << i) | sum(1 << ((i + s) % 48) for s in steps)
    while row:
        pivot = row.bit_length() - 1
        if pivot in basis:
            row ^= basis[pivot]
        else:
            basis[pivot] = row
            break
assert len(basis) == 46
```

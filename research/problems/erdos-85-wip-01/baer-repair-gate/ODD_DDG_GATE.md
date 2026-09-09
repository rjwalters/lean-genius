# Odd-degree divisible-design graphs with common-neighbor counts 0 and 1

**Theorem.** There is no simple k-regular graph with odd k>=3 whose vertices
can be partitioned into m>=2 groups of equal size h>=2, such that distinct
vertices in the same group have zero common neighbors and vertices in
different groups have exactly one common neighbor.

In standard notation this rules out every proper divisible-design graph
with odd degree and parameters lambda1=0, lambda2=1. There is no restriction
to a Baer seed, prime-power parameters, or a particular number of vertices.
It closes this design construction class for the odd-degree Erdős85 route.
It does not rule out arbitrary C4-free graphs, whose zero-common-neighbor
relation need not partition them into groups.

## Proof

Write v=mh and let K=I_m tensor J_h. The adjacency matrix A satisfies

    A²=kI+J-K,                 k(k-1)=h(m-1).       (1)

As in GRAM_GATE.md, regularity and (1) imply AK=KA. Thus the group partition
is equitable and its quotient R is a symmetric nonnegative integer matrix
with row sum k. Its square is

    R²=(k-h)I+hJ.

Each row therefore has both sum and squared sum k. The nonnegative integer
terms R_ij(R_ij-1) sum to zero, so R is a 0/1 matrix. In particular m>=k.
Equation (1), with k>=3, consequently gives h<=k.

For a vertex in group i, its R_ii within-group edges belong to no triangle,
and its k-R_ii cross-group edges each belong to exactly one triangle.
The latter count is twice the number of triangles at the vertex. Since k
is odd and R_ii is0 or1, R_ii=1 for every i. Therefore

    trace(R)=m,                 h is even.          (2)

The evenness follows because each diagonal block of A is a simple
1-regular graph on its h vertices, hence is a perfect matching.

Let U be the real subspace of vectors constant on each group, and W its
orthogonal complement. Both are A-invariant because A is symmetric and
commutes with K. The restriction to U is represented by R, so has trace m.
Since A has zero diagonal, its restriction to W has trace -m. On W both
J and K vanish, so (1) gives A²=kI there. Therefore

    -m=z sqrt(k) for some integer z.                (3)

Because m>0, this forces sqrt(k) to be rational, hence an integer a, and
a divides m. Thus k=a² and gcd(k,m-1)=1: every prime dividing k divides a
and m, and so cannot divide m-1. Applying Euclid's lemma to
h(m-1)=k(k-1) now shows k divides h.

Together with 0<h<=k, this gives h=k. But h is even by (2), while k is odd.
This contradiction proves the theorem.

## Relation to the Baer gate and source scope

GRAM_GATE.md is a special case with k=r²,m=r²+r+1,h=r²-r for odd r>=3.
Its direct complementary-plane trace proof remains valid independently.
The present proof needs neither that special quotient nor a plane completion.

The matrix and equitable-partition framework is standard; see Lemma2.1 and
Theorem3.1 in [Haemers, Kharaghani and Meulenberg, Divisible Design Graphs](https://www.cs.uleth.ca/~hadi/research/ddg-v4.pdf).
The proof above combines that framework with triangle parity and divisibility.
No claim of literature novelty is made. This is a uniform prose theorem,
not a finite computation or a Lean-formalized result.

Equivalently, for an odd-regular C4-free graph of degree at least3, the graph
joining distinct zero-common-neighbor pairs cannot be a disjoint union of
cliques. Indeed it is regular of degree v-1-k(k-1), so clique components
would all have the same size h=v-k(k-1). A single component would force
k<=1; singleton components would give v=k(k-1)+1 odd, contradicting the
handshake lemma for odd k. All remaining cases meet the theorem's hypotheses.

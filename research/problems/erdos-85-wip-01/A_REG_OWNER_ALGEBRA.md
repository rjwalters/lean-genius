# A-REG: the owner-coordinate algebra

Status: exact derivation from the proved component quotient and owner-graph
interfaces, 2026-08-17. This note targets the sole remaining binary
square-order gap after `squareOrder_regular_of_even` closed A-NONREG.

## 1. Setup

Let `G` be q-regular and C4-free on `q²` vertices, with q even, and let `D`
be its second-order defect graph. Write the connected components of `D` as
`c`, with

```text
|c| = q m_c,             sum_c m_c = q.
```

Let `A` be the adjacency matrix of `G`, let `P_c` be the diagonal projector
onto `c`, and let `O_c` be the owner graph for coordinate `c`. The proved
entrywise Gram formula is

```text
M_c := O_c + m_c I = A P_c A.
```

Each `O_c` is `m_c(q-1)`-regular, and the owner graphs edge-partition the
complement of `D`.

## 2. Cross-product identity

For distinct components `c != d`, the matrices satisfy

```text
M_c M_d = m_c m_d J.                         (OWNER-CROSS)
```

Indeed,

```text
M_c M_d = A P_c A² P_d A.
```

Insert the square-order identity

```text
A² = (q-1)I + J - D.
```

The `I` term vanishes because `P_c P_d=0`. The `D` term vanishes because `D`
has no edges between distinct connected components, hence `P_c D P_d=0`.
For the remaining term, `P_c J P_d = 1_c 1_d^T`, while the uniform component
quotient gives

```text
A 1_c = m_c 1,             A 1_d = m_d 1.
```

Thus the product is `m_c m_d J`.

Expanded in owner adjacency matrices, this is

```text
O_c O_d + m_d O_c + m_c O_d + m_c m_d I = m_c m_d J.   (1)
```

In particular all `O_c` commute pairwise. They also commute with `D`, since
`A`, `D`, and every component projector `P_c` commute in the required order.
The regular A-REG core therefore carries a simultaneous symmetric matrix
algebra, not merely an edge coloring.

Equation (1) has an exact graph-facing form:

```text
O_c O_d = m_c m_d (J-I) - m_d O_c - m_c O_d.             (1')
```

Thus, for distinct vertices `x,y`, the number of mixed two-walks whose first
edge is owned by `c` and second edge by `d` is

```text
m_d(m_c-1)   if xy is c-owned,
m_c(m_d-1)   if xy is d-owned,
m_c m_d      if xy is a D-edge or is owned by a third coordinate.
```

It is zero on the diagonal. This local intersection table is a fusion-scheme
law and is likely a more useful graph-theoretic interface than bare matrix
commutation.

## 3. Simultaneous spectral form

On the hyperplane `1^perp`, `J=0`, so OWNER-CROSS becomes

```text
(O_c + m_c I)(O_d + m_d I) = 0               (c != d).  (2)
```

Choose a simultaneous real eigenvector `v` in `1^perp`, and write `lambda_c`
for its `O_c`-eigenvalue. Then

```text
(lambda_c + m_c)(lambda_d + m_d) = 0          (c != d).  (3)
```

Hence at most one coordinate can have `lambda_c != -m_c`. This is the exact
spectral sparsity missing from the component-size partition alone.

Since the owner graphs partition the complement of `D`,

```text
sum_c O_c = J - I - D.
```

If `delta` is the simultaneous `D`-eigenvalue, then on `1^perp`

```text
sum_c lambda_c = -1-delta.
```

For a vector exceptional only in coordinate `e`, this gives

```text
delta = q - m_e - 1 - lambda_e.               (4)
```

The vectors with no exceptional coordinate have `lambda_c=-m_c` for all c
and therefore `delta=q-1`; these include the `(number of components)-1`
dimensional space of component-constant vectors orthogonal to `1`.

## 4. Exact moments and rank pressure

Because `O_c` is a loopless `m_c(q-1)`-regular graph on `q²` vertices,

```text
tr(M_c)   = m_c q²,
tr(M_c²)  = q² [m_c(q-1) + m_c²].
```

The all-ones eigenvalue of `M_c` is `m_c q`. Removing it leaves

```text
tr(M_c | 1^perp)    = m_c q(q-1),
tr(M_c² | 1^perp)   = m_c q²(q-1).             (5)
```

Moreover `M_c=A P_c A` is positive semidefinite. If `r_c` is its rank on
`1^perp`, Cauchy applied to its positive eigenvalues gives

```text
r_c >= m_c(q-1).                              (6)
```

By (2), the positive ranges of the different `M_c` on `1^perp` are mutually
orthogonal. Summing (6) yields

```text
sum_c r_c >= q(q-1).
```

Thus at least `q²-q` dimensions of `1^perp` are consumed by mutually
orthogonal owner-coordinate ranges; at most `q-1` dimensions remain in their
common kernel.

## 5. Decisive audit: the pure spectral algebra is a transport, not a terminal

The rank inequality is never the sharp information. Restrict the Gram block
to the columns indexed by `c`. Its square is

```text
P_c A² P_c = (q-1)I_c + J_c - D_c.
```

The connected graph `D_c` is `(q-1)`-regular. Therefore
`(q-1)I_c-D_c` is positive semidefinite with kernel exactly the constant
line, while `J_c` is strictly positive on that line and zero on its
orthogonal complement. The displayed matrix is positive definite. Hence the
columns of `A P_c` are independent and

```text
rank M_c = |c| = q m_c,
rank(M_c | 1^perp) = q m_c - 1.                (7)
```

Summing (7) gives `q²-r`, where `r` is the number of defect components. The
common kernel on `1^perp` consequently has dimension `r-1`. This is exactly
the component-constant subspace: a weighted combination of component
indicators orthogonal to `1` is killed by `A`, and conversely
`A²=(q-1)I+J-D` identifies `ker A ∩ 1^perp` with the `q-1` eigenspace of `D`.

More explicitly, if `u` is a nonconstant eigenvector of `D_c` with eigenvalue
`delta`, then transport by `A` produces an owner-coordinate vector with

```text
M_c-eigenvalue = q-1-delta,
O_c-eigenvalue = q-m_c-1-delta,
O_d-eigenvalue = -m_d                         (d != c).
```

Thus equations (2)-(5) reorganize the already known component spectra but do
not constrain them further. The owner algebra is valuable infrastructure and
a simultaneous-coordinate normal form, but **ordinary real spectral moments
of the owner matrices alone cannot close A-REG**. Any terminal must insert a
graph-specific condition not preserved by this transport—most plausibly the
selector disjointness/unique-owner laws or the internal cycle restrictions for
size-two parts.

## 6. Precise next statements

The immediate Lean target is OWNER-CROSS, followed by pairwise commutation.
Both are uniform structural theorems and use no finite certificate.

The remaining mathematical terminal can now be stated narrowly:

**GAP A-REG-OWNER-SPECTRUM.** Show that no family of simple regular owner
graphs with positive parts `m_c>=2`, `sum m_c=q=2^k`, can satisfy (1), the
owner edge partition, and the **component-selector intersection laws**. The
last condition is essential; deleting it leaves only the spectrally tautological
transport above.

Promising consumers are:

1. formalize (7) to prevent further searches for nonexistent rank slack;
2. express selector disjointness and unique ownership directly in the joint
   owner-matrix algebra (Hadamard products, not ordinary products);
3. combine those entrywise laws with trace-cube/triangle counts;
4. reduce the `m_c=2` case by inserting the already proved cycle quotient and
   selector-disjointness representation into (1).

This is now the highest-level open node in Track A.

## 7. Triangle inventory and its exact limitation

The first trace-cube calculation can be completed in closed form.  Write
`T(H)` for the number of (unoriented) triangles of a simple graph `H`, and
put `n=q^2`.  If `D_c` is the defect graph induced on a component of size
`q m_c`, then transport of the nonprincipal `D_c` eigenvalues through
`O_c=M_c-m_cI` gives

```text
T(O_c) =
  m_c q(q-1)(m_c^2 q - 3m_c q + q^2 + q - 2) / 6 - T(D_c).       (8)
```

OWNER-CROSS also determines every mixed-color triangle count.  For distinct
coordinates `c,d,e`,

```text
#(triangles with two c-edges and one d-edge)
  = q^2 m_c m_d (q-1)(m_c-1) / 2,                               (9)

#(triangles with one edge in each of c,d,e)
  = q^2 m_c m_d m_e (q-1).                                      (10)
```

Indeed, (9) is `tr(O_c^2 O_d)/2`; multiply (1') by `O_c` and use
`tr(O_cO_d)=0`, edge-disjointness, and regularity.  Equation (10) is
`tr(O_cO_dO_e)`; on an `e`-owned edge the mixed-walk entry in (1') is
`m_cm_d`.

For binary `q>=8`, the polynomial term in (8) is divisible by `8`.  To see
this, `q` supplies a factor `8`; the remaining product supplies a factor `2`
because either `m_c` is even or the parenthesis is even, and supplies a
factor `3` by considering `q mod 3`.  Consequently

```text
T(O_c) = -T(D_c)  (mod 8).                                      (11)
```

This congruence does **not** close A-REG.  The mixed counts (9)-(10) vanish
modulo `8`, so summing (11) merely recovers the standard complement-triangle
identity for the `(q-1)`-regular graph `D`; its constant term is itself
divisible by `8` (in fact by a substantially larger power of two).  Thus raw
triangle totals, like raw real spectra, are transport rather than a terminal.

There is, however, a sharper graph-specific normal form when `m_c=2`.
The proved selector equivalence identifies ambient vertices with the edges of
`H_c := complement(D_c)`.  Under this bijection, `O_c` is exactly the line
graph `L(H_c)`: two selectors are owner-adjacent precisely when the
corresponding two edges intersect.  Hence

```text
T(O_c) = 2q * choose(q,3) + T(H_c).                              (12)
```

Substitution into (8) is again an identity, using the complement-triangle
formula for `D_c` and `H_c`; triangle *counts* alone lose the selector data.
The useful next object is therefore the full line-graph identification (or
its Hadamard adjacency identity), combined across two different size-two
coordinates.  Cross-coordinate compatibility is information absent from
each individual spectrum and from (8).

## 8. Two size-two coordinates are orthogonal edge bijections

The cross-coordinate content of the preceding line-graph form has a compact
purely combinatorial statement.  Suppose `m_c=m_d=2`, let

```text
H_c = complement(D_c),       H_d = complement(D_d),
```

and use the two selector equivalences to label every ambient vertex `x` by
an edge `e_c(x)` of `H_c` and an edge `e_d(x)` of `H_d`.  Both graphs have
`2q` vertices, are `q`-regular, and have `q^2` edges.  The resulting edge
bijection

```text
phi_cd : E(H_c) -> E(H_d),       e_c(x) |-> e_d(x)
```

has the orthogonality property

```text
intersecting edges of H_c map to disjoint edges of H_d.             (13)
```

This is just edge-disjointness of the owner colors: intersection is
adjacency in the corresponding line graph.  It has a stronger equivalent
star form.  For every vertex `u` of `H_c`, the `q` edges in its star map to
`q` pairwise disjoint edges of `H_d`; since `H_d` has `2q` vertices, they
form a perfect matching.  Thus the `2q` stars of `H_c` become a two-fold
perfect-matching cover of `H_d`.  Matchings indexed by adjacent vertices of
`H_c` share exactly the image of their common edge, while matchings indexed
by nonadjacent vertices are disjoint.

In incidence-matrix notation this becomes especially transparent.  Let
`B_c,B_d` be the `q^2 by 2q` unsigned incidence matrices of `H_c,H_d`, with
rows identified by the ambient vertices.  Then

```text
B_c^T B_d = J_(2q).                                               (14)
```

Indeed, a vertex of `D_c` and a vertex of the distinct defect component
`D_d` are a non-defect pair, hence have exactly one common ambient neighbor.
Conversely, (14) says every `c`-star maps to a perfect matching in `H_d`.
It also immediately recovers OWNER-CROSS in this case:

```text
(B_c B_c^T)(B_d B_d^T) = B_c J B_d^T = 4J.
```

This reduction isolates the missing invariant more sharply than triangle
counts: rule out a sufficiently large family of pairwise orthogonal edge
bijections between connected-complement `q`-regular graphs on `2q` vertices.
The qualifier is essential.  `K_(q,q)` admits the familiar Latin-square
models of such orthogonality, but its complement is two disjoint `q`-cliques
and therefore represents two forbidden unit defect parts, not one connected
size-two part.  A terminal must use connectedness of each `D_c` (equivalently,
exclude this split model), rather than orthogonality alone.

Over `F_2`, a connected `H_c` has unsigned incidence rank `2q-1`, and (14)
reduces to a rank-one cross pairing.  The even-coefficient subspaces of
dimension `2q-2` from different size-two coordinates are mutually
orthogonal.  For `q/2` size-two coordinates their dimensions sum to
`q(q-1)`, exactly the same saturated dimension already seen over the reals.
So a bare mod-two rank count is again tight; a successful characteristic-two
argument must use the induced alternating/quadratic forms or the exclusion
of the split `K_(q,q)` model.

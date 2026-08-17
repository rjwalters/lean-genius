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

### 8.1 The first `F_2` radical is also visible blockwise

Let `K_c` be the adjacency matrix of `H_c` over `F_2`.  Because `q` is even,
`K_c` is alternating and kills the constant vector.  Its rank is even, so

```text
nullity(K_c) is even and at least 2.                              (15)
```

There is a useful sharp dichotomy.  Either `ker K_c` contains a nonconstant
even-weight vector, or `nullity(K_c)=2` and every nonconstant radical vector
has odd weight.  This follows by restricting the coordinate-sum functional
to the even-dimensional kernel: its even-weight kernel already contains the
constant vector.

If `a` is a nonconstant even-weight radical vector and `u=B_c a`, then
`u` is nonzero (the connected graph `H_c` has incidence kernel equal to the
constant line), and (14) gives

```text
u^T B_d = a^T J = 0       for every d != c,
u^T B_c = a^T K_c = 0.
```

Thus `u` lies in `im(A) cap ker(A)` for the ambient adjacency matrix reduced
modulo two.  This initially looks like extra global kernel pressure, but the
square relation shows exactly where it lives: on the `c` block,

```text
A^2|_c = I + J + D_c = adjacency(H_c) = K_c   (mod 2).           (16)
```

Consequently (15) is already the blockwise nullity of `A^2`; counting these
radicals without their quadratic form is tautological.  A viable next test
must distinguish the Witt/Arf type of these radicals, or prove that the
connected-complement condition forbids the nullity-two odd-radical escape.

### 8.2 Prior art and counterchecks

The perfect-matching cover above has established terminology.  When
`H_c=H_d`, the matchings indexed by `V(H_c)` form an **orthogonal double
cover (ODC)** of `H_c` by independent-edge pages: every host edge occurs in
exactly two pages, and two pages meet in one edge exactly when their indices
are adjacent.  For distinct `H_c,H_d`, our structure is the corresponding
cross/mutual version.  The directly relevant prior-art source is:

```text
S. Hartmann and U. Schumacher,
"Orthogonal double covers of general graphs",
Discrete Applied Mathematics 138 (2004), 107-116,
doi:10.1016/S0166-218X(03)00274-9.
```

Its abstract explicitly singles out ODCs whose pages are isomorphic sets of
independent edges.  Before building a new parity theory, its existence and
classification results should be checked against degree `q`, order `2q`, and
page `q K_2`.  Our multi-coordinate object asks for several mutually
compatible such covers, which is stronger than one ODC.

Two cheap computational checks prevent overstatement:

* Connectedness of `D_c` does not by itself exclude the nullity-two
  odd-radical case.  Random `q`-regular graphs with connected complements
  realize both Arf values already at `q=8`.
* The full matching-cover compatibility exists at `q=4` with connected
  complement: an exact SAT model found a self-ODC of a 4-regular graph on
  eight vertices by four-edge perfect matchings.  Thus (13)-(14) plus
  connected `D_c` are not uniformly contradictory.  This is consistent with
  `q=4` being an exceptional order, and shows that a terminal must use either
  the binary range `q>=8` in an essential way or compatibility among more
  than two coordinates.

The `q=8` self-ODC feasibility test is much harder; a direct permutation SAT
encoding did not reach a verdict in a short run.  No conclusion should be
drawn from that timeout.

### 8.3 The extra condition absent from abstract ODCs: self-indexed cycles

An arbitrary ODC by perfect matchings still forgets an essential part of the
square-order graph.  The edge labels of `H_c` are the ambient vertices `V`,
while its ground vertices are the actual subset `c.supp` of `V`.  Hence the
`2q` labels lying in `c` are distinguished, and their incidence with the
ground set is forced by the internal ambient graph:

```text
e_c(x) = N_G(x) cap c             for x in c.                    (17)
```

When `m_c=2`, `G[c]` is a disjoint union of cycles (with no 4-cycle).  On a
cycle written cyclically, (17) says

```text
e_c(x_i) = {x_(i-1), x_(i+1)}.                                  (18)
```

Thus the `2q` distinguished edges of `H_c` indexed by `c` themselves form a
2-factor: an odd internal cycle stays one cycle under the distance-two map,
whereas an even internal cycle splits into its two parity cycles.  In matrix
language, if rows and columns are both restricted to `c`, the incidence
matrix `B_c` is not arbitrary but is the symmetric adjacency matrix of
`G[c]`:

```text
B_c[c,c] = Adj(G[c]).                                             (19)
```

Over `F_2`, a cycle block of length `ell` in (19) has nullity `1` for odd
`ell` and nullity `2` for even `ell`; its kernel consists of constant vectors
in the odd case and the two parity-class constants in the even case.

This identifies the correct strengthened design problem.  We do not merely
need an ODC (or a mutual pair of ODCs) by perfect matchings.  We need a family
whose edge labels are partitioned into the ground sets of all coordinates,
such that every diagonal label block is the symmetric cycle incidence (19),
every off-diagonal pair obeys `B_c^T B_d=J`, and defect adjacency is
simultaneous disjointness in every coordinate.  The `q=4` ODC countermodel
above was not checked against (19), so it does not refute this stronger
self-indexed statement.  This diagonal cycle constraint is the first
graph-specific datum in the size-two reduction that is absent from ordinary
ODC theory and from all preceding spectral transports.

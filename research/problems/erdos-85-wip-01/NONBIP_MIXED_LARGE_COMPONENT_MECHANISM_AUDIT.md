# NONBIP-MIXED large-component mechanism audit

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED`, with at least one
normalized component weight `m_c >= 3`.

Status: q-generic positive algebraic reduction; no terminal claimed.

## Candidate: count every mixed owner triangle exactly

Let `q = 2^k`, let the defect-component weights be positive integers
`m_1,...,m_r` with sum `q`, and write `O_i` for the adjacency matrix of the
owner graph of component `i`.  The owner graphs partition the edges of the
complement of the defect graph.  The already-banked shifted cross-product
law says, for `i != j`,

```text
(O_i + m_i I)(O_j + m_j I) = m_i m_j J.             (1)
```

Taking traces after one further owner factor determines both possible kinds
of non-monochromatic owner triangle.

For two distinct colours,

```text
tr(O_i^2 O_j)
  = q^2 (q-1) m_i m_j (m_i-1).                       (2)
```

Indeed, expand `O_i O_j` from (1), multiply by `O_i`, and use
`tr(O_i)=tr(O_i O_j)=0` and
`tr(O_i J)=tr(O_i^2)=q^2 m_i(q-1)`.  Each triangle with two `i`-edges and
one `j`-edge is counted twice by (2), once in each orientation.

For three distinct colours, the banked theorem
`binarySquare_regular_trace_three_distinct_ownerMatrices` gives

```text
tr(O_i O_j O_l) = q^2 (q-1) m_i m_j m_l.             (3)
```

For a fixed ordering of three distinct colours, each rainbow triangle is
counted once.  Since owner colours partition complement edges, (2)--(3)
therefore give the exact unsigned deficit

```text
Delta = binarySquareMixedOwnerTriangleDeficit G
      = q^2(q-1)/2 *
          (sum_{i<j} m_i m_j(m_i+m_j-2)
             + 2 sum_{i<j<l} m_i m_j m_l).           (4)
```

Writing `e_2 = sum_{i<j} m_i m_j` and
`e_3 = sum_{i<j<l} m_i m_j m_l`, the bracket simplifies exactly to

```text
(q-2)e_2 - e_3.                                      (5)
```

The simplification follows from Newton's identities:
`sum_{i<j} m_i m_j(m_i+m_j) = q sum_i m_i^2 - sum_i m_i^3`.

## Exact theorem proposed before Lean

```text
binarySquare_regular_mixedOwnerTriangleDeficit_eq_partitionPolynomial
  : binarySquareMixedOwnerTriangleDeficit G
      = q^2 * (q-1) / 2 * ((q-2) * e2(m) - e3(m))
```

The graph-facing proof should be split into reusable statements:

1. a two-colour trace/count theorem derived from (1);
2. a disjoint partition of non-monochromatic complement triangles into
   their two-colour and three-colour cases;
3. a purely integral symmetric-polynomial simplifier avoiding division
   until evenness is established.

At the faithful `q=4`, `[2,2]` control, (4) gives `Delta = 192`.  Direct
enumeration from `sixteenRegularEdges` independently gives 272 complement
triangles: 80 monochromatic and 192 mixed, split as 96 of colour pattern
`(0,0,1)` and 96 of `(0,1,1)`.  Thus the identity deliberately survives the
known exception and its orientation factors are calibrated against an
actual ambient graph, not only symbolic traces.

## What it buys, and the remaining honest gap

This upgrades the existing quantum statement
`2^(2k-1) | Delta` to a complete partition-only value.  In particular the
old divisibility is automatic: the bracket in (4) is even, since every term
`m_i m_j(m_i+m_j-2)` is even.  Consequently the exact formula alone cannot
close `NONBIP-MIXED`; it contains no internal-component geometry.

It does isolate a sharper consumer interface for the neglected
`m_c >= 3` branch.  A terminal now needs a component-sensitive upper bound
on mixed owner triangles that is strictly below (4), or a forbidden local
configuration forced by equality in (2).  The latter is the more plausible
route.  The banked theorem
`binarySquare_regular_ownerEdge_coloredTwoStepMiddles_card` already fixes
the value `m_j(m_i-1)` on every individual `i`-owner edge, so merely
localizing the trace to endpoints is not new.

The next genuinely structural candidate is the **punctured owner rectangle**.
If `xy` has `i`-owner center `u in C_i`, then the exact count should refine
to a canonical bijection

```text
((N_G(y) intersect C_i) \ {u}) x (N_G(x) intersect C_j)
    ~= {z : y --[O_i] z --[O_j] x}.                  (6)
```

Existence and uniqueness use the cross-component common-neighbor theorem;
the omitted `u` is exactly what prevents the routed middle from collapsing
to `x`.  Cardinality of (6) recovers `m_j(m_i-1)`, but the labeled bijection
retains information discarded by (2).  For a defect edge inside the
connected component `C_i`, the already-banked unpunctured rectangle routing
has all `m_i m_j` cells.  Comparing (6) along successive internal defect
edges is therefore a concrete holonomy/compatibility probe for a large
component.  It is not the eliminated size-two double-shift invariant: its
fibres have size `m_i-1 >= 2` and retain the actual center labels.

### Small-cycle probe and cut

A labeled satisfiability probe at `q=8`, `(m_i,m_j)=(3,2)` imposed selector
sizes, pairwise C4 intersection at most one, and full routed rectangles on
base cycles of lengths three and five.  Both instances are SAT.  This is not
surprising after identifying the witness: it is a restriction of the affine
selector countermodel already recorded in `A_REG_CROSS_BLOCK_BUDGET_AUDIT`.
Affine lines provide the roots, points in selected coordinate fibres provide
the labeled centers, and every cross-fibre center pair lies on a unique line.
Hence all full and punctured rectangles close without collision.

The witness also identifies the exact missing hypothesis.  An aggregate
weight-three block in the affine model is a union of three coordinate fibres;
it is not a connected component of the formal defect relation.  Accordingly,
the probe does **not** refute a transport theorem using self-indexing and
connected nonbipartite `D[C_i]`.  It does refute any claimed odd-cycle
contradiction derived from labeled rectangle routing and C4 uniqueness alone:
one can simply select three or five mutually disjoint parallel affine lines
as the displayed base cycle at that weakened interface.

A credible next theorem must therefore use the fact that the roots traversed
by the odd cycle are themselves labels in the same component `C_i`, and
couple each root's selector to its position in `D[C_i]`.  It must show that
this self-indexed transport forces either a repeated routed middle (hence a
C4) or an impossible permutation on one of the labeled center fibres.
Without that consumer, (6) is another exact interface and should not yet be
atomized in Lean.

### An internal self-indexing relaxation is also insufficient

The phrase "use self-indexing" still hides a second gap.  The durable
countermodel checked by
`verify_nonbip_mixed_internal_self_index_countermodel.py` has `q=8`,
`m_i=3`, and 24 labels.  Its formal internal selector graph `K` is a simple cubic
graph with maximum pair codegree one.  Its formal defect graph `D` is
7-regular, connected, and contains a triangle.  For every `D`-edge `xy`,
the internal selectors `N_K(x)` and `N_K(y)` are disjoint.  Thus it satisfies
the exact self-indexed internal consequences

```text
y in N_K(x) <-> x in N_K(y),
|N_K(x)| = 3,
|N_K(x) intersect N_K(y)| <= 1,
D.Adj x y -> Disjoint (N_K(x)) (N_K(y)),
```

while already containing the shortest odd defect cycle.  The verifier checks
all pairs and all defect edges directly and prints a canonical model digest.

This is a relaxation countermodel only.  It does not realize a full ambient
`G`, simultaneous exterior-owner rectangles, the owner-matrix cross law, or
the canonical Baer operator `K = Omega triangle (D minus T)`.  It cuts an
odd-cycle argument using only the enumerated internal diagonal-selector
axioms.  A surviving mechanism must couple that self-indexed block to at
least one exterior component through the labeled full/punctured rectangles.
That simultaneous coupling -- not oddness, connectivity, self-indexing, or
rectangle routing separately -- is the precise remaining target.

Thus any successful argument must use where the closures lie relative to
the self-indexed component `C_i` and its connected nonbipartite defect graph.
Scalar triangle totals, like the earlier scalar cross-block budgets, are
exhausted.

This audit therefore records one positive q-generic theorem candidate and a
precise failure boundary.  It does not assert that a large component is
excluded.

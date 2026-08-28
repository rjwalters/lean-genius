# Size-two intermediate-factor tiling

Node: `A-REG-NONBIP / NONBIP-MIXED`, all normalized component weights two.

Status: exact non-arithmetic reformulation, isolated in divergence round 99.

## Block form

Let the defect components be `C_1,...,C_r`.  In the all-size-two branch,

```text
|C_c| = 2q,             r = q/2.
```

Write

```text
X_cd := A[C_c,C_d].
```

Every `X_cd` is a `2q by 2q` zero--one matrix with every row and column sum
two.  Symmetry of the ambient adjacency matrix gives

```text
X_dc = X_cd^T,
```

and `X_cc` is the symmetric adjacency matrix of the internal ambient cycle
2-factor on `C_c`.

For distinct `c,d`, the cross-component block of

```text
A^2 = (q-1)I + J - D
```

is `J`, because `D` has no edges between its components.  Therefore

```text
sum_e X_ce X_ed = J_(2q).                              (1)
```

## Exact support tiling

Each product in (1) is a nonnegative integral matrix.  Its row and column
sums are four:

```text
(X_ce X_ed) 1 = 4 1,
1^T (X_ce X_ed) = 4 1^T.
```

Since the sum of all `r=q/2` products is the zero--one matrix `J`, no entry
of any product can exceed one, and distinct products cannot share a support
entry.  Consequently:

> For every ordered pair of distinct component colors `(c,d)`, the `r`
> bipartite graphs with biadjacency matrices `X_ce X_ed`, indexed by the
> intermediate color `e`, are disjoint 4-regular spanning graphs whose edge
> sets partition `K_(2q,2q)`.

Equivalently, for every `x in C_c` and `y in C_d`, there is a unique
intermediate color `e` and a unique vertex `z in C_e` with

```text
A(x,z) and A(z,y).
```

The uniqueness of `z` inside a fixed `e` is exactly the statement that
`X_ce X_ed` is zero--one; uniqueness of `e` is disjointness of the supports.

## ODC interpretation

Fix a selector color `c`.  Its selector graph `H_c` has ground set `C_c`
and edge set labeled by all ambient vertices.  The rows belonging to a
component `C_e` form a labeled 2-factor of `H_c`.  Under the ambient edge
bijection from `H_c` to `H_d`, the star of any ground vertex becomes a
perfect matching.  Equation (1) says that these star matchings, resolved by
the intermediate component containing their common edge label, tile every
ordered cross pair exactly once.

This is the support-level form of mutual orthogonal-double-cover coherence.
It is stronger than pairwise line-graph disjointness or ordinary ODC
existence: it retains all intermediate colors simultaneously and is
compatible with transpose reciprocity.

## Scope

The identity is structural, not yet contradictory.  At `q=4`, the
formalized `sixteenRegular` graph realizes it with two intermediate colors.
Ordinary permutation-sheet decompositions of the 2-factors are noncanonical,
so a successful consumer should use the four-regular supports themselves.

The remaining non-arithmetic terminal can now be stated narrowly:

> Rule out, for binary `q>=8`, a reciprocal family of two-regular blocks
> satisfying the complete intermediate-factor tilings (1), the symmetric
> diagonal cycle placements, and connected nonbipartite defect complements.

Promising consumers are a support-level Latin-rectangle obstruction, a
coherent multi-color trade rigidity theorem, or an equality classification
of the mutually placed star-clique geometries.  Spectral ranks and raw
determinants forget the support partition and have already been audited.

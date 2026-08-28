# NONBIP-MIXED Cauchy--Binet reciprocity audit

Node: `A-REG-NONBIP / NONBIP-MIXED`; divergence round 96.

Status: exact `q=4` negative audit.  Pairing the distinguished
whole-component incidence minors does not control the first nonzero 2-adic
layer of a component Gram determinant.

## Candidate

For a normalized size-two defect component `C`, put

```text
B_C := A[:,C].
```

The selector equivalence identifies `B_C` with the unsigned edge--vertex
incidence matrix of the `q`-regular graph
`H_C = complement(D[C])`.  Hence

```text
B_C^T B_C = q I + Adj(H_C) = L(D[C]) + J,
det(B_C^T B_C) = (2q)^2 tau(D[C]).                 (1)
```

The ambient defect-component partition also partitions the rows of `B_C`
into square blocks `A[E,C]`.  In the all-size-two branch each such row block
is the incidence matrix of a labeled 2-factor of `H_C`, and reciprocity gives

```text
A[E,C]^T = A[C,E].                                (2)
```

It is tempting to combine (2) with Cauchy--Binet, pair the off-diagonal
component minors, and leave a diagonal residue controlled by the
self-indexed cycle factor `A[C,C]`.

## Full faithful enumeration

The formalized `sixteenRegular` graph has two eight-vertex defect components.
For either component, `B_C` is a `16 by 8` matrix, so its complete
Cauchy--Binet expansion has

```text
choose(16,8) = 12870
```

full minors.  Exact integer enumeration gives, for both components,

```text
absolute determinant       number of row subsets
0                           7174
2                           5504
4                            192
```

and therefore

```text
det(B_C^T B_C)
  = 5504 * 2^2 + 192 * 4^2
  = 25088
  = 2^9 * 7^2,                                      (3)
```

agreeing with the previously banked Smith and tree calculation
`tau(D[C]) = 392 = 2^3 * 7^2`.

The unsigned-incidence interpretation explains why a nonzero minor has
absolute determinant a power of two: its selected spanning subgraph is a
disjoint union of odd-unicyclic components, with one factor two per
component.  What matters here is which row subsets realize the lowest layer.

Every distinguished whole-component minor `A[E,C]` is zero.  The diagonal
blocks have rank six and the off-diagonal blocks rank seven.  In contrast,
the `5504` lowest nonzero minors use mixed row subsets.  For the first owner
component, their distribution by the number of selected rows in the first
defect component is

```text
rows from first component      1    2     3     4     5    6
number of |det|=2 minors      64  416  1408  2080  1280  256.
```

For the second owner component the reciprocal distribution occurs in row
counts `2,...,7`:

```text
rows from first component      2     3     4     5    6   7
number of |det|=2 minors      256  1280  2080  1408  416  64.
```

Thus (2) pairs the zero whole-component minors but supplies no map on the
mixed row subsets that actually determine the first nonzero layer.  Even the
deep valuation in (3) is an aggregate cancellation:

```text
5504 + 4 * 192 = 6272 = 2^7 * 49.
```

It is not read off from the distinguished 2-factors.

## Verdict

**The raw 2-factor-minor reciprocity route is cut.**  A surviving
Cauchy--Binet argument would need a canonical involution or congruence on
arbitrary mixed odd-unicyclic row sets, not merely transpose reciprocity of
the component blocks.  No such map follows from (2), and the faithful
exception shows that all whole-component terms may vanish while mixed terms
carry the entire determinant.

This does not refute the global tree-product square condition.  It isolates
why extracting a local 2-adic residue from that condition requires more than
the component 2-factorization.

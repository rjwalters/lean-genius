# Colored fourth-moment audit

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## Candidate and notation

Round 13 independently prioritized a colored block fourth moment.  Fix a
source difference fibre `t`.  For every target difference fibre `u`, let
`A_u=A_tu` be the zero-one incidence matrix from the `q` source cells in `t`
to the `q` target cells in `u`, and put

```text
R_u = A_u A_u^T.
```

The diagonal entry `R_u(x,x)` is the degree `d_u(x)` from source base `x`
into fibre `u`.  For `x != z`, `R_u(x,z)` is the number of common target
cells in fibre `u` of the two source cells.

The most immediate proposed statistic was

```text
tr(R_u R_v) = ||A_u^T A_v||_F^2.
```

It appears to retain the target-fibre colors `u,v` and has a transpose on
both sides.  In fact the full cap makes it collapse before reciprocity is
used.

## Exact collapse under the full cap

The full same-fibre cap for `t` says

```text
sum_u R_u(x,z) <= 1                 (x != z).
```

All terms are natural numbers.  Consequently:

1. every off-diagonal `R_u(x,z)` is zero or one; and
2. for `u != v`, the off-diagonal supports of `R_u` and `R_v` are disjoint.

Since each `R_u` is symmetric, direct expansion gives, for distinct colors,

```text
tr(R_u R_v)
  = sum_x d_u(x)d_v(x)
    + sum_{x != z} R_u(x,z)R_v(x,z)
  = sum_x d_u(x)d_v(x).
```

For one color the corresponding formula is

```text
tr(R_u^2)
  = sum_x d_u(x)^2
    + 2 |{{x,z} : x != z and R_u(x,z)=1}|.
```

Thus the entire table `tr(R_u R_v)` contains only the local block-degree
vectors and the already-known colored owner-pair support sizes.  It has no
new interaction between colors.  By cyclicity of trace,

```text
||A_u^T A_v||_F^2 = tr(R_u R_v),
```

so presenting the same quantity as a mixed transpose product does not retain
additional information.

This argument is not restricted to translation invariance.  In the TI
specialization the degree vectors are constant, say `d_u(x)=k_u`, and the
collapse is even more explicit:

```text
tr(R_u R_v) = q k_u k_v                     (u != v),
tr(R_u^2)   = q k_u^2 + 2q s_u,
```

where `s_u` is the number of positive nonzero-shift autocorrelation
coefficients up to orientation.  A probe dump of this table would merely
recount the cap supports, so none was added.

## What remains genuinely colored

The fixed-source-fibre fourth moment is **cut** as a source of a new
identity.  The failure is precise: multiplication of two matrices `R_u`
compares the same owner pair in two colors, and the cap has already declared
those supports disjoint.

A viable noncommutative trace must traverse at least three distinct fibre
indices before closing, for example a term shaped like

```text
tr(A_tu A_uv A_vt)
```

or a degree-four closed walk with a genuine fibre cycle.  Only then does
`A_ut=A_tu^T` identify entries belonging to *different source fibres*, which
is the information absent from the directed q=8 model.  Equivalently, any
surviving identity must not be expressible solely through the family
`{A_tu A_tu^T}_u` for one fixed `t`.

This narrows the round-13 consensus target: retain a cyclic word of block
indices (or a group-ring color) through transpose, rather than a colored
decomposition of the already-capped owner Gram matrix.

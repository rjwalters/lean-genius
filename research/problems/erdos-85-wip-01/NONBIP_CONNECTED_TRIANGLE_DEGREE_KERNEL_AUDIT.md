# NONBIP-CONNECTED triangle-degree kernel audit

Date: 26 August 2026.  Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: exact algebraic simplification and positive q4 calibration, not a
proof of the remaining local identity.

## Direct terminal hidden in the affine potential

Let `t_x` be the number of A-triangles through `x`, and let `K` be the graph
of A-edges lying in no triangle.  The affine-potential audit proposed

```text
(T1)  sum_{y in N_K(x)} t_y
        = t_x^2 - (q+1)t_x + (q^2+2)/3,
(T2)  sum_{x in tau} t_x = q+1  for every A-triangle tau.
```

These two pointwise identities have a much shorter common consumer.  At a
vertex `x`, the triangle edges through `x` contribute

```text
t_x (q+1-t_x)
```

to the sum of neighboring triangle degrees: each of the `t_x` triangles
contributes the other two entries in (T2), namely `q+1-t_x`.  Adding (T1)
cancels every `t_x` term and gives

```text
(AT)  sum_{y in N_A(x)} t_y = (q^2+2)/3.              (1)
```

Thus T1+T2 imply the single vector identity

```text
A t = ((q^2+2)/3) 1.
```

Since `A1=q1`, the integral vector

```text
w = 3q t - (q^2+2)1
```

satisfies `Aw=0`.  It is nonzero for every `q>=3`: otherwise
`3q t_x=q^2+2` at every vertex, which would imply `q | 2`.
Consequently (1) alone closes `NONBIP-CONNECTED` uniformly.  It needs no
invertibility assumption on the triangle core `M`, no Schur case split, and
no mod-nine residue terminal.

There is an equivalent form which displays the connectedness hypothesis
directly.  From `A^2=L_D+J`, equation (1) gives

```text
L_D t = (q(q^2+2)/3 - sum_x t_x) 1.
```

Every Laplacian row sum is zero, so summing coordinates forces the scalar on
the right to vanish.  If `D` is connected, `ker L_D` consists of the constant
vectors, hence `t` is constant.  Its forced value
`(q^2+2)/(3q)` is not integral because `q` does not divide 2.  This is the
same contradiction as the explicit A-kernel argument, but it explains
exactly where connected deficiency enters: (1) makes the triangle-degree
vector D-harmonic.

## Triangle-free-degree form

Write `k_x=deg_K(x)`.  C4-freeness and q-regularity give
`k_x=q-2t_x`.  Equation (1) is therefore equivalent to

```text
(AK)  sum_{y in N_A(x)} k_y = (q^2-4)/3.              (2)
```

This uses only the already-formalized `triangleFreeEdgeGraph`.  Its explicit
kernel vector is

```text
v = 3q k - (q^2-4)1,
```

because `Av=0` follows from (2).  Under the intended `q=2^k`, `k>=3`
range, `v` cannot vanish since that would force `q | 4`.

The existing generic commutator row formula rewrites

```text
sum_y [A,K]_(x,y)
  = sum_{y in N_A(x)} k_y - q k_x.
```

It does not prove (2): its global sum is identically zero by A-regularity.
The incidence-bottleneck diagonal `E_xx=k_x-1` also records `k`, but the
banked bottleneck theorem supplies only a global lower energy bound.  Thus
(2) is a genuinely new weighted-neighbor assertion, not a consequence of
the current commutator or energy ledgers.

## Calibration and scope

The all-256 q4 affine probe verifies T1 and T2 and hence (1)/(2) on every
sample.  This is positive evidence only; those controls have disconnected
deficiency.  Outside-first searches found standard local triangle-count and
polarity-graph identities but no theorem forcing (1) or (2) for a regular
C4-free graph at square order.

The honest new bridge is therefore:

> Prove that the A-neighbor sum of the triangle-free degree is the constant
> `(q^2-4)/3`, using connectedness of the deficiency graph and the
> self-indexed relation `K=A intersection D`.

This target is weaker than proving T1 and T2 separately and, unlike their
global arithmetic corollary, closes every binary exponent class at once.

## Actual connected-defect even-degree counterexample (2026-09-06)

The intended binary-degree restriction is essential to any attempted proof
of this bridge. Boza's [arXiv:2409.12770v2, Section 3, Lemma 9](https://arxiv.org/pdf/2409.12770v2)
identifies H36 as [House of Graphs 56942](https://houseofgraphs.org/graphs/56942).
The offline [verifier](verify_boza_h36_triangle_control.py) stores the API's
adjacency list and independently checks simplicity, degree 6 at all 36
vertices, and at most one common neighbor for all 630 distinct vertex pairs.
Thus this is an actual regular C4-free graph at square order, not a reduced
spectral or fractional control.

Its defect D is connected and nonbipartite. Its distance-three graph
E = D minus A is also connected. Triangle degrees are 2 at 12 vertices and
3 at 24 vertices; each of D and E has 30 edges joining unequal triangle
degrees. Its 32 triangles have degree sums 6 (once), 8 (21 times), and
9 (10 times), so none satisfies T2's value q+1=7. The entries of At are
14, 15, 16, 17, and 18, so AT fails as well (its proposed value is 38/3).
The proved triangle-edge bound t_u+t_v >= q/2+1 still holds on every
triangle edge.

Consequently, even degree, square order, connected nonbipartite D, and
connected E do not imply T2, AT, D-harmonic triangle degree, or constancy of
triangle degree on distance-three components. Any binary-q proof must use
an additional restriction not satisfied at q=6. This does not refute the
binary-q bridge, supply an unbounded graph family, or resolve Erdős 85.

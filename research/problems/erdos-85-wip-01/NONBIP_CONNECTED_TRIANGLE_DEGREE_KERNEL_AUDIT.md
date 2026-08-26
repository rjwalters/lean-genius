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

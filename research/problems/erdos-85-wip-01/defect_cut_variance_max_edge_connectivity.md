# Defect cut variance and maximal edge connectivity

Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.

Status: q-generic hand proof, independently audited in squad review #16.
This is structural progress, not a terminal contradiction.  The companion
script exhausts every shore of the banked q=4 fixed-free control.

## Setup

Let `A` be a symmetric loopless q-regular 0/1 matrix on `n=q^2` vertices,
with every two distinct rows having inner product at most one.  Let `D` be
the second-order defect graph, so

```text
L_D = (q-1)I - D = A^2 - J.
```

For `S` a vertex set, write `s=|S|`,
`b_v=|N_A(v) intersect S|`, and `delta_D(S)` for its D-edge boundary.

## Exact cut-variance identity

Center the indicator of `S`:

```text
x = 1_S - (s/q^2) 1.
```

Then `x` is perpendicular to `1`, and regularity gives

```text
A x = b - (s/q) 1.
```

Consequently

```text
|delta_D(S)|
  = x^T L_D x
  = x^T (A^2-J) x
  = ||A x||^2
  = sum_v (b_v-s/q)^2.                       (1)
```

Write `s=qa+r`, with `0 <= r < q`, and put `c_v=b_v-a`.  Since
`sum_v b_v=qs`, one has `sum_v c_v=qr`.  Among `q^2` integers with this
sum, the square sum is minimized by `qr` ones and zeros elsewhere.  Equation
(1) therefore gives

```text
|delta_D(S)| >= r(q-r).                       (2)
```

When `r=0`, equation (1) is an integer square sum with zero coordinate sum,
so every such cut is even.

## Maximal edge connectivity

Assume `D` is connected.  Suppose a nontrivial cut has size
`delta <= q-2`.  Inequality (2) forces `r=0`.  Hence

```text
y = A 1_S - a 1
```

is a nonzero integer vector satisfying

```text
sum_v y_v = 0,       ||y||^2 = delta.
```

Let `m=|supp(y)|`; then `2 <= m <= delta`.  Count incidences from
`supp(y)` into A-neighborhoods.  There are `mq` incidences.  If `k_v` is
the number of support vertices adjacent to `v`, C4-freeness gives

```text
sum_v choose(k_v,2) <= choose(m,2).
```

For `k_v >= 2`, one has `k_v <= 2 choose(k_v,2)`.  Therefore at least

```text
mq - 2 choose(m,2) = m(q-m+1)                (3)
```

vertices have exactly one A-neighbor in `supp(y)`.  At each such vertex
`Ay` is nonzero, so (3) is a lower bound for `|supp(Ay)|`.

On the other hand,

```text
Ay = A^2 x = L_D 1_S,
```

which is supported only at endpoints of the `delta` cut edges.  Thus

```text
m(q-m+1) <= 2 delta.                          (4)
```

The left side is concave in `m`.  On `2 <= m <= delta <= q-2`, its two
endpoint values satisfy

```text
2(q-1) > 2 delta,
delta(q-delta+1) >= 3 delta > 2 delta,
```

contradicting (4).  Every nonzero D-cut therefore has size at least `q-1`.
Since `D` is `(q-1)`-regular, a singleton shore realizes a cut of size
`q-1`, and hence

```text
lambda(D) = q-1.
```

## Immediate residue

- A minimum cut has shore size congruent to `1` or `-1` modulo `q`.
- A nontrivial q-divisible shore has an even cut of size at least `q`.
- `D` is bridgeless and odd-regular, hence has a perfect matching by
  Petersen's 1-factor theorem; deleting it leaves an even `(q-2)`-regular
  graph with a 2-factor decomposition.
- If `F=D\T` is disconnected, every union of F-components has an all-T
  boundary of size at least `q` (and at least `2q-4` when its even size is
  not divisible by `q`).

These consequences are new constraints on a connected defect graph, but
they do not yet exclude one.  Lean promotion should wait for a consumer, in
accord with goal #24's math-before-certificates rule.

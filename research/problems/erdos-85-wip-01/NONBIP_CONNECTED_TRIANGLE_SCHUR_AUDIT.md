# NONBIP-CONNECTED triangle-hypergraph Schur audit

Date: 2026-08-26.  Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **positive bounded calibration and a precise new interface gap**, not
a theorem and not a q=8 enumeration.

## Exact decomposition

Let `A` be a symmetric loopless C4-free adjacency matrix.  Every edge lies
in at most one triangle.  Let

- `H` be the vertex-by-triangle zero-one incidence matrix;
- `t = H 1`, the vector of vertex triangle counts;
- `K` be the spanning graph of A-edges lying in no triangle; and
- `M = A_K - diag(t)`.

Then, entrywise over the integers,

```text
A = M + H H^T.                                      (1)
```

For q-regular `A`, every triangle column has sum three and

```text
M 1 = q 1 - 3t.                                     (2)
```

This retains information absent from `A^2`: triangles and their unmatched
edges are located on the same self-indexed vertex set as the polarity.

## The Schur terminal

Assume first that `M` is invertible and put

```text
S = I + H^T M^(-1) H.
```

If `S z = 0`, then the explicit vector

```text
x = -M^(-1) H z
```

satisfies `A x = 0` by (1).  For the distinguished triangle vector `z=1`,
equation (2) gives the sharper equivalence

```text
S 1 = (q/3) H^T M^(-1) 1.                           (3)
```

Thus the exact new target is

> **CORE-TRIANGLE-CANCELLATION.** If `M` is invertible, the sum of the
> coordinates of `M^(-1)1` on every A-triangle is zero.

Because a q-regular triangle-free C4-free graph has a two-ball of size
`1 + q + q(q-1) = q^2+1`, no such graph has order `q^2`.  Hence `H` has at
least one column in the square-order problem, so `H1=t` is nonzero and the
kernel vector supplied by (3) is nonzero.

The singular-core sibling that makes the split complete is also precise:

```text
ker(M) intersect ker(H^T) is nontrivial.             (4)
```

Any vector in (4) is already killed by (1).  A uniform theorem proving (4)
when `M` is singular and CORE-TRIANGLE-CANCELLATION when it is invertible
would close NONBIP-CONNECTED directly.  Neither statement is currently
proved.

### Integer cofactor form

The invertible-core target has a denominator-free form that is better suited
to combinatorial cancellation.  Put

```text
c = adj(M) 1 in Z^V.
```

Since `M^(-1)=adj(M)/det(M)`, CORE-TRIANGLE-CANCELLATION is exactly

```text
H^T c = 0.                                            (5)
```

In words: for every A-triangle, the three corresponding row sums of
`adj(M)` add to zero.  If (5) holds, the explicit integral vector

```text
X = -adj(M)t
```

is killed by `A`.  Equation (2) also gives the useful identity

```text
3X = det(M) 1 - q c.                                  (6)
```

This exposes a concrete bridge to the signed-matching mechanism: entries of
`adj(M)` are signed cofactors, hence signed sums of near-perfect cycle-cover
terms in the looped triangle-free core.  A sign-reversing cancellation of
the three cofactor families owned by each triangle would prove (5) directly.
No such involution is currently known, and the coarse parity of triangle/K
edges has already been refuted as its selector; actual owner placement must
enter.

## Faithful q=4 calibration

`nonbip_connected_triangle_schur_q4_probe.py` enumerates actual symmetric
loopless 4-regular C4-free matrices on 16 vertices with a fixed root
neighborhood.  For each model it constructs every triangle, `H`, `K`, `M`,
and `S` over the rationals and stops on either a nonsingular `A` or failure
of `S1=0`.

All 256 bounded models have exactly the same profile:

```text
(#triangles, rank A, rank M, rank S, S1=0)
  = (8, 15, 16, 7, true).
```

For the previously banked fixed-free control specifically,
`det(M)=-768`, the entries of `S` have denominators only 3 and 6, and
`ker(S)` is exactly the span of the eight-coordinate all-ones vector.
This is substantially sharper than merely re-observing that `A` is
singular: it identifies the exact small Schur kernel and its canonical
triangle label.

Scope discipline: these q4 deficiency graphs are disconnected, and 256
models are evidence only.  The probe does not establish the uniform
cancellation, connectedness dependence, or the singular-core branch.

## Verdict and next step

The triangle-hypergraph decomposition **survives** and exposes a named
q-generic terminal with an explicit kernel vector.  This also complements
the independently positive signed-Levi matching exchange: both mechanisms
seek determinant cancellation, one through triangle ownership and one
through alternating perfect-matchings.

The next legitimate move is not a larger finite sample.  It is to derive
CORE-TRIANGLE-CANCELLATION from the connected deficiency relation, or to
refute it on a faithful symbolic/constructed control.  Formalizing (1)--(3)
should wait until that connectedness bridge is found; the algebra itself is
short and no longer the gap.

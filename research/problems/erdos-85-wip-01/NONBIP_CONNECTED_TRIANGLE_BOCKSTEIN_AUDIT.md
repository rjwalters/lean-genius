# NONBIP-CONNECTED triangle-incidence Bockstein audit

Date: 2026-08-26.  Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **bounded mechanism cut**.  The genuine coefficient Bockstein of a
graph is zero.  The tempting unsigned lift that returns triangle incidence is
not homology-invariant, and the external-incidence lift is an identity rather
than an additional constraint.

## Setup

Let `A` be a loopless C4-free graph.  Write

- `H` for the vertex-by-triangle zero-one incidence matrix;
- `R` for the unsigned vertex-by-edge zero-one incidence matrix of `A`; and
- `P` for the edge-by-triangle zero-one incidence matrix, where a column is
  the three edges bounding its triangle.

Every vertex of a triangle is incident with exactly two of its boundary
edges.  Therefore, over the integers,

```text
R P = 2 H.                                             (1)
```

Reducing (1) modulo two gives `Rbar Pbar = 0`; modulo two, unsigned and signed
vertex-edge incidence agree.  It is tempting to lift the mod-2 triangle cycle
using the displayed zero-one matrices, divide its boundary by two, and call
the result

```text
unsigned_defect([Pbar z]) = [Hbar z] in coker(Rbar).   (2)
```

But (2) is **not** the coefficient Bockstein.  Over the integers the graph
boundary is an oriented signed incidence matrix `partial`, not `R`.  Every
mod-2 graph cycle has an integral oriented cycle lift (equivalently,
`H_1(graph; Z)` is free), so the genuine connecting map

```text
beta : H_1(graph; F_2) -> H_0(graph; F_2)
```

is zero.  Concretely, orienting the three boundary edges cyclically makes
`partial P_signed=0` exactly.  With a fixed global edge orientation and a
zero-one lift, dividing `partial P` by two produces an even-support vertex
vector, hence a boundary modulo two.  The all-positive unsigned lift instead
produces `H`; the discrepancy proves that (2) depends on the chosen integer
lift and does not descend to homology.

## What the unsigned defect would remember

Even if one ignores the failure of invariance, the cokernel of the mod-2
unsigned incidence matrix has one coordinate for each connected component of
`A`.  A triangle lies in a single component and
its `H`-column has three ones.  Consequently its class in that component is
the class of one vertex.  For an arbitrary selected family `z`, (2) records
exactly

```text
number of selected triangles in each A-component (mod 2).              (3)
```

In particular, when `A` is connected this putative image is just `|z| mod 2`.
Thus even the noncanonical construction contains no rooted information and
cannot imply either sharp terminal input

```text
t_x = t_y (mod 4) for every D-edge xy,
(A t)_x = 2 (mod 4) for every vertex x.
```

There are therefore two independent cuts: the genuine Bockstein vanishes,
while the unsigned substitute is not well-defined and would in any case lose
vertex location upon quotienting by graph boundaries.

## The tempting external-incidence lift

Let `C` be the vertex-by-triangle matrix in which `C[x,tau]=1` when `x` is
outside `tau` and adjacent to one of its vertices.  C4-freeness ensures that
an outside vertex cannot meet two vertices of a triangle, and hence

```text
A H = C + 2 H.                                        (4)
```

Modulo two, (4) says `Abar Hbar = Cbar`; it does **not** say that `Hbar` is a
cycle for a fixed differential.  Treating the quotient `(AH-C)/2=H` as a
connecting map therefore inserts `C` precisely to make the relation hold and
returns `H` by construction.  It supplies no independent condition on `H`.

The same circularity remains after combining (4) with the square-order
identity.  Put `U` for the all-ones vertex-by-triangle matrix.  Since every
triangle has three vertices and

```text
A^2 = (q-1) I + J - D,
```

one obtains, for `4 | q`,

```text
A C + 2 C ≡ A^2 H
            ≡ (q-1)H + 3U - D H
            ≡ -H + 3U - D H                         (mod 4).             (5)
```

Multiplying (5) by the all-ones triangle vector gives no new rooted
congruence.  Indeed `C 1 = A t - 2t`, so its left side reduces identically to
`A^2 t` modulo four, while the right side is just the square identity applied
to `t`.  Thus (5) repackages the uncontrolled vectors `t`, `Dt`, and `At`.

## Verdict

The genuine triangle-boundary coefficient Bockstein is zero.  The unsigned
construction `RP=2H` is a lift-dependent secondary defect, not a Bockstein;
even if retained, its quotient is only the componentwise triangle-count
parity (3).  The alternative mod-4 lift from external incidence is
tautological and its square-order consequence (5) reduces to the
already-known matrix identity.  Neither route supplies triangle-degree
propagation modulo four or the rooted triangle-mass residue.

Any viable cohomological replacement must retain vertex location after
passing to homology (for example through genuinely twisted/local
coefficients), and must prove a new compatibility with the defect graph `D`;
ordinary constant-coefficient Bockstein theory does not provide that bridge.

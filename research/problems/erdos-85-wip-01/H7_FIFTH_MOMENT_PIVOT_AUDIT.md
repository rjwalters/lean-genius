# H7 fifth-moment pivot audit

Date: 2026-08-26

## Question

The proof of `R(C4,K1,39)=46` at upstream commit
`86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33` ultimately avoids SAT.  For a
7-regular graph it writes

```text
A^2 = 6 I + J - D
```

with a cubic deficiency graph `D`.  Since the scalar diagonal makes `A` and
`D` commute, the nonprincipal eigenvalues of `A` lie in two short symmetric
intervals.  An exact fifth moment then lets rational dual polynomials trap the
integer number of positive eigenvalues strictly between 21 and 22.

This audit asks whether that decisive mechanism transfers to the canonical H7
stratum at order 49.

## Exact H7 deficiency data

Let `A` be the adjacency matrix and define

```text
K = diag(deg(v) - 1),
D = K + J - A^2.
```

C4-freeness makes `D` a simple off-diagonal relation: distinct vertices are
`D`-adjacent exactly when they have no common neighbor.  In H7 there are seven
degree-8 highs and forty-two degree-7 lows.  The highs are independent, and
the low support multiplicities are 7 empty, 14 singleton, and 21 pair.

For every vertex,

```text
deg_D(v) = deg(v) - 1 + 49 - sum_{u in N(v)} deg(u).
```

Therefore the exact `D` degrees are:

| vertex role | population | `deg_D` |
|---|---:|---:|
| high | 7 | 0 |
| empty-support low | 7 | 6 |
| singleton-support low | 14 | 5 |
| pair-support low | 21 | 4 |

In particular, all deficiency edges lie among lows and

```text
sum_v deg_D(v) = 7*6 + 14*5 + 21*4 = 196.
```

## General fifth-trace identity

Expanding `tr(A (K+J-D)^2)` for any such graph gives

```text
tr(A^5)
  = 2 sum_v deg(v)(deg(v)-1) + 2 n |E|
    - 2 tr(A K D) - 2 deg^T D 1 + tr(A D^2).
```

For H7, `|E|=175`, every endpoint of a `D` edge is a degree-7 low,
`tr(AKD)=6 tr(AD)`, and `deg^T D 1=7*196`.  Hence the exact specialization is

```text
tr(A^5) = 18718 - 12 tr(A D) + tr(A D^2).        (H7-M5)
```

Here `tr(AD)` is twice the number of low-low graph edges with no common
neighbor.  Writing `T_low` for the number of all-low triangles, the 119
low-low edges consist of 28 edges in high-containing triangles, `3*T_low`
edges in all-low triangles, and the remaining triangle-free edges.  Thus

```text
tr(AD) = 182 - 6*T_low.
```

The last term is

```text
tr(A D^2) = 2 * sum_{uv in E(G)} |N_D(u) intersect N_D(v)|,
```

and is not determined by the H7 support profile or empty-mask cube.

## Why the regular certificate does not transfer

The obstacle occurs before polynomial optimization.  In the regular proof,
`K=6I`, so `D=6I+J-A^2` commutes with `A`; on the nonprincipal space an
eigenvalue `mu` of `D` forces adjacency eigenvalues satisfying
`theta^2=6-mu`.  This supplies the two compact symmetric spectral intervals
on which the fifth-degree dual polynomials work.

For H7, `K` has value 7 on highs and 6 on lows.  It is not scalar, and the
high-low graph edges make `AK != KA`.  Neither `D` nor the degree vector is a
polynomial in `A`, so there is no common eigenbasis and no equation
`theta^2 = constant - mu`.  Moreover, (H7-M5) retains both the variable
all-low triangle count and the variable overlap statistic `tr(AD^2)`.

Consequently the published rational dual polynomials cannot even be applied
to the H7 spectrum: their validity relies on the missing square-root support,
not just on knowing a fifth-moment interval.  Crude adjacency bounds such as
`|theta| <= 8` are far too wide to reproduce the integer-eigenvalue-count
trap.

## Verdict

The degree-five regular spectral certificate is **NO-GO for H7 as stated**.
The exact replacement identity (H7-M5) is useful bookkeeping, but pursuing
higher scalar moments without a new nonregular spectral decomposition would
be hill climbing.

A genuinely new spectral route would first need one of:

1. an equitable/block decomposition that simultaneously reduces `A`, the
   high/low degree projection, and `D`; or
2. a matrix-valued polynomial certificate that works with the two-valued
   diagonal `K` and controls `tr(AD^2)`.

Absent such an input, do not port the regular LP polynomials or formalize a
standalone H7 fifth-moment bound.


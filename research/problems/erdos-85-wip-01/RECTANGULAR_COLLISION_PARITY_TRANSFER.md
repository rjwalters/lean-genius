# Rectangular collision parity transfer

Status: parameter-free matrix identity extracted from the A-REG collision
table for reuse in the B.3 rectangular-incidence model, 2026-08-22.

Let `Q` be a zero-one matrix whose rows are indexed by `X` and columns by
`Y`.  Let `K` be the adjacency matrix of a simple graph on `Y`, and put

```text
R = Q K Q^T.
```

If `S_x subset Y` is the support of row `x`, then

```text
R(x,z) = number of ordered K-edges from S_x to S_z,
R(x,x) = 2 * e_K(S_x).                                  (1)
```

The matrix `R` is symmetric.  Consequently, for the integer collision mass

```text
C(R) = sum_(x,z) choose(R(x,z),2),                       (2)
```

all off-diagonal summands occur in transposed pairs.  On the diagonal,

```text
choose(R(x,x),2)
  = choose(2*e_K(S_x),2)
  = e_K(S_x) * (2*e_K(S_x)-1)
  = e_K(S_x)                         (mod 2).
```

Therefore

```text
C(R) = sum_x e_K(S_x)                                  (mod 2). (3)
```

If an application additionally proves `R(x,z) in {0,1,2}`, then (2) is
literally the number of ordered cells with `R(x,z)=2`, and (3) localizes its
parity to the number of `K`-edges internal to the row supports.

This is the exact rectangular analogue of the size-two identity for
`B_c=A_cD_c`.  It requires no regularity, square order, or graph census.

For a nonsymmetric product such as `A Q K Q^T`, (3) must first be applied to
the symmetric matrix `R=QKQ^T`.  Multiplication by `A` preserves the same
argument only if `A` commutes with `R` (so `AR` is symmetric), or if a
separate support-mask argument reduces back to entries of `R`.  Zero support
of `A hadamard R` alone does not make `AR` symmetric and should not be used as
a substitute for commutation.

In the B.3 model this gives a concrete audit checklist:

1. identify the row supports `S_x` of the rectangular incidence `Q`;
2. determine or bound `e_K(S_x)` from the puncture/row geometry;
3. prove an entry bound for `QKQ^T` if collision cells, rather than the full
   binomial mass, are desired;
4. use the residual adjacency `A` only after verifying commutation or an
   exact support reduction.

The identity does not itself contradict the model; it transfers a global
collision parity to a diagonal row-support statistic where connectivity or
puncture geometry may act.

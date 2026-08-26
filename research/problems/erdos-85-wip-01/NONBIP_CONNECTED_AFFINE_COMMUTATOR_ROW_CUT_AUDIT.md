# NONBIP-CONNECTED affine-moment commutator row cut

## Question

Can the generic row identity

```text
sum_y (A H - H A)[x,y]
  = sum_{z in N_A(x)} deg_H(z) - q deg_H(x)
```

from `Erdos85AntipodalCommutatorRows.lean` supply the first aggregate
identity in the triangle affine-potential route?

Write `A` for the adjacency matrix of a `q`-regular C4-free graph on
`q^2` vertices, `D` for its `(q-1)`-regular defect graph, `K=A intersect D`
for its triangle-free-edge graph, and `t_x` for the number of ambient
triangles through `x`.  Then

```text
deg_K(x) = q - 2 t_x.
```

The desired aggregate identity is

```text
(2q+1) S1 - 3 S2 = q^2(q^2+2)/3,
S1 = sum_x t_x,  S2 = sum_x t_x^2.
```

## Exact reduction

Taking `H=D` gives no information: regularity of both graphs makes every
row sum identically zero,

```text
sum_{z in N_A(x)} deg_D(z) - q deg_D(x)
  = q(q-1) - q(q-1) = 0.
```

Taking `H=K` and substituting `deg_K=q-2t` gives

```text
sum_y (A K - K A)[x,y]
  = 2 (q t_x - sum_{z in N_A(x)} t_z).
```

Summing over `x` also gives zero identically, because ambient regularity
implies

```text
sum_x sum_{z in N_A(x)} t_z = q sum_x t_x.
```

Thus neither the `A,D` nor the `A,K` unweighted commutator row sum contains
the quadratic moment `S2` or the constant term required by the affine
terminal.

For comparison, summing the conjectural pointwise identity

```text
K t = t^2 - (q+1)t + (q^2+2)/3
```

does produce the target, but only because symmetry and `K 1=q 1-2t` give

```text
1^T K t = (K1)^T t = q S1 - 2 S2.
```

Equating this tautological evaluation of the *left* side with the
conjectural polynomial *right* side is precisely the new content.  The
generic commutator row theorem does not provide that equality.

In the degree coordinates `k_x=deg_K(x)=q-2t_x`, the two aggregate affine
identities are exactly

```text
3 sum_x k_x^2 - (2q-2) sum_x k_x
  = -q^2(q-2)(q-4)/3,                         (aggregate T1)

3 sum_x k_x^2 - (4q-2) sum_x k_x + q^3(q-2)
  = 0.                                        (aggregate T2)
```

This also locates the nearest existing trace result:
`trace_adj_sq_triangleFree_sq_sub_fourth_eq_degreeMoments` rewrites a trace
difference as

```text
q sum_x k_x - sum_x k_x^2.
```

It names a linear combination of the two free degree moments, but does not
fix either moment and hence does not imply either displayed equation.

## Incidence-bottleneck comparison

The matrix `E=AD-(J-A)` does see these moments on its diagonal, since the
banked theorem
`incidenceBottleneck_diag_eq_triangleFreeDegree_sub_one` gives

```text
E[x,x] = k_x-1,
sum_x E[x,x]^2 = sum_x k_x^2 - 2 sum_x k_x + q^2.
```

However, the connected-incidence ledger bounds the *full* Frobenius energy
`sum_{x,y} E[x,y]^2`.  Its off-diagonal energy is not determined by the
diagonal, and the current lower bounds therefore give only inequalities in
the degree moments, not either required equality.  Passing from the full
energy to the affine moment would require a new sharp off-diagonal identity
or equality case; the diagonal formula alone is not a bridge.

## Verdict

**CUT for the unweighted row-sum route.**  The banked commutator theorem is
compatible with the affine setup but collapses to regularity identities.
A viable commutator successor would need genuinely new weighted information
(for example a controlled pairing with `diag(t)`), and must independently
produce an `S2` term; merely summing or specializing the existing row theorem
cannot prove the affine aggregate identity.

This does not refute either local affine identity.  It only closes the
suggested shortcut through
`sum_adjMatrix_commutator_row_eq_neighborDegreeSum_sub`.

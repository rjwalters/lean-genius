# NONBIP-CONNECTED discriminant-form audit

Status: bounded negative audit under `A-REG-NONBIP`, 26 August 2026.

## Candidate consequence

If a connected A-REG target existed, then

```text
B = L_D + J = A^2
```

would be positive definite.  For any symmetric integral nonsingular `A`,
the image

```text
A Z^n / A^2 Z^n <= Z^n / A^2 Z^n
```

is isotropic for the discriminant pairing

```text
<x,y> = x^T B^{-1} y mod Z.
```

Indeed `<Au,Av> = u^T v = 0 mod Z`.  Its order is `|det A|`, the square
root of `|det B|`, so it is a Lagrangian.  Therefore the discriminant form
of `L_D+J` must be metabolic.  This refines the already-banked necessary
condition that `det(B)` (equivalently the tree count) is a square.

The standard critical-group literature develops Smith invariants of graph
Laplacians, but the outside search found no theorem turning this metabolic
condition into the required 0/1 self-adjoint square root.  The q=4 bounded
control shows why.

## Exact connected control

Use the connected nonbipartite cubic circulant `D_4` from
`q_generic_connected_defect_spectral_countermodel.py`.  The companion
calculation already proves

```text
charpoly(L_D + J) = (x - 16)(x - 4) P(x)^2
```

and that the residual field norms prevent a rational trace-zero square root.
In particular it has no candidate A-REG incidence square root.

Nevertheless exact Smith decomposition gives

```text
coker(L_D + J) = C_1552 x C_24832,
1552  = 2^4 * 97,
24832 = 2^8 * 97,
det(L_D+J) = 38,539,264 = 6208^2.
```

`nonbip_connected_discriminant_metabolic_control.py` computes the linking
pairing in these Smith coordinates and checks an explicit Lagrangian:

- on `C_16 x C_256`, `(0,16)` and `(4,0)` generate an isotropic subgroup
  `C_16 x C_4` of order `64`;
- on `C_97 x C_97`, `(1,46)` generates an isotropic subgroup of order `97`;
- the primary pieces pair orthogonally, so their direct sum has order
  `64*97 = 6208 = sqrt(det(B))`.

Thus this connected nonbipartite `D` satisfies the full metabolic
discriminant-form consequence while failing even to have the needed rational
square root.  The full Smith/linking invariant does not recover incidence
placement and cannot close `NONBIP-CONNECTED` by itself.

## Scope cut

The convergent round-71 proposals based on critical groups, primitive
2-adic embeddings, and the discriminant form are cut at the graph-only
level.  A stronger invariant would have to retain the actual 0/1 square
root, such as Plucker relations among its Pfaffian cofactors or the
self-indexed owner map.  Merely strengthening `tau(D) is a square` to
`disc(L_D+J) is metabolic` is still insufficient.

Reference for Smith groups and graph Laplacians: D. Lorenzini, *Smith normal
form and Laplacians*, Journal of Combinatorial Theory B 98 (2008),
1271--1300, <https://doi.org/10.1016/j.jctb.2008.02.002>.

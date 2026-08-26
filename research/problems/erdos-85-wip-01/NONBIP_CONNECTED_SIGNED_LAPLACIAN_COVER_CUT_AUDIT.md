# NONBIP-CONNECTED signed-Laplacian cover cut

Status: exact structural falsification of divergence-round 74 proposal P3,
26 August 2026.

## Proposed mechanism

The proposal was to realize

```text
-M = diag(t) - A_K
```

as a grounded Laplacian, possibly after the standard two-sheet lift of a
signed graph.  Then all-minors matrix-tree theory would turn
`H^T adj(M)1` into a forest imbalance on which sheet exchange might act.

## Necessary local inequality

In a nonnegative-weight grounded Laplacian, an interior principal block has
off-diagonal entry `-w_uv` and diagonal entry

```text
sum_{interior u} w_vu + sum_{boundary b} w_vb.
```

Consequently its diagonal is at least the sum of the absolute values of its
interior off-diagonal entries.  The same condition holds for a signed-graph
Laplacian and its ordinary two-sheet cover: signing changes which sheet an
edge reaches, not its nonnegative contribution to the diagonal degree.

For `-M`, every `K` edge has unit absolute weight, so this necessary
condition is

```text
t_v >= deg_K(v).
```

But in a `q`-regular C4-free graph each triangle through `v` consumes two
incident non-`K` edges, hence

```text
deg_K(v) = q - 2 t_v.
```

Thus any such Laplacian realization requires `3 t_v >= q` at every vertex.

## Exact control

In the faithful q=4 control used by the triangle-Schur and cofactor probes,
the triangle-degree vector has vertices with `t_v=1`.  At each such vertex
`deg_K(v)=2`, so the proposed block would have diagonal `1` and absolute
off-diagonal row sum `2`.  The necessary grounded-Laplacian inequality fails
strictly.

This is independent of how the K edges are signed or assigned between two
sheets.  Adding grounded boundary vertices can only increase the required
diagonal; it cannot repair a deficit of one.

## Verdict and scope

The genuine nonnegative-weight Laplacian/two-sheet-cover route is cut even
on the smallest exact control.  Therefore the ordinary positive
matrix-tree theorem cannot supply the desired cofactor cancellation through
this representation.

This does **not** cut arbitrary signed determinant or forest expansions of
the indefinite matrix `M`: those permit cancellation without realizing
`-M` as a positive Laplacian.  It also does not weaken the target
`H^T adj(M)1=0`.  It only rules out the proposed positive-cover mechanism;
the surviving cofactor route must remain genuinely indefinite or use a
pre-expansion algebraic identity.

# NONBIP-CONNECTED defect-gradient energy audit

Date: 27 August 2026. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: exact reduction and trace-route cut; no propagation theorem claimed.

## Target and exact energy

Let `A` be the ambient adjacency matrix, `D` the second-order defect
adjacency matrix, and

```text
k_x = deg_{A intersection D}(x) = (AD)_{xx} = q - 2 t_x,
K   = diag(k).
```

At square order `D` is `(q-1)`-regular.  The desired defect-edge
propagation of triangle degree is exactly

```text
DK = KD.
```

Its squared Frobenius norm is twice the Dirichlet energy

```text
1/2 ||DK-KD||_F^2
  = sum_{{x,y} in E(D)} (k_x-k_y)^2
  = k^T L_D k
  = tr(K^2 D^2) - tr(K D K D)                         (E)
  = (q-1) sum_x k_x^2 - 2 sum_{{x,y} in E(D)} k_x k_y.
```

Because `k=q1-2t`, the same quantity is

```text
4 sum_{{x,y} in E(D)} (t_x-t_y)^2.
```

Thus (E) vanishes if and only if `t`, equivalently `k`, is constant on
every defect component.  Connectedness would then make it globally
constant.

## Why the ordinary trace/moment ledger cannot evaluate (E)

The square-order identity

```text
A^2 = (q-1)I + J - D
```

makes every *ordinary* word in `A,D,J` reducible to spectral moments of
`D`.  It does not recover `K`: the operation

```text
K = diag(diag(AD)) = I HadamardProduct (AD)
```

is a Schur/diagonal extraction, outside that ordinary adjacency algebra.
Both terms in (E) retain new rooted information:

* `tr(K^2 D^2)=(q-1) sum k_x^2` needs the second moment of the diagonal of
  `AD`, not `tr((AD)^2)`;
* `tr(KDKD)=2 sum_{D-edge} k_x k_y` needs the defect-edge correlation of
  that diagonal.

Even knowing `sum k_x = tr(AD)`, all ordinary traces through any fixed
degree, and regularity of `D` leaves these two Schur moments undetermined.
The commutation `AD=DA` does not imply that `diag(AD)` commutes with `D`.

Consequently a proof that merely expands higher ordinary traces, or rewrites
`(AD)^m` using `A^2=(q-1)I+J-D`, cannot force (E) to vanish.  It must add a
genuinely Hadamard/coherent identity controlling at least one of the two
displayed rooted moments.  This is precisely the missing input identified
by divergence #77's coherent-closure probe.

## Relation to the stronger weighted-neighbor terminal

Vanishing of (E) only propagates `k`; it does **not** prove the stronger
identity

```text
A k = ((q^2-4)/3) 1,
```

which already gives a nonzero rational kernel vector and closes the
connected branch.  Uniform `k=r1` instead gives `Ak=qr1`, and no current
arithmetic fixes `r=(q^2-4)/(3q)`.  Therefore even a successful energy-zero
proof needs a second structural or arithmetic terminal.

## Verdict

The defect-gradient energy is the exact nonnegative propagation invariant,
but it is not an ordinary trace consequence.  The pure spectral/moment
version of this route is cut.  A future reopening must name a Schur-product
or coherent-configuration identity that evaluates one of
`sum k_x^2` or `sum_{D-edge} k_x k_y`, and must also state the post-propagation
terminal.  Merely banking higher polynomial moments does not advance this
node.

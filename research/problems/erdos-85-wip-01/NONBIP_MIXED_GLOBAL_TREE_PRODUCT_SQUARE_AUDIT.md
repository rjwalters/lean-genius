# Global tree-product square and signed-owner audit

Node: `A-REG-NONBIP / NONBIP-MIXED`; divergence round 95.

## 1. A genuinely ambient square-class invariant

Let the connected components of the `(q-1)`-regular defect graph `D` be
`C_1,...,C_r`, with

`|C_i| = q m_i`,  and  `sum_i m_i = q`.

Write `tau_i` for the number of spanning trees of `D[C_i]`.  From

`A^2 = (q-1)I + J - D`

one reads the complete nonzero spectrum of `A^2`:

- the all-ones line contributes `q^2`;
- the other `r-1` component-constant lines contribute zero;
- on the sum-zero subspace of `C_i`, the eigenvalues are the nonzero
  Laplacian eigenvalues of `D[C_i]`.

The matrix-tree theorem says that the product of those nonzero Laplacian
eigenvalues is `|C_i| tau_i = q m_i tau_i`.  Therefore

`pdet(A^2) = q^2 product_i(q m_i tau_i)`.

On the other hand every nonzero eigenvalue of `A^2` is the square of a
nonzero eigenvalue of the integral symmetric matrix `A`.  Its
pseudodeterminant is, up to sign, the first nonzero integral coefficient of
the characteristic polynomial.  Consequently

> `q^(r+2) product_i(m_i tau_i)` is a perfect square integer.       (T)

Unlike the single-component packing Gram, (T) uses the one symmetric ambient
matrix and couples all defect components.  The q-generic prescribed-leave
countermodel from divergence 94 does not supply such a simultaneous square
root.

For `q=2^k`, (T) splits into the explicit necessary conditions

```text
k(r+2) + sum_i (v2(m_i) + v2(tau_i)) = 0 mod 2,
product_i oddPart(m_i tau_i) is an odd square.
```

The q=4 `[2,2]` control passes sharply: `r=2`, `m_1=m_2=2`, and
`tau_1=tau_2=392`, so the product is `(16*784)^2`.

### Scope

This is not yet a terminal.  Connected nonbipartite odd-regular graphs do not
have a fixed spanning-tree parity or square class; even small examples realize
both behaviours.  A consumer must extract a componentwise residue from the
self-indexed incidence blocks and then use (T) to show their global product
cannot be square.  Without that local residue, (T) is a precise new interface,
not a proof of `A-REG`.

## 2. Balanced signed owners: exact inertia, no obstruction

Put

`S_i = O_i + m_i I = A P_i A`.

For signs `epsilon_i in {+1,-1}`, let

`E = sum_i epsilon_i P_i`,  `W = sum_i epsilon_i S_i = A E A`.

If the positive and negative normalized weights are both `q/2`, then `W` has
zero diagonal and is a `+1/-1` signing of the non-D edges, with zero entries
on D-edges.  This looked like a possible Seidel-inertia obstruction.  In fact
its inertia is forced and always consistent.

Let `r_+` and `r_-` be the numbers of positive and negative components.
The real kernel of `A` is the `(r-1)`-dimensional hyperplane of
component-constant vectors whose weighted component sum is zero.  Its
orthogonal complement is

`im(A) = (direct sum_i 1_{C_i}^perp) direct sum span(1)`.

On the first summand, `E` has positive dimension `q^2/2-r_+` and negative
dimension `q^2/2-r_-`.  The all-ones line is orthogonal to every first
summand and is radical for the restricted form because
`sum_i epsilon_i |C_i|=0`.  Congruence through `A` and the kernel of `A`
therefore give

```text
inertia(W) = (q^2/2-r_+, q^2/2-r_-, r).
```

The exact q=4 signing has inertia `(7,7,2)` and characteristic polynomial

```text
t^2 (t-4)(t+4)(t-2)^2(t+2)^2
    (t^2-8t+14)^2(t^2+8t+14)^2,
```

matching the formula.  Thus balanced signed-owner inertia is another form of
the already-banked exact adjacency-kernel decomposition.  It supplies no
contradiction at `k>=3`; do not open a Lean wrapper without an additional
support-sensitive signed invariant.

## Disposition

- Retain the global tree-product square (T) as a new ambient arithmetic
  consumer interface.
- Stop balanced signed-owner inertia/discriminant: the complete inertia is
  algebraically feasible for every mixed partition admitting a balanced
  subpartition.

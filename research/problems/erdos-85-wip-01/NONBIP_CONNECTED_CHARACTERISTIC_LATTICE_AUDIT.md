# NONBIP-CONNECTED characteristic-lattice audit

## Proposal

Use the neighborhood incidence matrix A as a self-dual partial-design matrix.
On the augmentation space, its Gram form is

```text
A^2 restricted to 1-perp = L_D = (q-1)I-D,
```

the Laplacian of the `(q-1)`-regular defect graph.  The divergence-79 proposal
asked whether a characteristic-vector norm congruence (of van der Blij / even
unimodular-lattice type) could force rooted triangle counts modulo four.

## Parity of the augmentation lattice

Let

```text
Lambda = {v in Z^n : sum_i v_i=0}.
```

For q even, `q-1` is odd.  Modulo two, the off-diagonal terms of
`v^T L_D v` occur twice, so

```text
v^T L_D v = (q-1) sum_i v_i^2 = sum_i v_i = 0 (mod 2)
```

on Lambda.  Thus the augmentation lattice is already even and its trivial
characteristic vector is zero.  This canonical characteristic vector contains
no rooted information.

For a defect edge xy, the proposed nontrivial vector `w=e_x-e_y` reduces
modulo two to `e_x+e_y`.  It is characteristic on the even augmentation
lattice only if `L_D w` is constant modulo two.  Its x and y coordinates are
zero, and for every other z its coordinate is

```text
D(z,x)+D(z,y) (mod 2).
```

Consequently w is characteristic exactly when x and y are adjacent defect
twins:

```text
N_D(x) without {y} = N_D(y) without {x}.
```

Connectedness and regularity of D do not imply this; it is a strong extra
classification hypothesis.  The characteristic property therefore does not
propagate along arbitrary defect edges.

## Failure of the unimodular hypothesis

For connected D, the nonzero Laplacian eigenvalue product is `n*tau(D)`.
In the standard basis `e_i-e_n` of Lambda, the discriminant of the restricted
Gram form is

```text
det(B^T L_D B) = n^2 * tau(D).
```

It is highly nonunimodular and has precisely the uncontrolled 2-primary
critical-group data already isolated by the cofactor/discriminant audits.
Van der Blij's mod-eight characteristic norm conclusion for unimodular
lattices therefore does not apply.  Passing to the discriminant form reopens
the previously cut critical-group route rather than supplying a new theorem.

Finally, the form `L_D` depends only on D.  Ambient triangle degree
`t_x=(A^3)_{xx}/2` depends on the particular symmetric integral square root A
and is not a norm of `e_x` or `e_x-e_y` in this D-lattice.  Bringing A back
into the characteristic vector is an additional, unproved embedding—not a
consequence of the partial-design Gram identity.

## Verdict

The characteristic-lattice proposal is **cut** in its natural form.  The
augmentation lattice has the root-blind characteristic vector zero,
`e_x-e_y` is characteristic only for adjacent defect twins, and the lattice is
not unimodular.  Any repaired proposal must construct a genuinely A-dependent
characteristic covector and control the 2-primary discriminant independently;
those are exactly the missing inputs, not consequences of square order.

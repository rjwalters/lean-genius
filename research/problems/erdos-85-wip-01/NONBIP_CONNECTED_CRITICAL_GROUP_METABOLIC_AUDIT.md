# NONBIP-CONNECTED critical-group metabolic audit

Status: exact structural consequence, nonterminal.  Derived during divergence
round 25 on 24 August 2026.

## Setup

Let `A` be a nonsingular symmetric integral matrix of order `n=q^2` with

```text
A 1 = q 1,
L = A^2 - J,
```

where `L` is the Laplacian of a connected graph.  Put

```text
Lambda  = {x in Z^n : sum x = 0},
Lambda* = {x in Q^n : sum x = 0 and x_i-x_j is integral for all i,j}.
```

Projection along the constant line identifies `Z^n / Z 1` with `Lambda*`.
Consequently the graph critical group and its linking pairing are

```text
K(L) = Lambda / L Lambda* = Lambda / A^2 Lambda*,
<x,y> = x^T L^(-1) y  (mod Z).
```

It is important not to replace this by `Lambda/L Lambda`: the latter has an
extra factor of `n` and is the source of a false direct-sum cancellation.

## Action on the root-lattice discriminant

The root lattice has cyclic discriminant group

```text
Delta = Lambda* / Lambda = Z/nZ.
```

For `u_i=e_i-(1/n)1`, symmetry and the row sum of `A` give

```text
A u_i = A e_i - (1/q)1,
A u_i - q u_i = A e_i - q e_i in Lambda.
```

Thus `A` acts on `Delta=Z/q^2 Z` as multiplication by `q`.  In particular
its image and kernel on `Delta` both have order `q`, and `A^2` acts as zero.
This explains integrally why `A^2 Lambda*` lies in `Lambda` although
`A Lambda*` generally does not.

## The canonical metabolizer

Define

```text
U = {u in Lambda* : A u in Lambda},
H = A U / A^2 Lambda*  <=  K(L).
```

Since `U` is the inverse image of `ker(q : Delta -> Delta)`, it has index
`q` in `Lambda*`.  If

```text
delta = |det(A restricted to 1-perp)| = |det A|/q,
```

then `[Lambda*:A Lambda*]=delta`, while `A Lambda*` is contained in `U`.
Therefore

```text
|H| = [U:A Lambda*] = delta/q = |det A|/q^2.
```

The matrix-tree identity gives

```text
tau(L) = det(A)^2/q^4,
```

so `|H|=sqrt(tau(L))=sqrt(|K(L)|)`.

It remains to check isotropy.  Write `x=A u` and `y=A v` with `u,v in U`.
On the zero-sum space `L=A^2`, hence

```text
<x,y> = (A u)^T A^(-2) (A v) = u^T v  (mod Z).
```

Membership in `U` says that the classes of `u` and `v` lie in
`ker(q : Z/q^2 Z -> Z/q^2 Z)`, so both are multiples of `q`.  The
discriminant bilinear form of `A_(n-1)` is `-ab/n` on classes `a,b`.
It is integral on two multiples of `q` because `n=q^2`.  Thus `u^T v` is
integral, `H` is isotropic, and its square-root order makes it a Lagrangian.

Hence the full critical-group linking form forced by an admissible connected
square root is metabolic, including its 2-primary part.

## Disposition

This is strictly stronger than the already-banked statement that the
spanning-tree count is a square, but it is not a contradiction.  The connected
cubic `q=4` defect-only control has critical group

```text
Z/3 Z + Z/3 Z + Z/15129 Z,       15129 = 3^2 41^2,
```

and its exact linking form is metabolic.  More generally, graph-Jacobian
realization results make metabolic pairings common rather than forbidden.
The result can become terminal only with a new theorem excluding metabolic
critical forms for the exact simple `(q-1)`-regular, self-polar/J2-free
deficiency geometry.  Connectedness and regularity alone cannot supply that
theorem, so no further determinant or Smith-normal-form wrapper is justified.

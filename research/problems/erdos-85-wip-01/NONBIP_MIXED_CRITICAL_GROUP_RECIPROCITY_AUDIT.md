# Critical-group reciprocity and generalized-zero-layer audit

Node: `A-REG-NONBIP / NONBIP-MIXED`; divergence round 96.

## 1. The exact reciprocal critical-group map

Let `C,D` be defect components, put

```text
L_C = (q-1)I-D[C],
B_CD = A[C,D].
```

Because `A` commutes with `A^2=(q-1)I+J-D`, its component blocks satisfy

`L_C B_CD = B_CD L_D`.

The block `B_CD` has constant row and column sums (`m_D` and `m_C`,
respectively).  It therefore maps the integral root lattice
`1_D^perp` to `1_C^perp`, and the displayed intertwining induces a map
between the corresponding critical-group presentations.  Reciprocity is
literal: `B_DC=B_CD^T`, so the two induced maps are adjoint for the usual
Laplacian linking pairings whenever those pairings are defined at the prime
under consideration.

This is a genuine simultaneous-block statement, unlike the isolated packing
Gram.  It is nevertheless not yet an inverse or an isometry: the block
equations do not say that `B_DC B_CD` is a scalar modulo `L_D`.  That missing
congruence is exactly what a local square-class theorem would need.

## 2. Exact `q=4` control

For each of the two order-eight defect components in `sixteenRegular`, a
reduced Laplacian has Smith factors

`[1,1,1,1,1,7,56]`,

so `tau=392`.  The reciprocal cross block has Smith factors

`[1,1,1,1,1,1,1,0]`.

The induced behavior is sharply prime-dependent.

- Modulo `7`, the full Laplacian kernel has dimension three.  After
  quotienting its constant line, `B_CD` has rank two, hence gives an
  isomorphism between the two nonconstant critical kernels.
- Modulo `2`, the full Laplacian kernel has dimension two, but `B_CD` sends it
  into the constant line.  Its induced map on the nonconstant quotient has
  rank zero.

Thus the example supports odd-primary pairing at `p=7`, while simultaneously
falsifying any prime-uniform inverse statement.  Notice also that `7` is not a
divisor of `q-1=3`; a theorem restricted to primes dividing the defect degree
would miss the observed tree torsion.

## 3. Why self-adjoint generalized kernels alone do not pair components

On the direct sum of centered component spaces, write `X=A|_(sum 1_C^perp)`.
Then

`X=X^*` and `X^2=directSum_C L_C`.

If one `L_C` acquires an extra kernel modulo an odd prime, the quotient
`ker(X^2)/ker(X)` is the length-two nilpotent layer.  Symmetry supplies its
standard adjoint pairing, but does **not** force this quotient to have even
dimension or to be supported on two different components.

The smallest abstract warning is already over `F_3`.  The vector
`v=(1,1,1)` is isotropic for the standard dot product, and

`N=v v^T`

is a nonzero symmetric rank-one matrix with `N^2=0`.  Hence
`ker(N^2)/ker(N)` is one-dimensional even though `-1` is nonsquare.  In
Jordan-chain language, a length-two self-adjoint zero block has Gram
discriminant `-a^2`; its nonsquare class can be absorbed by the nonsingular
orthogonal complement rather than by a second nilpotent block.

This abstraction does not obey all graph support, diagonal, and row-sum laws,
so it is not a countermodel to `A-REG`.  It does cut the proposed inference

```text
p == 3 mod 4 + symmetric square root
    => even nonconstant p-primary nullity componentwise.
```

Any surviving theorem must use the actual `0/1` reciprocal blocks to prove an
additional congruence such as

`B_DC B_CD = unit (mod L_D)`

on a specified primary quotient, or compute the global discriminant/Hasse
class including the nonsingular complement.  Self-adjointness and the square
identity alone recover only the already-banked global product-square law.

## 4. Disposition

- Retain `L_C B_CD=B_CD L_D` and the induced reciprocal critical-group maps as
  a precise interface.
- Retain the `p=7` isomorphism in the `q=4` control as evidence that an
  odd-primary support-sensitive theorem may exist.
- Stop the bare `p == 3 mod 4` generalized-kernel parity route and every
  prime-uniform inverse claim.
- The next useful probe is either an exact formula for
  `B_DC B_CD` on critical quotients, or the first nonzero 2-adic
  Cauchy--Binet layer of the incidence minors.  Without one of these, no
  componentwise residue is available to contradict
  `q^(r+2) product_C(m_C tau_C)` being a square.

# Size-two factor-kernel Bockstein audit

## Purpose

`SIZE_TWO_TILE_FACTOR_RECONSTRUCTION.md` proves a genuinely branch-wide
interface: the family of individual tiles through a fixed via color recovers
the real kernel of its reused two-factor.  A natural next proposal is to pass
the corresponding binary kernel flag through a first `Z/4` Bockstein and hope
to read cycle-length parity.  This note records the exact value of that lift.

The verdict is negative at first order.  The Bockstein is just the canonical
transport of incidence-component indicators.  It contains no half-length
parity beyond the component/shores data already exposed by the binary kernel.

## General two-factor calculation

Let `X` be a zero-one square matrix with every row and column sum two.  Choose
a decomposition into perfect matchings

```text
X = P + Q = P (I + sigma),       sigma = P^T Q.
```

The permutation `sigma` is well defined up to the usual matching swap and
conjugacy gauges.  Its orbits are the incidence-cycle components of `X`,
viewed from the domain shore.  Over `F_2`,

```text
ker(X) = ker(I + sigma)
```

has the orbit indicators `1_C` as a basis.

For a binary kernel vector `v`, lift it to its zero-one integer vector and
define the first integral lift

```text
beta_X(v) = (X v)/2  (mod 2).
```

For an orbit indicator, `sigma 1_C = 1_C`, and hence

```text
X 1_C = P(I + sigma)1_C = 2 P 1_C,
beta_X(1_C) = 1_(P C).
```

Thus `beta_X` merely sends a domain incidence component to its corresponding
range incidence component.  In particular it is a permutation of the
component-indicator bases.  No orbit length occurs in the formula.

Changing the matching decomposition does not create new numerical data: it
only changes the displayed component identification by the same shore and
matching gauges already present in the factor correspondence.

## Self-indexed diagonal cycles

For a diagonal block equal to the adjacency matrix of an even cycle `C_L`,
take `P` and `Q` to be the forward and backward cycle matchings.  Then
`sigma` is shift by two.  It has the two parity orbits of the cycle, and the
calculation above says that `beta_X` transports (equivalently, swaps after a
choice of shore identification) the two parity-class indicators.

For a disjoint union of even cycles this happens independently on every
cycle.  Again the first lift remembers the two shores of each bipartite
incidence component, but not `L/2 mod 2` or any higher length residue.

## Consequence for the active route

The real common-kernel reconstruction remains useful: it proves that
individual tile families retain information erased by their sum.  But its
first `Z/4` lift lands exactly in the incidence-component transport and
sheet-holonomy interface already audited in the simultaneous-routing work.
It therefore cannot by itself yield the all-size-two contradiction.

Any arithmetic continuation must use genuinely higher data—for example a
second lift with a specified integral preimage, or coefficients that depend
on positions *inside* an incidence cycle.  Merely assigning a quadratic value
to the first Bockstein component flag silently repackages the old shore
pairing and should not be treated as a new invariant.

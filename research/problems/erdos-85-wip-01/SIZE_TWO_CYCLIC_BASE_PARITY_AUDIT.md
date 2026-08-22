# Size-two cyclic base-parity audit

## Setup

Work in the connected cyclic exterior grid underlying
`BinarySizeTwoCyclicPackingBound`.  Let

```text
q = 2^k,  k>=3,       d=q-2,       h=d/2,
N=q(q-2)=d(d+2).
```

The exterior cells are `(x,t)`, with two reflected difference fibers omitted.
Those two hole differences are `a` and `-1-a`, so they have opposite parity.
The exterior adjacency has the exact row-hit and column-hit laws and is
C4-free.

This audit retains the parity of the base coordinate `x`.  It is the first
fiber-labelled refinement after the aggregate collision and scalar exterior
distance ledgers.

## Exact neighbor split

From a source `(x,t)`, target base coordinates are `x+r` for all relative
rows `r` except `t,t+1`.  The two omitted rows have opposite parity.  Hence
exactly

```text
h=q/2-1
```

neighbors have even base displacement and exactly `h` have odd displacement.
Equivalently, if the exterior vertices are split by parity of `x`, every
vertex has `h` neighbors on each side of that split.  The alternating base
sign `(-1)^x` is therefore a zero eigenvector of the exterior adjacency.

This zero mode is the order-two character shadow of the already known cycle
spectral transport; by itself it is not a new spectral obstruction.  Its
value is that it refines the nonlinear disjoint-pair ledger.

## Disjoint traces by base parity

Fix a cell `(x,t)`.  For a prospective trace `(x',t')` to be disjoint, one
needs both `x' != x` and the second component coordinate to differ.  Among
the two rows in which a fixed second coordinate is a hole, exactly one has
the same base parity as `x` and one has the opposite parity, because the two
hole differences have opposite parity.  Direct counting gives the number of
disjoint partners:

```text
same base parity:      D_same  = h(d-1)+1,
opposite base parity:  D_cross = h(d-1)+d.
```

Their sum is `d^2+1`, the scalar disjoint-trace count.

At a middle exterior vertex, unordered pairs of neighbors with the same base
parity number

```text
2*C(h,2)=h(h-1),
```

while pairs with opposite base parity number `h^2`.  C4-freeness makes all
these two-walk endpoints distinct.  Therefore the unordered disjoint pairs
with no exterior common neighbor split exactly as

```text
S_same  = N*D_same/2  - N*h(h-1) = N(h+1)/2,
S_cross = N*D_cross/2 - N*h^2     = Nh/2.
```

Adding them recovers `N(d+1)/2`, but neither summand is visible in the scalar
ledger.

## Parity-refined far-pair identities

The exact neighbor split also gives `Nh/2` exterior edges of each base-parity
type.  Let

* `R_same,R_cross` count resolver edges (adjacent traces sharing a component
  endpoint) by base parity;
* `Theta_same,Theta_cross` count disjoint-trace exterior edges lying in their
  unique exterior triangle;
* `L_same,L_cross` count far disjoint pairs with no exterior edge and no
  exterior common neighbor.

All non-resolver exterior edges join disjoint traces.  Splitting each slack
class into residual nontriangle edges and far pairs yields

```text
L_cross = R_cross + Theta_cross,
L_same  = N/2 + R_same + Theta_same.
```

These are exact integer identities, not merely congruences.  Moreover the
resolver graph is 2-regular, so every cut of it has even size and `R_cross`
is even.  Every triangle has either zero or two cross-parity edges, so
`Theta_cross` is even.  Consequently

```text
L_cross is even.
```

## Scope and next consumer

This does not yet prove `BinarySizeTwoCyclicPackingBound`.  It refines the
previous scalar identity by a row label and shows exactly where parity can
enter, but the two refined equations remain arithmetically feasible.  A
closing consumer must control the *locations* of cross-parity far pairs or
relate `R_cross` to the source-fiber displacement law.  The promising target
is a second refinement by residues modulo `4`: the two omitted consecutive
rows then occupy adjacent residue classes rather than merely opposite parity,
so reciprocity may constrain the four resolver cut sizes separately.

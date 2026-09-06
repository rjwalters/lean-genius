# Half-turn symmetry forces an exterior defect split

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: uniform mathematical exclusion of half-turn-invariant completions
of the fixed cyclic carrier with connected exterior defect. This is a
proof audit, not a Lean theorem. Arbitrary completions need not preserve
the carrier's half-turn, so the general node remains open.

## Hypotheses

Let q be even, q>=8. Use the carrier of
`NONBIP_MIXED_SIZE_TWO_TRIPLE_COMPANION_AUDIT.md` on `C=Z/(2q)`:
H has differences ±1, D_C has the odd differences except ±1 together with
q, and L has all remaining nonzero differences except ±2. Put n=q-2,
`F=E(L)`, and let B be the unsigned incidence matrix. Let

```text
tau(a)=a+q,      tau({a,b})={a+q,b+q},
Z={e in F : the endpoints of e have opposite parity}.
```

The set Z consists exactly of the 2q H-cycle selector edges. Its complement
has q(q-4) elements, all same-parity selectors. Translation tau preserves
parity because q is even. No L-edge is antipodal, so tau acts freely on F;
moreover e and tau(e) are disjoint for every e in F.

Suppose T is a symmetric zero-one exterior adjacency matrix with zero
diagonal satisfying the cross block, and D_F is a simple exterior defect
graph satisfying the full Gram equation:

```text
HB+BT=J_CF,
H^2+BB^T=(q-1)I_C+J_C-D_C,
B^TB+T^2=(q-1)I_F+J_F-D_F.                            (1)
```

For the `[q-2,2]` partition, D_F is required to be connected. The additional
hypothesis to be excluded is

```text
T_(tau(e),tau(f))=T_(e,f)           for every e,f in F.  (2)
```

This is only half-turn invariance, weaker than translation invariance.

## Defect transport follows from the full equations

Column sums in the cross equation give every column of T sum n, and
symmetry gives its row sums. H has degree two; B has row degree n and
column degree two. Multiplying the cross equation on the left by H and
on the right by T, then subtracting, gives

```text
BT^2-H^2B=(n-2)J_CF.
```

Expand the two Gram equations in `D_CB-BD_F`. The cubic incidence terms
cancel, while `J_CB=2J_CF` and `BJ_F=nJ_CF`. Therefore

```text
BD_F=D_CB.                                             (3)
```

This is not an extra independent hypothesis.

## The endpoint budget is supported on two points

Fix a same-parity selector e={a,b}, and let P be that parity class of C.
Since the only same-parity D_C-neighbor of a is tau(a), (3) gives, for
every x in P,

```text
sum_(f in N_D_F(e)) 1_(x in f)
  = 1_(x=tau(a)) + 1_(x=tau(b)).                       (4)
```

The left side is a sum of nonnegative integers. A same-parity neighbor f
of e in P must therefore be exactly tau(e), using both units of the
budget. If it is present, e has no D_F-neighbor in Z. If it is absent,
both units must come from Z-neighbors, each contributing one endpoint in
P. Neighbors lying wholly in the other parity class contribute nothing.
Consequently, without assuming (2),

```text
deg_D_F(e,Z)=2(1-D_F(e,tau(e))).                         (5)
```

There are no other possibilities for a P-selector neighbor because its
two distinct endpoints would have to lie in {tau(a),tau(b)}.

## Half-turn invariance and the full cap force closure

By (2), tau maps the common T-neighbors of e and tau(e) to themselves.
It has no fixed point on F. If a common neighbor f existed, tau(f) would
be a distinct second common neighbor. But the selectors e,tau(e) are
disjoint, so their off-diagonal Gram entry in (1) gives

```text
(T^2)_(e,tau(e))=1-D_F(e,tau(e)) <= 1.
```

Thus there is no common neighbor, and `D_F(e,tau(e))=1`. Equation (5)
now implies `deg_D_F(e,Z)=0` for every e outside Z. Symmetry of D_F
shows Z is a union of connected components.

Since `|Z|=2q>0` and `|F\Z|=q(q-4)>0`, D_F cannot be connected.
This contradicts the stipulated `[q-2,2]` exterior component.

Therefore no completion satisfying (1), connected D_F, and (2) exists.
The proof is uniform and contains no finite enumeration or assumption
that q is a prime power beyond the stated evenness. The same proof works
for even q>4 whenever this carrier is used; q=4 has F=Z and no such
connectedness contradiction.

## What a completion without symmetry must do

Combining (5) with the disjoint-selector Gram entry gives the exact identity

```text
deg_D_F(e,Z)=2(T^2)_(e,tau(e))             (e outside Z). (6)
```

Connectedness of D_F forces a boundary edge of Z, hence some same-parity
selector e has exactly one common T-neighbor f with tau(e). The vertex
tau(f) cannot also be common. Thus any genuine completion must break
half-turn invariance in this concrete configuration: at least one of
the translated edges corresponding to e--f and tau(e)--f is absent.

This is a necessary condition for arbitrary completions, not their
exclusion. It identifies the exact missing step if one tries to extend
the symmetric argument: one would have to rule out these uniquely
resolved antipodal pairs without assuming (2).

## Consequence for future searches

The translation-invariant integral q16 witness already fails the full
cap, as its checker proves. The argument above explains why no repair
that retains half-turn symmetry can meet both the cap and the required
connected exterior defect. It does not assert that every such repair
must contain a C4: disconnected exterior defect is the other allowed
failure.

Do not impose half-turn or full translation invariance as a harmless
normalization of a genuine completion. Averaging preserves the linear
cross block, but destroys the integral common-neighbor cap. A search
with that symmetry can therefore miss every completion of the intended
connected exterior type. The fixed carrier itself is not a classification
of all size-two carriers, and A-REG-NONBIP remains open.

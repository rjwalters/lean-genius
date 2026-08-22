# q=16 reversed cycle-orientation audit

## Statement

In the q=16 weight-two alternating-eigenline reduced model with internal
ambient graph

```text
H = C6 disjoint-union C26,
```

the C6 cannot be cross-saturated while the C26 is T-saturated.  This already
follows from selector degree, the alternating eigenline, distance-two
exclusion, and the exact commutator `[H,F]=0`; no exterior adjacency is used.

The opposite orientation (C6 T-saturated, C26 cross-saturated) is the banked
reduced witness in `q16_weight_two_cycle_sync_reduced_sat.py`.

## Proof

Let `F` be the graph of outside two-point traces on the 32 component points.
It is 14-regular.  Write its block form relative to C6 and C26 as

```text
F = [[X,Y],[Y^T,Z]].
```

The exact cross-block identity for a genuine component gives `[H,F]=0`, so

```text
A(C6) X = X A(C6),        A(C26) Z = Z A(C26).
```

Because each cycle is connected and 2-regular, its eigenvalue-2 eigenspace is
spanned by the all-ones vector.  Applying the displayed commutators to the
all-ones vector shows that the internal F-degrees are constant: say `r` on
C6 and `s` on C26.  Therefore cross-edge balance gives

```text
6(14-r) = |E_F(C6,C26)| = 26(14-s).        (1)
```

The alternating eigenline requires every F-edge to join opposite signs.
Inside C6, the only opposite-sign pairs are its six cycle edges and its three
opposite pairs.  Distance-two pairs are same-sign and are excluded anyway.
If C6 is cross-saturated, all six cycle edges lie in F, so its constant
internal degree is

```text
r=2   (without the opposite matching), or
r=3   (with the opposite matching).
```

For r=2, equation (1) says `26(14-s)=72`, impossible over the integers.  For
r=3 it says `26(14-s)=66`, also impossible.  Hence the reversed orientation
cannot occur.

## Interpretation

This is a genuine orientation asymmetry, not an all-or-nothing theorem.  In
the surviving orientation, C6 is T-saturated and its internal trace degree is
`r=1` (the opposite matching); equation (1) then forces `s=11`, exactly the
C26 circulant degree in the reduced witness.

The argument generalizes as a quotient constraint.  For two internal cycles
of lengths `ell` and `2q-ell`, exact commutation makes their internal trace
degrees constant, and cross-edge balance forces

```text
ell * (q-2-r_1) = (2q-ell) * (q-2-r_2).
```

Combining this divisibility law with the few internal degrees allowed by the
alternating signs, distance-two exclusion, and a chosen saturation orientation
can eliminate orientations without constructing the exterior.  It does not
yet exclude the surviving C6-T/C26-cross orientation, whose full exterior
completion remains open.

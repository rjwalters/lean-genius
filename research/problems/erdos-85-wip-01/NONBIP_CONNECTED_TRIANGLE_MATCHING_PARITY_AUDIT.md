# Triangle/K parity versus signed matching exchange

Date: 2026-08-26.  This is the first bounded consumer joining the two
positive round-73 mechanisms: the triangle/Eulerian-remainder decomposition
and signed Levi perfect-matching exchange.

## Question

Every A-edge is either owned by a unique triangle or belongs to the
triangle-free remainder `K`.  Could the parity of K-edges in an alternating
Levi cycle determine whether switching that cycle changes determinant sign?
If so, triangle-owned odd switches could generate within-sign classes while
K parity controlled the sign-changing quotient.

For an alternating cycle of half-length `ell`, the switch changes
permutation sign exactly when `ell` is even.  Its symmetric difference has
`2 ell` A-edges, so triangle-edge parity and K-edge parity are equal; it
suffices to test K.

## Exact q4 result

`nonbip_connected_triangle_matching_parity_control.py` constructs the exact
eight triangles and eight K-edges of the fixed-free q4 control, enumerates
the first twelve Levi perfect matchings, and exhaustively enumerates every
single alternating-cycle switch from them.  The joint counts

```text
(half-length parity, K-edge-count parity) : count
(odd,  odd)  : 20,377
(odd,  even) : 19,864
(even, even) : 19,735
(even, odd)  : 18,755
```

contain all four combinations.  Concrete first witnesses have
`(ell,#K)=(5,6),(13,9),(8,8),(12,9)` respectively.  Thus neither K parity
nor triangle-edge parity determines the sign of a switch, even on the
faithful control where both parent mechanisms calibrate positively.

## Verdict

**CUT the coarse parity quotient.**  The Schur decomposition does not by
itself label the two shores of the matching exchange graph, and merely
counting triangle-owned versus K edges cannot prove Hall expansion.

This does not cut either parent mechanism.  A combined proof may still use
the actual triangle owner labels, the order in which an alternating cycle
visits them, or the Schur potential `M^(-1)1`.  What is ruled out is the
tempting one-bit quotient based only on the H/K edge partition.

# Parity-missing-rank boundary audit

Node: the structural PMR inequality beneath
`BinarySizeTwoCyclicPackingBound`.

## Aggregate Hall deficiency is not the mechanism

For the q8/a2 cap-free witness with

```text
total defect rank <= 70,
R(0)+R(1) <= 15,
```

the two aggregate difference-multiplicity support graphs are both connected
and have perfect matchings.  Relative to a maximum matching, each directed
Dulmage--Mendelsohn graph is one strongly connected component on all twelve
row/column vertices.  The separate zero-slot and positive-excess graphs
also have several components.  Hence PMR cannot be proved by claiming that
a bad adjacent pair creates a unique Hall-deficient component in either
aggregate base matrix.

The rank-64 equality witness gives the same negative diagnosis.  Its
parity-selected zero-slot graphs have two or three components in every
adjacent window, not one propagating component.

## Exact boundary permutations

`size_two_cyclic_full_probe.py --dump-route-table` prints, for every source
cell `(x,t)`, the exact map from target base `y` to target-difference fibre
`u`.  This exposes the shared-hole interface directly.

For adjacent bases `x,x+1`, take the unique route from `(x,t)` in the first
column outside their shared column hole, `c=x+1`, and the unique route from
`(x+1,t)` in the opposite boundary column `c=x-1`.  Exact column hits make
their target-fibre labels two permutations `L_x,R_x` of the allowed
difference set.  Define the boundary monodromy

```text
P_x = R_x^{-1} L_x.
```

In the rank-70 witness at its bad pair `x=0`, the permutations are

```text
L = {0:3, 1:6, 3:7, 4:1, 6:0, 7:4},
R = {0:3, 1:0, 3:6, 4:7, 6:1, 7:4},
P cycles = (0)(7)(1 3 4 6).
```

Thus the boundary object has two fixed fibres and one cycle on the other
`q-4` fibres.  This is the first concrete alternating component aligned
with the adjacent-rank dip.

For comparison, a rank-64 q8/a2 equality model is period two in `x`; its
boundary-monodromy cycle types alternate

```text
5+1,  4+2,  5+1,  4+2, ... .
```

The observed cycle types come from individual witnesses.  Sampling the
rank-70 query with Z3 seeds 1 through 8 falsifies their invariance: the bad
pair realizes cycle types

```text
1+1+4,  1+2+3,  and  2+4.
```

In particular neither two fixed fibres nor one prescribed long cycle is
forced.  The boundary permutations are canonical data, but their ordinary
cycle type is not the propagating invariant.  What survives this audit is
only the negative conclusion: neither aggregate Hall/DM components,
parity-zero components, nor unweighted boundary-monodromy cycles explain
PMR.  A viable boundary argument must retain labels/weights (missing and
positive-excess tokens, or the parity charge `Q`) rather than just support
connectivity.

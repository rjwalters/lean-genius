# NONBIP-CONNECTED triangle-flip quotient audit

Status: bounded falsification, 26 August 2026.  This cuts the clean orbit-
quotient version of the signed Levi matching proposal; it does not cut the
full sign-changing exchange graph.

## Proposed mechanism

An alternating Levi 6-cycle has half-length three, so switching it preserves
the permutation sign of a perfect matching.  A tempting way to use the
self-indexed triangles is therefore:

1. quotient perfect matchings by alternating 6-cycle switches;
2. join two quotient classes when some representatives differ by one
   sign-changing alternating cycle;
3. prove this bipartite quotient has a perfect matching, then lift it to a
   sign-reversing pairing of determinant terms.

This would turn the large, nonregular exchange graph into an orbit graph whose
edges remember triangle placement rather than only cycle length.

## Exact q=4 falsifier

`nonbip_connected_triangle_flip_quotient_q4.py` enumerates all 19,972 perfect
matchings of the banked faithful q=4 matrix.  It generates every alternating
6-cycle switch directly in the matching-contracted digraph and obtains:

```text
triangle-flip edges                         155,808
triangle-flip components                         6
positive-sign components / negative-sign       5 / 1
component sizes                    1, 1, 1, 1, 9,982, 9,986
sign-changing component-quotient edges              5
```

Every triangle-flip component is sign-homogeneous, as required, but the two
shores have different component counts.  The quotient is a five-leaf star:
each positive component meets the unique negative component.  Thus it cannot
have a perfect matching.  In particular, an unweighted Hall theorem for the
triangle-flip quotient is false even on the smallest exact self-polar control.

The mass balance remains exact: the five positive components have total size
9,986, equal to the single negative component.  Hence a substantially more
delicate transport theorem could still work, but it must split an orbit and
control vertex-level capacities.  Orbit-level pairing, canonical pairing of
whole triangle classes, and any proof that treats each class as one unit are
ruled out.

## Consequence for the critical path

The full q=4 sign-changing exchange graph still has a verified perfect
matching.  This audit only shows that sign-preserving triangle connectivity
does not expose it through an ordinary quotient matching.  A viable successor
must prove a capacitated Hall/transport statement using class cardinalities,
or return to a vertex-level global potential.  Merely combining the
Naddef--Pulleyblank full flip theorem with triangle-orbit contraction cannot
close `BinarySquareRegularExclusion`.

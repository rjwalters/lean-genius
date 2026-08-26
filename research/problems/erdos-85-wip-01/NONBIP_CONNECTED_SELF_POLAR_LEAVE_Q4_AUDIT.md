# NONBIP-CONNECTED self-polar leave q=4 audit

Status: bounded faithful probe under round 71, 26 August 2026; no verdict on
the full q=4 instance.

The proposed self-polar packing-leave theorem asks whether a symmetric
loopless `q`-regular C4-free matrix on `q^2` vertices can have connected
deficiency graph.  At q=4 this is a finite faithful test, not a relaxation.

`nonbip_connected_inverse_potential_q4_sat.py` now has
`--connected-defect`, which encodes exact bounded reachability in the graph

```text
D(i,j) iff i != j and commonNeighbors_A(i,j) = 0.
```

The encoding keeps all original symmetry, degree, and C4 constraints.  The
root neighborhood is a matching, so `--root-triangles {0,1,2}` is a complete
split into its three isomorphism types.

Bounded results with Z3 were:

```text
unsplit, 60 s: UNKNOWN
root-triangles 0, 30 s: UNSAT
root-triangles 1, 30 s: UNKNOWN
root-triangles 2, 30 s: UNKNOWN
```

The type-0 result is not a connectivity insight: that stratum is already
UNSAT without `--connected-defect`.  Type 1 is SAT without connectedness,
which provides a regression for the added reachability constraints.

As a separate enumeration control, 606 ordinary faithful models were
generated before the same bounded run stopped; every one was singular with
rational rank exactly 15.  Since nonsingularity is equivalent to connected
deficiency in this interface, this is a small-parameter signal but not a
proof.

The cheapest falsifier therefore did not refute the self-polar-leave
statement, but neither did it certify it.  The q=4 CSP is already difficult
in the two realized local strata, so extending this into a census would be
another finite siege and is cut under goal 36.  The useful bank is the exact
connectivity switch for future targeted falsification if a stronger local
invariant eliminates one of the remaining matching types.

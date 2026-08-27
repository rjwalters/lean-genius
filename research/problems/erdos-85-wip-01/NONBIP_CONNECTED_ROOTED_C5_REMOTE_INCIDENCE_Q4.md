# NONBIP-CONNECTED rooted C5/remote-edge incidence audit

## Proposed link complex

The divergence-77 link-complex wildcard proposed taking ambient edges internal
to the remote layer `R_x` as 1-cells and rooted simple 5-cycles as 2-cells, in
the hope that

```text
e_A(R_x) - C5_x + 3 t_x
```

would become an Euler characteristic or boundary-rank residue.

## Structural cut

The direct boundary incidence is identically zero.  Write a rooted simple
5-cycle as

```text
x - a - b - c - d - x.
```

Then `a,d` are neighbors of `x`.  The vertices `b,c` each have an `A`-path of
length two from `x`, so they lie in the second layer (C4-freeness makes their
rooted common-neighbor branch unique).  The only cycle edge not incident to a
neighbor of `x` is `bc`, and it is therefore an edge between second-layer
branches, not an edge internal to `R_x`.  No rooted C5 contains a remote edge.

Consequently the incidence matrix between `e_A(R_x)` and rooted C5s is the
zero matrix for structural reasons.  Its GF(2) rank is always zero and it
cannot pair the two terms in the desired residue.

## Exhaustive q=4 confirmation

`nonbip_connected_rooted_c5_remote_incidence_q4.py` checks 256 labelled
models and all 4096 roots.  The only profiles are

```text
(t,B,|R|,E,C5,target,rank) = (1,4,1,0,9,2,0)
(t,B,|R|,E,C5,target,rank) = (2,2,3,2,6,2,0).
```

Every rooted C5 has remote-incidence degree zero, and every remote edge has
cycle-incidence degree zero.

## Verdict

The naive rooted C5/remote-edge link complex is cut.  The two counts live in
disjoint distance layers, so a topological explanation needs additional
connecting 1-cells or 2-cells encoding the layer handshakes.  Merely declaring
remote edges and rooted C5s as adjacent-dimensional cells produces a zero
boundary and restates the cardinality residue without mechanism.

## Nonbacktracking reversal follow-up

The remaining orbit proposal also stops at the known count.  A rooted closed
length-five walk

```text
x,v1,v2,v3,v4,x
```

with no immediate reversal at the four internal positions has only two
possible shapes in a simple C4-free graph:

1. `v1,v2,v3,v4` are distinct, giving a simple rooted C5;
2. `v1=v4`, giving a triangle `v1,v2,v3` not containing `x`, attached to
   `x` at its unique neighbor `v1`.

All other repetitions are either loops or immediate reversals.  In the second
case C4-freeness prevents `v2` or `v3` from also being adjacent to `x`, so the
triangle is exactly one of the objects counted by `B_x`.

Walk reversal is fixed-point-free and has two orientations for every object.
Consequently

```text
number of oriented rooted nonbacktracking closed 5-walks = 2(B_x + C5_x),
number of reversal orbits = B_x + C5_x.
```

The q=4 profiles give orbit counts `4+9=13` and `2+6=8`, so even the parity of
the reversal quotient is not uniform while the desired residue is uniformly
2 modulo 4.  Reversal therefore supplies only the familiar factor of two; it
does not create four-element orbits or eliminate the C5 term.  Moreover, a
simple C5 has no guaranteed `D`-chord: every distance-two pair already has its
intermediate common neighbor.  The proposed "first defect chord" operation is
not defined on all cycles.

Thus rooted nonbacktracking reversal is cut as a standalone mechanism.  Any
successful orbit proof needs a new total operation mixing the triangle-tail
and C5 classes and using global square-order data; ordinary reversal and local
C4-freeness do not provide it.

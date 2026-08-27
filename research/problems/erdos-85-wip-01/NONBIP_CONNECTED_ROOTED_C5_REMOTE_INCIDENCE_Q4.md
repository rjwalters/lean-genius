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

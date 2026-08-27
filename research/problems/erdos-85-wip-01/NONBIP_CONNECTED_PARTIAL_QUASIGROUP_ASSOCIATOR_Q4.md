# NONBIP-CONNECTED partial-quasigroup associator calibration

Date: 27 August 2026. Node: `A-REG-NONBIP / NONBIP-CONNECTED [q]`.
Status: **positive q=4 calibration only; no q-generic propagation theorem**.

## Candidate operation

For distinct vertices `x,y` which are not joined in the second-order defect
graph, C4-freeness and the square-order identity give a unique common ambient
neighbor.  Write it as

```text
x * y = the unique element of N_A(x) intersect N_A(y).
```

This is a commutative partial operation whose holes are exactly the defect
edges.  Unlike a proposed parallelism equivalence, it retains the canonical
common-neighbor label.  Divergence round 81 proposed testing whether the
boundary of its associator

```text
(x*y)*z  versus  x*(y*z)
```

sees the two rooted congruences in the sharp connected terminal.

## Exact bounded result

The verifier

```text
python3 research/problems/erdos-85-wip-01/
  nonbip_connected_partial_quasigroup_associator_q4.py --models 256
```

enumerates 256 labelled q=4 boundary controls with the standard fixed root
neighborhood.  For every root `x`, it counts ordered pairs `(y,z)` according
to whether both associator sides are defined and equal, both are defined and
unequal, or exactly one side is defined.  All 256 controls have the same
profile:

```text
t_x=1: (equal, unequal, left-only, right-only) = (10,80,54,54)
t_x=2: (equal, unequal, left-only, right-only) = (16,66,62,62)
```

Thus modulo four,

```text
equal(x)   = 2 t_x       (mod 4),
unequal(x) = 2(t_x-1)    (mod 4)
```

on every sampled vertex.  Each of the four associator residues is constant
across every defect edge, as is `t_x`; the ambient-neighbor triangle mass is
also uniformly `At=6=2 (mod 4)`.

## Scope and next falsifier

This calibration does not prove either displayed congruence for general q,
and it does not explain preservation across a defect edge.  At q=4 the
defect graph has two components, so componentwise constancy may merely be a
repackaging of the already-known triangle-degree split.  Counting associator
terms without a boundary operation would therefore be another recognition
result, not a force.

A viable successor must exhibit an explicit pairing or signed boundary on
associator witnesses for a defect edge `xy` whose unpaired terms evaluate to
`2(t_x-t_y)` modulo eight.  The cheapest decisive falsifier is to implement
that proposed pairing on the same 256 controls before attempting a general
proof.  Absent such an operation, this route remains calibrated but open and
should not accumulate higher associator moments.

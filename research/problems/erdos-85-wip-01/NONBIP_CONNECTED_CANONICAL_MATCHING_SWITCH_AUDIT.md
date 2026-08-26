# NONBIP-CONNECTED canonical matching-switch audit

## Question

The signed Levi matching-exchange calibration proves that the faithful q=4
exchange graph has a perfect matching, while correctly leaving a q-generic
Hall theorem open.  A potentially shorter alternative is to choose one even
alternating cycle canonically in every Levi perfect matching and switch it.
For termwise determinant cancellation, that choice must be stable under its
own switch: applying it twice must restore the original matching.

## Bounded falsifier

`nonbip_connected_canonical_matching_switch_control.py` uses the same exact
q=4 self-polar C4-free control and its lexicographically first Levi matching.
It tests the two natural label-based rules:

1. lexicographically least normalized even alternating cycle;
2. shortest even alternating cycle, then lexicographically least.

Both fail on the first matching.  For the first rule, the selected 8-cycle

```text
(0,3,13,6,5,1,8,4)
```

is replaced after switching by the newly preferred 12-cycle

```text
(0,1,3,14,7,2,5,4,11,12,10,9),
```

not by the reverse restoring cycle.  For the shortest-first rule, the first
4-cycle `(0,3,15,5)` changes the preferred cycle to `(0,5,14,7)`, again not
the inverse.  The verifier asserts both failed restorations exactly.

## Verdict

**The naive canonical-switch alternative is cut.**  A switch changes the
contracted directed graph and can create an earlier eligible cycle, so label
minimality is not involutive.  This does not weaken the positive q=4 perfect
matching or the open Hall-expansion route: a global pairing can exist without
arising from a local greedy selector.  Any canonical successor must include a
switch-stable global potential or use the triangle/Eulerian decomposition;
do not try further lexicographic tie-break variants without such an invariant.

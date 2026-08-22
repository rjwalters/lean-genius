# q=4 size-two trace dichotomy audit

## Question

Let `A` be a loopless 4-regular C4-free graph on 16 vertices whose
second-order defect graph has two components `C` and `C'` of order eight.
For `z in C'`, its trace `N_A(z) intersect C` has size two.  Must the number
of `z` for which that trace is an `A`-edge be either zero or eight?

This is the smallest exact falsifier for the proposed q-generic
all-or-nothing trace lemma under `A-REG-NONBIP / NONBIP-MIXED`.

## Exhaustive result

Yes at q=4.  The component quotient laws make `A[C]` and `A[C']`
2-regular.  C4-freeness excludes a four-cycle, so an eight-vertex induced
block has only two possible cycle types:

* `C8`;
* `C5 disjoint-union C3`.

The script `q4_size_two_trace_all_or_nothing_sat.py` fixes canonical
representatives of the four ordered type pairs and leaves all 64 cross
edges symbolic.  In every case it imposes exactly:

* cross degree two at every vertex (hence total A-degree four);
* pair codegree at most one (C4-freeness);
* cross pair codegree exactly one (no defect edge between components);
* internal defect degree three;
* a trace-edge count strictly between zero and eight.

Z3 returns `unsat` in all four cases.  Canonical cycle representatives lose
no cases because the cross-edge variables remain unrestricted.

Run:

```text
python3 research/problems/erdos-85-wip-01/q4_size_two_trace_all_or_nothing_sat.py
```

## Structural reading and q-generic boundary

At q=4 the cross graph `A[C,C']` is 2-regular.  Each of its edges has a
unique common neighbor, and C4-freeness makes the resolution occur on
exactly one side.  When a vertex's two cross neighbors form an internal
edge, both incident cross edges resolve on that side; otherwise neither
does.  Thus the side-choice propagates around every cross cycle.  The SAT
result additionally says the exact defect constraints do not permit a mix
of differently oriented cross cycles.

The first propagation step is special to q=4.  For a weight-two component
at general q, vertices inside it have `q-2` outside neighbors, while an
outside vertex still has a two-point trace.  The cross incidence graph is
therefore `(q-2,2)`-biregular, not 2-regular, and the binary orientation
argument at the component vertices disappears.  Consequently this audit
supports the proposed lemma in the exact control but does **not** establish
the q-generic statement.  A uniform proof still needs a constraint coupling
the many outside resolutions incident to one component vertex, or a
q-generic countermodel with an intermediate trace count.

# RETRACTED: B.3 is not matroid intersection

Date: 2026-08-24

Owner: codex-sol-2

Scope: goal #36, B.3 generic-transfer outside probe

## Retraction

Commit `0209a083dd` claimed that the directed fractional system (12g) in
`B3_HOLE_PARTITION_OBSTRUCTION_AUDIT.md` was a common-base problem for two
direct sums of truncated transversal matroids.  That claim is **false**.
Commits `7b7c4fe2cb` and `3c3a16afb3` derived oriented-cut and dual-rank
statements from the same false premise and are retracted with it.

The error was caught while attempting to implement the proposed deficient-
set extractor.  In the augmented graph of (12f), a candidate is an **edge**
whose two endpoints are its two selected labels.  A singleton-label
candidate is completed to an edge by adding its own private dummy.  Choosing
several residual neighbours is therefore choosing a set of pairwise
vertex-disjoint edges.  A two-label candidate consumes both label capacities;
it is not a left vertex which may be matched to either one of its labels.

The false translation replaced every candidate edge by a left vertex and
allowed it to choose one endpoint.  That relaxation forgets one of the two
fiber caps and is not the polytope `P_t` used in (12g).

## Minimal counterexample

Matchings of a bipartite graph do not form the independent sets of a matroid.
In the three-edge path

```text
a --e1-- b --e2-- c --e3-- d
```

both `{e2}` and `{e1,e3}` are matchings, but neither element of the larger
matching can be added to `{e2}`.  This violates matroid exchange.  Hence the
candidate-edge matching system is not generally a transversal matroid on
candidate arcs, and its cardinality face is not a matroid base polytope.

Therefore the asserted identity `P = B(M_out)`, the Edmonds rank inequality,
its oriented uncrossing, and its dual-rank form do not follow and must not be
used downstream.

## What remains valid

The original audit remains correct:

- each individual row polytope is an integral bipartite matching polytope;
- its unweighted feasibility has a Kőnig/Hall cover certificate (12fa);
- its weighted support function has the exact matching dual (12fb)--(12fc);
- the product `P` intersected with its transpose image has the general
  antisymmetric separation certificate (12h)--(12n).

What fails is the compression of those rowwise edge-matching systems to
matroids.  The outside dictionary stops at the already-known bipartite
matching LP dual and supplies no new global min--max theorem for transpose
coupling.

There is a precise corrected dictionary.  For one row, bipartite matching
is the intersection of the two partition-matroid capacity systems given by
the two label shores.  Imposing the transposed incoming constraints adds two
more partition-matroid systems on the same candidate arcs.  Globally, (12g)
is therefore a four-capacity-system problem, equivalently a four-resource
hypergraph `b`-matching-style LP with exact tail/head degree faces.  Ordinary
two-matroid intersection is exactly one intersection short.  This explains
both the failed Edmonds reduction and why its one-cut certificate has no
reason to exist; it also agrees with the audit's observed LP/integrality
separation.

No Lean wrapper or deficient-set script is opened.  Any renewed discrete
route must retain both endpoints of every candidate edge, for example through
the exact matching-cover prices already present in (12fb), rather than
projecting candidates to one chosen label.

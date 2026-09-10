# Universal H7 singleton-capacity exclusions

Fifteen of the43 possible seven-vertex empty-support graph classes fail a
necessary singleton-incidence condition. This leaves7,12,7,2 classes at
empty-edge count a=6,7,8,9 respectively. There is no triangle-count or
residual-spectrum premise, and no whole H7 sector is excluded.

## Actual graph incidence constraint

Use the actual H7/T0 support census:7 empty vertices E,14 singleton-support
vertices S,21 pair-support vertices P. Write A=G[E], a=e(E), and d(v)=deg_A(v).
The reviewed support-edge ledger gives

    e(E,S)=49-4a,   n_S(v)=7-2d(v).

Each singleton has at most two empty neighbors, while each pair-support
vertex has at most one. These are the existing local quotient capacities
n_E<=3-t for support size t. Let X be the graph on E whose edges are pairs
sharing an outside-low common neighbor. Such a neighbor must be a singleton.
By C4-freeness each pair has at most one such neighbor, so |X| equals the
number of singleton vertices having two empty neighbors.

If the14 singletons have E-degrees0,1,2 with counts z0,z1,z2, then
z1+2z2=49-4a and z0+z1+z2=14. Therefore

    |X|=z2=35-4a+z0 >= max(0,35-4a).

An X edge cannot join a pair that already has a common neighbor in E,
since this would give a C4. At each v, its incident X edges require distinct
singleton neighbors (each singleton has at most two E-neighbors). Thus

    X subset F := {uv : N_A(u) intersect N_A(v) is empty},
    deg_X(v) <= c(v) := 7-2d(v).

These observations apply to every a in6..9, not just the previously studied
nine-edge endpoint. They do not involve edges among the outside low vertices.

## Short upper-bound certificates

For any vertex subset U of E, each X edge touching U consumes at least
one of the sum of degree capacities on U. All other X edges belong to
F[E minus U]. Consequently

    |X| <= sum(c(v), v in U) + |F[E minus U]|.

This inequality is valid even when an X edge has both endpoints in U:
it then consumes two units, which only makes the stated upper bound looser.
For15 induced classes a subset U makes this upper bound strictly smaller
than max(0,35-4a). Each exclusion is therefore certified by just a vertex
subset, rather than relying on an optimization result.

| a | Induced classes | Excluded by capacity | Remaining |
|---|---:|---:|---:|
|6|19|12|7|
|7|15|3|12|
|8|7|0|7|
|9|2|0|2|

For each of the28 remaining classes the JSON also gives an explicit
allowed pair set of size max(0,35-4a) satisfying every degree capacity.
This certifies that this necessary capacity test alone cannot exclude it;
it is not an assignment of all high labels or an actual graph extension.

For example, the triangle with one pendant leaf at each triangle vertex
and one isolated vertex (canonical mask2387) has a=6 and requires |X|>=11.
There are12 allowed pairs. Each of the three triangle vertices has exactly
two allowed incident pairs but capacity1; those six pairs are distinct,
so at least three of them must be omitted. Thus |X|<=9, a contradiction.
The subset certificate U equal to the three triangle vertices gives the
same upper bound9. This universal argument supersedes a weaker proposed
fixed-spectrum cut for that class.

## Verification

Run `python3 verify_q7_h7_universal_singleton_capacity.py`.
It first replays the reviewed43-class induced enumeration, then reconstructs
F and c for each representative and checks all128 vertex-subset bounds.
It checks the15 strict contradictions and the28 explicit surviving pair
sets. No optimizer, timeout, full graph search, or spectrum test is used.
The finite enumeration and these graph arguments are not Lean certificates.
The separate actual triangle-free-empty lemma remains a distinct result.

The generic upper bound is proved in
`Erdos85VertexSubsetEdgeCapacity.lean` (review1665 PASS): for X contained
in an allowed graph F, it bounds the number of X edges by the degree
capacities on U plus the number of F edges avoiding U. Both the inequality
and its contradiction corollary pass source/public Lean builds with only
standard axioms. The actual H7 outside-pair graph construction and the
finite certificate enumeration are not formalized by this generic file.

`Erdos85ExteriorPairDegreeCapacity.lean` reuses the existing exterior-pair
graph definition and proves both the routed-witness degree bound and the
prohibition on an inside common neighbor (review1669 PASS).
`Erdos85OrderFortyNineSevenHighT0ExteriorPairCapacity.lean` discharges the
routing and two-neighbor premises in the actual H7/T0 graph: an outside
common neighbor has at least two empty neighbors, so the quotient capacity
and nonempty support force it into the singleton class. The resulting
actual inequality is degree_X(u)+2*n_E(u)<=7. Both sources and public builds
pass with standard axioms; actual-wrapper review1670 passed. The finite certificate bridge remains separate.

`Erdos85OrderFortyNineSevenHighT0ExteriorPairLowerBound.lean` supplies the
actual total-edge inequality35<=4a+|X| (review1672 PASS), using the singleton
census14 and the directed incidence equation I10+4a=49. Its generic
injection dependency is `Erdos85ExteriorPairEdgeLowerBound.lean`
(review1671 PASS). Source and public builds pass with standard axioms.

`Erdos85OrderFortyNineSevenHighT0ExteriorCapacityInequality.lean` combines
these graph-side bounds for every subset U of the actual empty fiber.
It defines the allowed graph F by absence of an inside common neighbor
and proves35<=4a+sum_U(7-2*n_E)+|F edges avoiding U|. Source and public build
pass with standard axioms; review1675 passed.
The43-class enumeration, numerical representative certificates, and their
isomorphism transfer are not certified by that theorem.

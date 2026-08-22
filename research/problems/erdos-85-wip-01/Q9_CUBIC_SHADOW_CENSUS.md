# q=9 cubic-shadow census

For a vertex-transitive, C4-free, 9-regular graph on 80 vertices, the
triangle-free-edge shadow `F` is vertex-transitive and cubic.  It contains
neither a triangle nor a four-cycle, so it has girth at least five.

`F` need not be connected.  Vertex transitivity permutes its connected
components transitively, and the stabilizer of a component is transitive on
that component.  Consequently `F` is a disjoint union of isomorphic connected
cubic vertex-transitive graphs.  Their common order divides 80.

Filtering the complete Potočnik--Spiga--Verret census of connected cubic
vertex-transitive graphs gives the following candidates.  An ordinal means
the one-based position among census entries of that order.

| component order | copies | all census entries | girth-at-least-5 ordinals |
|---:|---:|---:|:---|
| 4 | 20 | 1 | none |
| 8 | 10 | 2 | none |
| 10 | 8 | 3 | 3 |
| 16 | 5 | 4 | 4 |
| 20 | 4 | 7 | 4, 6, 7 |
| 40 | 2 | 12 | 3, 4, 5, 6, 7, 8, 11 |
| 80 | 1 | 33 | 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 28, 29, 30, 32, 33 |

Thus the local and transitivity constraints reduce the shadow to exactly 37
unlabeled types: eight Petersen components; five copies of the unique
surviving order-16 graph; four copies of one of three order-20 graphs; two
copies of one of seven order-40 graphs; or one of 25 connected order-80
graphs.

This is a necessary-condition census, not an existence result.  A survivor
still needs a compatible vertex-transitive symmetric `80_3` linear
configuration whose point graph is edge-disjoint from `F` and whose union
with `F` is C4-free.

## Reproduction

The source is `cubicvt4-300g6.txt` from commit
`68c592d4790ab1737f04d86d3102c4999bbc6c09` of
<https://github.com/kguo-sagecode/cubic-vertextransitive-graphs>.  Its SHA-256
is `4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088`.

With NetworkX installed, run:

```text
python3 q9_cubic_shadow_census.py /path/to/cubicvt4-300g6.txt
```

The verifier checks the source digest, connectedness, cubicity, and the exact
survivor lists.  Its girth calculation is a direct repeated breadth-first
search.

## A first transitive orbit quotient

The smallest surviving shadow type is eight disjoint Petersen graphs.  The
script `q9_petersen_product_orbit_census.py` tests nine natural transitive
product actions on this shadow.  Internally it uses `F20`, `A5`, or `S5` on
the Petersen graph's model as the 2-subsets of five points.  On the eight
components it uses the regular action of `C8`, `C4 x C2`, or `C2^3`.

There are 56,000 possible triples whose points are pairwise at shadow distance
at least three.  The nine group actions reduce these to only 7 or 28 possible
invariant orbit unions of size 80.  None gives a compatible graph: every
union is non-linear, violates the definition of the triangle-free-edge
shadow, or creates a four-cycle.

This rules out those nine product actions, not every transitive subgroup of
the full wreath-product automorphism group of eight Petersen components.
That distinction matters: the census remains a necessary-condition reduction,
not a q=9 nonexistence proof.

## Vertex-transitive configuration candidates

The triangular shadow is the point graph of a symmetric `80_3` linear
configuration.  Its Levi graph is cubic and bipartite on 160 vertices.  A
Levi 6-cycle gives three pairwise-intersecting lines and hence a four-cycle in
the point graph (using the third point on one line); a Levi 8-cycle gives a
four-cycle directly.  Conversely, a point-graph four-cycle lifts to a Levi
6- or 8-cycle.  Thus the point graph is C4-free exactly when the linear
configuration's Levi graph has girth at least 10.

Among the 104 connected cubic vertex-transitive graphs of order 160 in the
PSV census, 94 are bipartite and exactly 17 have girth at least 10.  Their
one-based order-160 ordinals are:

```text
41 42 43 44 53 56 62 63 64 66 75 76 80 84 100 101 104
```

All 17 have girth exactly 10.  The script
`q9_configuration_levi_census.py` reproduces the filter, constructs an
80-vertex point graph from each bipartition, and checks that it is 6-regular,
C4-free, and has exactly 80 triangles.  Since a connected bipartite
vertex-transitive graph has a part-preserving subgroup transitive on each
side, every resulting point graph is vertex-transitive.

This catalogs the vertex-transitive-Levi subfamily.  A point-transitive
configuration need not have a vertex-transitive Levi graph, so the 17 graphs
are concrete candidates rather than an exhaustive list of all possible
triangular shadows.

### Complete exclusion of the 17-member subfamily

For each of the 17 point graphs `T`, the compatibility graph on pairs which
are neither adjacent nor have a common neighbor in `T` is vertex-transitive
and 49-regular.  Every possible triangle-free-edge shadow `F` is a cubic
subgraph of this compatibility graph.

The verifier `q9_vt_levi_shadow_orbit_exclusion.py` computes `Aut(T)`,
enumerates every transitive subgroup `H`, and then enumerates every union of
eligible unordered-pair `H`-orbits having valency three.  There is only one
transitive subgroup for the fourteen point graphs with automorphism-group
order 80.  Each of the other three point graphs has automorphism-group order
160 and exactly three transitive subgroups (two of order 80 and the full
group).  Depending on the action, only 4 to 182 cubic orbital unions occur.
Every union makes some vertex pair have at least two common neighbors in
`T union F`, so every union contains a four-cycle.

This exhausts the vertex-transitive completion problem for all 17
vertex-transitive-Levi configurations.  Indeed, automorphisms of a candidate
`G` preserve the intrinsic partition into triangular and triangle-free
edges, so `Aut(G)` would be one of the transitive subgroups of `Aut(T)` and
`F` would be one of the checked orbital unions.  Hence none of the 17
configurations extends to a q=9 candidate.

The script requires NetworkX and pynauty; the recorded run used NetworkX
3.6.1 and pynauty 2.8.8.1.  It independently checks the pinned census digest,
automorphism-group sizes, subgroup-lattice sizes, transitive subgroup orders,
orbital-union counts, and the final common-neighbor obstruction.

## Exhausting connected cubic shadows

The same group-orbit strategy can start from the cubic shadow instead of the
configuration.  For each connected census graph `F`, any vertex-transitive
candidate supplies a transitive subgroup `H <= Aut(F)`.  Its 80 configuration
lines form an `H`-invariant set of triples whose points are pairwise at
`F`-distance at least three.

For 24 of the 25 connected shadow types, `|Aut(F)|` is 80 or 160.  The script
`q9_connected_shadow_orbit_exclusion.py` enumerates every transitive subgroup.
In every action, each allowed triple orbit has size at least 80, so an
invariant set of exactly 80 lines must be one orbit of size 80.  There are
between 31 and 708 such orbits per action.  Every orbit either repeats a point
pair (so is not a linear configuration), gives an `F` edge a common neighbor,
or creates a four-cycle in the union graph.  No orbit survives.

Thus 24 connected cubic-shadow types are completely excluded, including
point-transitive configurations whose Levi graphs need not be
vertex-transitive.  The sole remaining connected type is order-80 census
ordinal 30, the unique girth-10 survivor, whose automorphism group has order
960.  Its larger subgroup lattice is handled separately rather than hidden
inside the small-group sweep.

### The final connected type

For ordinal 30, `q9_f30_transitive_subgroups.g` asks GAP for the conjugacy
classes of subgroups of the order-960 automorphism group.  GAP finds 132
subgroup classes, of which exactly five are transitive.  Their representative
orders and numbers of conjugates are `(160,6)`, `(240,2)`, `(480,1)`,
`(480,1)`, and `(960,1)`, accounting for all eleven transitive subgroups.

The companion `q9_f30_shadow_orbit_exclusion.py` independently checks that
the emitted generators act as automorphisms of the pinned census graph,
generate groups of the stated orders, and act transitively.  Their allowed
triple orbits again have no size below 80.  The five representatives have
respectively 30, 9, 3, 3, and 1 possible 80-line orbits.  Every one is
non-linear, violates the triangle-free-edge definition, or creates a C4.
Conjugation preserves these properties, so all eleven transitive subgroups
are excluded.

Consequently **all 25 connected cubic-shadow types are impossible** for a
vertex-transitive q=9 candidate.  Any remaining candidate must have a
disconnected shadow: equal copies of the surviving order-10, 16, 20, or 40
component types.

## Disconnected order-40 pairs

For component ordinals 4, 5, 6, and 7, the shadow is two isomorphic
order-40 components and its full wreath-product automorphism group has order
3200.  The live GAP-to-Python verifier
`q9_order40_pair_shadow_exclusion.py` computes 695 subgroup conjugacy classes
and 34 transitive classes for each type (273 actual transitive subgroups after
expanding conjugacy classes).

Again, every allowed triple orbit has size at least 80, so each invariant
80-line configuration must be one orbit.  Depending on the component type,
there are 8,524 or 8,558 representative line orbits across the 34 transitive
classes.  Every orbit is non-linear or creates a C4; none survives.  This
completely eliminates four of the seven order-40-pair shadow types.

The three higher-symmetry order-40 component types—ordinals 3, 8, and 11—have
doubled-shadow automorphism groups of orders 12,800, 12,800, and 460,800,
respectively, and remain separate classification leaves.

The companion `q9_order40_pair_highsymmetry_exclusion.py` closes ordinals 3
and 8.  Each order-12,800 automorphism group has 23,183 subgroup conjugacy
classes.  GAP finds 468 transitive classes (4,629 actual subgroups) for
ordinal 3 and 364 transitive classes (3,253 actual subgroups) for ordinal 8.
The verifier checks 58,392 and 33,644 representative line orbits,
respectively.  Every orbit is non-linear, violates the shadow-edge condition,
or creates a C4; there are no witnesses.

Hence **six of the seven order-40-pair types are excluded**.  Only component
ordinal 11, with doubled-shadow automorphism group of order 460,800, remains
in this component-size branch.

For that last type, direct wreath-product subgroup enumeration is too coarse.
Every configuration line has block type `2+1`; incidence balance forces
exactly 40 lines in each orientation.  Therefore the triangular graph induced
inside each order-40 component is a 2-factor.  The component automorphism
group has order 480 and only five transitive subgroup classes.

`q9_order40_ordinal11_internal_sieve.py` enumerates all 21 invariant eligible
2-factors.  Thirteen contain a 4-cycle and are immediately impossible.  The
eight remaining representatives all occur under the regular order-80
projection class and have cycle types `4·C10` (five representatives), `5·C8`
(two), or `8·C5` (one).  This reduces the final order-40 pair leaf to eight
internal cycle patterns and a cross-component 4-regular lift.

The regular subgroup has six conjugates in the order-480 component
automorphism group, so it is self-normalizing.  Consequently every remaining
two-component transitive action is conjugate into the restricted wreath
product `K wr C2`, of order 12,800.  This avoids the intractable full
order-460,800 wreath product without losing a candidate.

`q9_order40_ordinal11_lift_exclusion.py` enumerates all 5,264 subgroup classes
and 75 transitive classes of `K wr C2` (509 actual transitive subgroups), then
checks all 934 representative invariant 80-line orbits.  Every orbit is
non-linear, violates the intrinsic shadow-edge condition, or creates a C4.
There are no witnesses.

Therefore **all seven disconnected order-40-pair shadow types are
impossible**.

## The order-20 four-component shadows

There are three surviving connected order-20 component types, PSV ordinals
4, 6, and 7, with automorphism-group orders 20, 120, and 240.  In a
vertex-transitive candidate, the stabilizer of one component is transitive
on its 20 vertices.

`q9_order20_internal_edge_sieve.py` enumerates every transitive subgroup
class of each component automorphism group and every invariant union of
eligible internal pair orbitals.  It checks both the intrinsic shadow-edge
condition and C4-freeness.  The three types have respectively 1, 2, and 9
surviving subgroup cases, and in every case the unique surviving internal
triangular graph is empty.  All 505 shadow-violating and 235 C4-creating
nonempty unions are rejected.

Thus every configuration line meets three distinct components.  There are
only four block triples.  Each 20-point component has 60 line incidences,
while there are 80 lines in total, so the triple omitting any fixed block has
weight `80 - 60 = 20`.  The block quotient is therefore unique, with weights
`(20,20,20,20)`; every pair of components supports 40 triangular edges.
This is an exact quotient reduction, not yet an exclusion of its lifts.

## The order-16 five-component shadow

The unique surviving order-16 component type has automorphism group of order
96.  In a vertex-transitive candidate, each component stabilizer is
transitive on its 16 vertices, so the triangular graph induced inside a
component is invariant under one of the eight transitive subgroup classes.

`q9_order16_internal_edge_sieve.py` enumerates every union of eligible
internal pair orbitals for all eight classes.  Every nonempty union either
creates a C4 together with the cubic component or gives a shadow edge a
common neighbor.  The empty union is the unique survivor in every class.

Consequently the triangular graph has **no edge within a shadow component**,
and every one of the 80 configuration lines meets three distinct components.
The remaining lift is therefore five-partite, with each 16-point block having
48 line incidences.

`q9_order16_block_quotients.py` next exhausts the five transitive groups of
degree five and every invariant nonnegative integer weighting of the ten
block triples.  For the cyclic and dihedral actions the triples form two
orbits of size five, with weights `(a, 16-a)` for `0 <= a <= 16`: 17
patterns for each action.  For each of the Frobenius group of order 20,
`A5`, and `S5`, the ten triples form one orbit and its unique weight is 8.
Thus exactly 37 action-pattern pairs survive the block quotient.  Their
pair-codegrees are 16 through 32 on the two pair orbitals in complementary
amounts for the cyclic/dihedral cases, and uniformly 24 in the remaining
three cases.  These are necessary quotient data; they do not yet exclude
the order-16 lift.

There is a further integral lift condition already at block level.  The
stabilizer of one component is transitive on its 16 points, so the total
number of incident lines in each of its orbits on block triples must be a
multiple of 16.  For `C5` the six incident triples are fixed individually;
for `D10` their orbit sizes are `2,2,1,1`.  In both cases only the endpoint
weights `(0,16)` and `(16,0)` remain.  The unique uniform pattern remains for
each of `F20`, `A5`, and `S5`.  Hence only **seven** action-pattern pairs can
lift: two each for `C5` and `D10`, and one for each of the other three groups.

The four cyclic/dihedral endpoint pairs do not lift.
`q9_order16_endpoint_lift_sat.py` uses a preimage of the block 5-cycle.
After independent changes of coordinates on the five component copies, that
lift is a cyclic block shift with one closing twist `alpha` in `Aut(C)`.
The component automorphism group has 13 conjugacy classes, all enumerated by
the verifier.  The identity twist is split losslessly into its 56 diagonal
seed-line orbits; the other twelve twist classes are checked as single
centralizer-invariant formulas, for 68 UNSAT branches in total.  Each formula
enforces all 80 line incidences, linearity, zero common neighbors on every
shadow edge, and the global at-most-one-common-neighbor condition equivalent
to C4-freeness.  Therefore only the three uniform quotient cases with block
actions `F20`, `A5`, and `S5` remain.

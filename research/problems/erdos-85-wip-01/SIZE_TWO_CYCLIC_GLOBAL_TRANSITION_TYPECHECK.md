# Global transition construction: GT0 typecheck

Date: 2026-08-24

Scope: `BinarySizeTwoCyclicPackingBound`; adversarial audit of the proposed
extended Cohn--Lempel interface

## Verdict

The extended Cohn--Lempel theorem is a valid consumer for a fixed 4-regular
graph and a circuit partition obtained by choosing one of three transitions
at every vertex.  The current routing construction has not yet produced
those two layers with the advertised interpretation.  It presently mixes:

1. pairing four boundary incidences of one routing **block**, which completes
   missing graph edges; and
2. pairing four half-edges at one reciprocal-dart **central vertex**, which
   is a circuit-partition transition on a fixed graph.

These are different operations on different index sets.  The audit exposed
a real gap in the first construction, but the squad supplied a clean repair:
**promote every block boundary to a new 4-valent hub vertex**.  The hub graph
is fixed, and the three block-boundary pairings are exactly the three
transitions at that hub.  At every reciprocal-dart central vertex, use the
fixed shore-preserving reciprocity transition `R_A--R_B | C_A--C_B`.

Thus GT0 is repairable and GT1 may proceed on the hub graph.  The distinction
below remains load-bearing: without the hubs, changing a block completion
changes graph edges and cannot be represented by an interlacement-matrix
state change.

There is a second GT0 condition at the reduced-code interface.  Loopless is
not assumed in `SizeTwoCyclicPackingExclusion`.  A self-reciprocal diagonal
route has only one endpoint view and hence gives a degree-two, not degree-four,
central object.  The q=8 relaxed controls contain many such routes.  The hub
graph is therefore 4-regular only after a loop-inflation gadget is supplied,
or after looplessness is derived from the capped hypotheses.

## Incidence bookkeeping

Fix `q=2m`.  A reciprocal pair of routing darts is a central object `e`.
It has four incidences:

```text
(endpoint block 0, row), (endpoint block 0, column),
(endpoint block 1, row), (endpoint block 1, column).
```

Within a block, every nonboundary folded coordinate node has degree two.
Suppressing it joins two central objects by an edge.  A boundary coordinate
node has degree one; suppressing it leaves a dangling half-edge.  Pairing the
four dangling half-edges of that block joins their central objects in pairs.
It therefore supplies the missing **edges** of a 4-regular multigraph on the
central objects.

After this edge completion, the three Cohn--Lempel transitions at a central
vertex are instead the three perfect matchings of the four incidences listed
above.  Changing such a matching does not change the graph.  In particular,
the three possible completions of a block's boundary incidences are not the
three transition states of a central vertex: the four boundary incidences
generally belong to four different central objects.

This does not refute the whole transition-system route.  It refutes the
specific sentence that block-local boundary pairing automatically becomes a
central-vertex state.

## Choice dependence of the present graph

The internal degree-two coordinate nodes give canonical graph edges, but the
four boundary half-edges in each block still require one of three pairings.
Different pairings generally connect different pairs of central vertices,
so they produce different 4-regular multigraphs.  Extended Cohn--Lempel may
be applied separately to each completed graph, but its interlacement matrix
does not turn those graph-edge changes into the delete/keep/diagonal-flip
operations for transitions of one fixed graph.

Consequently a q=8 program that varies block completions and compares the
resulting interlacement matrices would not test GT1 as stated.  It would mix
changes of the underlying graph with changes of the circuit partition.

## Three possible repairs

### Repair 0 (adopted): promote boundaries to hubs

Do not pair the four dangling boundary incidences directly.  Add one new
4-valent hub vertex `h_(x,t)` per routing block and attach the four dangling
incidences to its four half-edges.  Suppress only the degree-two coordinate
nodes.  This produces a fixed 4-regular multigraph with two vertex types:

```text
central vertices: reciprocal dart pairs;
hub vertices:     routing blocks.
```

At a central vertex with endpoint views `A,B`, fix the canonical
shore-preserving reversal transition

```text
R_A--R_B | C_A--C_B.
```

At a hub vertex, the three perfect matchings of its four half-edges are
precisely the three block-boundary completions.  Circuit partitions vary the
hub transitions while leaving the graph fixed, so Traldi's
delete/keep/diagonal-flip operations are now well typed.

This repair also gives the first concrete GT1 candidate.  Two m-separated
lifts sharing a neighbor create parallel row and column transition edges (a
digon) after reversal at the target block.  The same-difference cap should be
translated as forbidding two such shared-neighbor digons for one lifted
source pair.  That translation is not yet proved, but it is now a statement
about transitions of one fixed graph.

### Loop inflation required by the reduced code

The description above is literally 4-regular for non-diagonal reciprocal
dart pairs.  If a route is diagonal, reversal fixes it.  The symmetric
relation and the exact row/column laws count that route once, so its central
object has only its row and column incidences.  Duplicating the endpoint view
would alter those exact degrees and is not valid.

This occurs throughout the executable controls.  Using the exact permutation
CNF at `q=8,a=1`, with `cross_mode=same-t` and `loopless=False`, one returned
model for each cap set has:

```text
cap {0}:    22 diagonal routes
cap {2}:    24 diagonal routes
cap {4}:    20 diagonal routes
cap {0,2}:  32 diagonal routes
cap {0,4}:   8 diagonal routes
cap {2,4}:  16 diagonal routes
cap {0,2,4}: UNSAT
```

Thus deleting Loopless is not a harmless relaxation for the transition
construction; every displayed SAT comparator has 2-valent central objects.

A canonical candidate repair is to attach one artificial graph loop to each
2-valent central object.  A graph loop contributes two incidences, restoring
degree four.  Fix the transition there as

```text
real row -- real column | dummy loop half -- dummy loop half.
```

This contributes one distinguished one-edge circuit per diagonal route.
Traldi's primary text supports the gadget: the directed formulation explicitly
permits loops and multiple edges, discusses the half-edge convention at looped
vertices, and Theorem 4 applies to arbitrary undirected 4-regular graphs.
Consequently the dummy circuits are already included in the exact equality;
a calibrated routing statistic may subtract their known number from
`|P|`.  GT0 therefore has a well-typed repair for the actual reduced target,
subject to the elementary incidence assertions in the stop rule below.

### Repair A: central transitions, arbitrary fixed edge completion

Choose one boundary completion in every block once and for all, producing a
fixed 4-regular graph on reciprocal-dart central vertices.  Then identify a
routing meaning for the three matchings at each central vertex.  There is a
natural distinguished matching that pairs row and column incidences within
each endpoint view.  The other two cross the endpoint views.  A valid GT1
could say that the common-neighbour cap forbids one pattern of these
**central** transitions.  The block-local half-quotient pairing would no
longer itself be the transition state, and one must prove that the chosen
boundary completion does not affect the proposed forbidden pattern.

### Repair B: blocks as 4-valent vertices

Choose a canonical transition at every central routing-edge object, alternate
it with the degree-two local-coordinate pairings, and suppress the resulting
paths.  If every path ends at a boundary incidence, this produces a fixed
4-regular multigraph whose vertices are routing blocks and whose four
half-edges are their four boundary incidences.  The three block-boundary
pairings are then genuinely the three transitions at a vertex.

This repair needs two proofs before use:

- reciprocity and the row/column shore labels determine the central
  transition without an arbitrary choice; and
- the alternating paths have no closed component that loses all boundary
  information (or such components are accounted for separately).

## Bounded stop rule

Before enumerating transition minors, implement only the incidence maps on
one q=8 SAT control and assert:

```text
each completed graph edge has two ends;
each proposed graph vertex has degree four;
the three varied objects are matchings at one vertex, not graph edges;
the underlying edge multiset is identical across the three states.
```

With the adopted hub repair, also assert that the number of hubs equals the
number of routing blocks and that varying a hub transition leaves the graph's
edge multiset unchanged.  If the latter assertion fails, Cohn--Lempel does
not compare the states through one interlacement matrix and this formulation
stops.  If Repair B is used instead, assert that every alternating component
has exactly two boundary ends.  Only after these checks pass is GT1 a
well-typed bounded target.

For the reduced code, additionally assert that every central object is either
4-valent or a diagonal 2-valent object equipped with exactly one dummy loop,
and subtract the number of dummy circuits in the Cohn--Lempel calibration.

Primary source for the loop convention: Lorenzo Traldi, *Binary nullity,
Euler circuits and interlace polynomials*, arXiv:0903.4405, discussion before
Corollary 2 and the half-edge note immediately before Theorem 4.

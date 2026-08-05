# Erdős 85 polarity conic and even-core checkpoint — 2026-08-04

## Status

Eventual monotonicity remains open.  This session substantially extended the
finite-field polarity families and identified an exact obstruction to the
most natural one-vertex extension of a new regular witness.

All results below compile with pinned Lean 4.31 and have the standard axiom
inventory `[propext, Classical.choice, Quot.sound]`.

## Odd characteristic

The absolute locus was parametrized explicitly.  Starting from an absolute
vector `a` and a transverse vector `b`, put `w = a × b` and

```text
x(t) = b + t w
       - (b·b + t²(w·w)) / (2(a·b)) a.
```

The map `Option K → absolutePoints K` sending `none` to `[a]` and `some t`
to `[x(t)]` is bijective.  Consequently the absolute conic has exactly
`q + 1` points.  The odd two-secant theorem then gives, for every
`k ≤ q + 1`,

```text
q ≤ f(q² + q + 1 - k) ≤ q + 1.
```

The main implementation is `Erdos85PolarityConic.lean`.

## Characteristic two

For `n = [1,1,1]`, the identity

```text
x·x = 0  ↔  n·x = 0
```

shows that the absolute locus is the polar line of the nonabsolute nucleus
`[n]`.  This proves the same exact cardinality `q + 1` in characteristic two,
and hence over every finite field.

Deleting the absolute line and its nucleus leaves a `C₄`-free graph on
`q² - 1` vertices.  Every survivor loses exactly one neighbor, so this core is
exactly `q`-regular.  The counting upper bound matches the witness:

```text
f(q² - 1) = q + 1.
```

It follows that the immediately preceding step is monotone:

```text
f(q² - 2) ≤ f(q² - 1).
```

## Exact attachment obstruction

For the characteristic-two regular core, every
common-neighbor-independent attachment set has cardinality at most `q - 1`.
The bound is sharp: the surviving points on the polar line of any absolute
point form such a set.  Equivalently,

```text
indepNum (commonNeighborConflict evenCore) = q - 1.
```

Thus the standard one-new-vertex attachment cannot extend this `q`-regular
core while preserving minimum degree `q`; it is exactly one selector vertex
short.  This is an obstruction for this witness and this extension mechanism,
not a counterexample to monotonicity at `q² - 1 → q²`.

The characteristic-two development is in `Erdos85PolarityEven.lean`.

## Next directions

1. Investigate compensated or multi-vertex extensions of the even core that
   bypass its exact selector obstruction.
2. Determine whether the odd deletion band can be sharpened from the
   two-valued interval `{q,q+1}` at additional orders.
3. Use the exact conflict graph geometry of the even core to classify near-safe
   sets and possible edge-switching repairs.

## Later continuation: odd secant defects

The odd-characteristic full-conic deletion is now understood at the defect
level.  Its degree-`q-1` vertices are in bijection with unordered pairs of
absolute points, hence their number is exactly

```text
choose (q + 1) 2.
```

A reusable selector-counting theorem was also proved: if `S` is
common-neighbor-independent in a finite graph, then

```text
∑ x ∈ S, degree(x) ≤ number of vertices.
```

In particular, `|S| d ≤ n` whenever the minimum degree is at least `d`.
Applying this to the `q²`-vertex deleted-conic core shows that no safe selector
can contain all `choose (q+1) 2` degree defects.  Therefore the standard
one-new-vertex attachment cannot repair this core at degree `q`.  As with the
even-core obstruction, this rules out a natural witness-extension mechanism,
not monotonicity itself.

## Full odd-core degree distribution

A double count gives exactly `q(q+1)` incidences between projective points and
the absolute conic.  The `choose(q+1,2)` classified secant poles, with two
incidences each, already exhaust this total.  Consequently no nonabsolute
point is incident with exactly one absolute point.  The deleted-conic core is
therefore exactly biregular:

```text
choose(q+1,2) vertices have degree q-1,
q² - choose(q+1,2) vertices have degree q+1.
```

The checked statements are `sum_absoluteIncidences`,
`absoluteIncidences_ne_one`, `oddCore_degree_eq_low_or_high`, and
`card_oddCoreHighVertices` in `Erdos85PolarityOddSecantCount.lean`.

## Kneser structure of the odd defects

The absolute-neighbor pair of each low-degree vertex determines it uniquely.
If two such pairs are disjoint, the two poles have a nonabsolute common
neighbor and therefore conflict inside the core.  Thus every safe family of
low-degree defects maps to an intersecting family of two-subsets of the
`q+1` absolute points.  The checked Erdős--Ko--Rado bridge yields

```text
|safe defect family| ≤ q.
```

This is formalized as `safe_lowVertices_card_le`; the general finite-type EKR
transport is `pair_intersecting_card_le` in
`Erdos85IntersectingPairs.lean`.

The bound is sharp.  Fixing one absolute point `a`, the poles of the `q`
absolute pairs `{a,b}` form `oddCoreDefectStar`.  Any two share `a` as a
common neighbor in the full polarity graph, and uniqueness of line
intersection shows that they have no common neighbor after the conic is
deleted.  The checked theorems are

```text
card_oddCoreDefectStar = q,
oddCoreDefectStar_subset_low,
oddCoreDefectStar_safe,
exists_safe_lowVertices_card_eq.
```

Hence the largest safe family contained in the odd defect locus has exact
cardinality `q`.

Covering all `q(q+1)/2` defects by independently safe selectors therefore
requires a linearly growing number of selectors.  The division-free checked
bound is

```text
q + 1 ≤ 2 · number_of_selectors.
```

This is `two_mul_numSelectors_ge_card_add_one`.  In particular, no bounded
number of direct safe attachments repairs the full deleted-conic odd core
uniformly in `q`.

The underlying rank-two combinatorics has also been sharpened independently.
Every intersecting family of pairs is either a star or has at most three
members, and a family of intersecting pair-families covering every pair of an
`n`-element set has at least `n-2` members.  These checked statements are
`pair_intersecting_star_or_card_le_three` and
`pair_intersecting_cover_card_ge`; transporting the latter through the defect
bijection gives the checked geometric bound

```text
q - 1 ≤ number_of_selectors.
```

This is `numSelectors_ge_card_sub_one`.  It improves the earlier elementary
counting bound `q+1 ≤ 2·number_of_selectors` and shows that direct safe repair
of the odd core needs essentially one new vertex per field element.

The lower bound is exact.  Choose three absolute points, use the three pair
poles among them as one triangle selector, and use a full defect star for
every remaining absolute point.  These `q-1` selectors are independently
safe and cover every defect.  The generic optimal pair cover is implemented
by `PairCoverIndex` and `pairCoverFamily`; its geometric transport is
`exists_optimal_safe_lowVertex_cover`.

This exact cover result does **not** itself attach all `q-1` vertices: a
simultaneous extension must additionally control common neighbors and edges
involving different new vertices.  It precisely identifies the scale and
shape of any direct multi-selector repair.

## Two-point core and compensated switch

A new operation `crossEdgeSwitch H x w` deletes every edge between `N(x)`
and `N(w)` and then inserts `xw`.  The checked theorem
`crossEdgeSwitch_not_containsC4` proves this preserves `C₄`-freeness for every
finite `C₄`-free graph.  The degree lemmas show that the new edge raises the
degree of `x` by exactly one and give a completion theorem whenever the cross
deletion leaves `x` as the unique one-unit defect.

For distinct absolute points `a,b`, `twoPointCore` deletes `{a,b}`.  Their
unique nonabsolute common neighbor `x` has degree `q-1`, and the checked
theorem `eq_twoPointDefect_of_degree_eq_sub_one` proves it is the only vertex
of that degree.  Thus a successful switch would give a `q`-minimum-degree
graph on `q²+q-1` vertices, hence the new lower bound
`q < minDegreeForC4 (q²+q-1)`.

The remaining coordinate problem is now narrow.  Write isotropic
representatives `A,B`, put `α=A·B ≠ 0`, and choose a representative `X` of
their common neighbor, with `X·A=X·B=0` and `β=X·X ≠ 0`.  In the pencil

```text
W = X + t(B-A),       t ≠ 0,
```

we always have `X·W=β ≠ 0`, so `x,w` are nonadjacent, while `w` is adjacent
to neither deleted point.  A neighbor of `x` has representative
`U=sA+rB` with `s,r≠0`; it is nonabsolute and has no deleted incidence, hence
degree `q+1` in the two-point core.  If `V` is the opposite endpoint of a
deleted cross edge, then in the basis `A,B,X`, after scaling,

```text
V = -(s/r) A + B + t α ((s/r)+1)/β X.
```

Both `V·A` and `V·B` are nonzero.  Its only possible lack of one-unit slack
is therefore absoluteness.  Setting `z=s/r`, the absolute condition reduces
to the quadratic

```text
c(z+1)² - 2z = 0,     c = t² α/β,
```

whose discriminant is `4(1-2c)`.  Consequently it is enough to choose `t`
so that `1-2t²α/β` is a nonsquare (with the small/degenerate cases treated
separately).  This is the exact finite-field character-sum existence lemma
still needed for the candidate `q²+q-1` construction.

### Correction: the nonsquare pencil still has a double-loss vertex

The nonsquare condition does prove that every opposite endpoint is
nonabsolute, and the required finite-field lemma has now been checked.
However, an exact multiplicity audit shows that the sole vertex in
`N(x) ∩ N(w)` loses two cross edges.  It begins at degree `q+1` and falls to
`q-1`, so this pencil moves the defect instead of repairing it.  The earlier
claim that all cross-edge losses were at most one was false.

Exhaustive computations for `q=5,7,11,13` reveal the correct pattern: take
`w` to be any surviving absolute point.  Then `xw` is absent, the cross edges
form a matching of size `q-2`, and the switched graph has minimum degree `q`.
The geometric reason is tangency.  If `w` is absolute and `z~w`, the polar
lines of `z` and `w` intersect at `w`; because the simple graph omits the loop
at `w`, `z` and `w` have no graph-theoretic common neighbor.  This removes one
of the two possible losses at the unique vertex in `N(x)∩N(w)`.

The revised formal target is therefore:

1. prove adjacent vertices `z,w` with `w` absolute have no common neighbor;
2. deduce cross-edge loss at most one for `N(x),N(w)` when `xw` is absent;
3. show every positive-loss endpoint other than the absolute `w` has original
   two-point-core degree `q+1`;
4. apply the checked unique-defect switch witness theorem.

All four steps are now checked.  The tangent right endpoint makes every
cross-edge loss at most one; every vertex of positive loss has two-point-core
degree exactly `q+1`; the unique pole retains degree `q-1` through deletion
and gains the new switch edge.  Therefore, for every finite field `K` with
`(2 : K) ≠ 0`, the development now proves

```text
C4FreeMinDegreeWitness (q²+q-1) q,
minDegreeForC4 (q²+q-1) = q+1.
```

The checked headline theorem is `minDegreeForC4_odd_twoPoint_order` in
`Erdos85PolarityTangentSwitch.lean`.  This extends the known consecutive
polarity values at `q²+q` and `q²+q+1` to a run of three exact orders in odd
characteristic.

## Why the same surgery stops at three deleted absolute points

The general checked theorem `crossEdgeSwitch_degree_le_of_ne_endpoints` says
that a cross-edge switch cannot increase the degree of any old vertex other
than its two endpoints.  Consequently
`crossEdgeSwitch_minDegree_lt_of_three_low_vertices` proves that one switch
cannot reach target degree `d` when the old graph has three distinct vertices
of degree below `d`.

After deleting three distinct absolute points, every deleted pair still has
its nonabsolute pair pole at degree `q-1`: the third absolute point is not
adjacent to that pole by the odd two-secant theorem.  This core is introduced
as `threePointCore`, with the checked per-pair degree theorem
`threePointPairDefect_degree`.  Thus extending the new plateau one step
further requires a genuinely multi-endpoint or multi-switch construction;
choosing a more clever single tangent endpoint cannot suffice.

## Finite switch programs and the cumulative endpoint obstruction

The universal surgery can be iterated.  `crossEdgeSwitchProgram` folds a list
of endpoint pairs through the current graph, recomputing the two neighborhoods
at every stage.  Since each individual switch preserves `C₄`-freeness with no
extra hypothesis, `crossEdgeSwitchProgram_not_containsC4` proves the entire
finite program is `C₄`-free.

This does not remove the degree obstruction.  The checked theorem
`crossEdgeSwitchProgram_degree_le_of_not_mem_endpoints` says that a vertex
which never occurs as either endpoint has final degree at most its initial
degree.  Therefore every initial sub-target vertex must be named by a
successful program.  The endpoint set has cardinality at most twice the
program length, giving

```text
number of initial sub-target vertices ≤ 2 · number of switches.
```

Thus the three pair-pole defects force at least two switches.  Computation for
`q=5,7,11` indicates that merely touching all three poles is far from enough:
a static simultaneous two-edge path surgery on the poles stays `C₄`-free and
repairs the original poles, but creates `q-2` new degree-`q-1` vertices.  (This
is not the dynamically recomputed sequential program above.)  This identifies
cumulative loss, not cycle creation, as the next decisive bottleneck.

The first general cascade theorem is now checked.  Away from the two inserted
edge endpoints, a switch has exactly the degree left after cross deletion.  If
a vertex begins that stage with degree exactly `d` and has positive cross-edge
loss, it ends the stage below `d`.  Therefore
`positive_loss_forces_later_switch_endpoint` proves that any continuation
which finally restores minimum degree `d` must name this newly damaged vertex
as a later endpoint.  A successful finite repair program must consequently be
closed under all target-tight vertices hit by its evolving cross deletions.

There is also a checked tight-vertex inventory independent of any switch.
Exactly `q-2` absolute points survive deletion of three distinct absolute
points, and every surviving absolute retains degree exactly `q` because
distinct absolute points are nonadjacent.  The theorem
`exists_tight_absolute_set_threePointCore` packages these as a canonical
`q-2`-element set of tight vertices.  These are not the `q-2` new defects seen
in the static pole-path experiment: every pair pole is nonadjacent to every
third absolute point, so surviving absolutes lie in none of the pole
neighborhoods and incur no such cross-edge loss.  The spawned defects belong
to a different tight incidence class that still needs classification.

A finer computation corrects the last sentence: the spawned vertices are not
initially tight.  They are precisely `q-2` clean neighbors of the center pair
pole, each initially of degree `q+1`; the two arms of the static path delete
two incident edges at each, dropping them directly to `q-1`.  This prompted
the stronger checked theorem `excess_loss_forces_later_switch_endpoint`: a
vertex must become a later endpoint whenever its cross-edge loss exceeds its
available slack above the target.  The earlier tight/positive-loss theorem is
the zero-slack special case.  What remains is to formalize the projective-plane
incidence statement producing those `q-2` clean center-neighbors and their two
distinct losses.

The clean family and its cardinality are now formalized.  For the center pole
of the pair `{a,b}`, remove the three deleted absolute points from its
neighborhood and then remove all neighbors of `c`.  The resulting finset
`pairPoleCleanCenterNeighbors` has exactly `q-2` members.  Every member is
nonabsolute and adjacent to none of `a,b,c`, so
`threePointCore_degree_of_mem_pairPoleCleanCenterNeighbors` proves its core
degree is exactly `q+1`.  The unique excluded surviving center neighbor is the
unique common neighbor of the pair pole and `c`.  The remaining task for the
static-path obstruction is now only to show that each clean member has one
distinct deleted cross edge toward each outer pole neighborhood.

The first arm is checked: `cleanCenter_commonNeighbors_outerAC_card_one`
proves that every clean center neighbor has exactly one common neighbor in the
three-point core with the outer pole of `{a,c}`.  Equivalently, exactly one
incident edge is selected by that arm's cross deletion.  The proof uses the
unique intersection of two projective lines and verifies that the intersection
point is none of the three deleted absolutes.  The `{b,c}` arm and distinctness
of the two selected edges remain to be mirrored.

Both arms are now checked, as is their distinctness.  The outer pair poles
have only `c` as a common neighbor in the full polarity graph, so their
neighborhoods are disjoint in the three-point core.  Hence every clean center
neighbor supports two distinct incident cross edges, one selected by each
arm.

The simultaneous operation is formalized as `twoArmPathSwitch`.  Its generic
degree theorem says that deleting two distinct incident selected edges lowers
the degree by at least two away from the three path endpoints.  Specializing
to the pair-pole path gives

```text
degree after the path switch ≤ q-1
```

for every member of the `q-2` clean family.  Thus the computational defect
propagation is now a theorem: the static path repairs the three original pair
poles only by creating a growing family of at least `q-2` new sub-target
vertices.  (A separate `C₄`-freeness theorem for this static operation is not
needed for the obstruction, though the finite computations show it in the
tested fields.)

Finally, `threePairPolePathSwitch_minDegree_le_sub_one` packages the nonempty
clean family into the global conclusion that the simultaneous path graph has
minimum degree at most `q-1`.  Thus this repair is now formally excluded as a
degree-`q` witness on `q²+q-2` vertices.

## Dynamic first switch: a new unique-defect core

The dynamic operation behaves much better at its first stage.  For
`q=5,7,11`, switching any two of the three pair poles deletes `q-2` cross
edges, repairs those two degree-`q-1` endpoints, creates no new sub-target
vertex, and leaves exactly the third pair pole at degree `q-1`.  Exhaustively
trying every possible partner for a second universal switch produced no
degree-`q` graph in those fields, but the first stage is a canonical reduction
from three defects to one and deserves a structural proof.  The next formal
target is to show that the shared-absolute pair poles are nonadjacent with
disjoint core neighborhoods and that every positive-loss vertex has the one
unit of required slack.

That target is now complete.  The three degree-`q-1` vertices are classified
exactly as the three pair poles.  Two pair poles sharing an absolute endpoint
are nonadjacent and have disjoint neighborhoods after that absolute point is
deleted.  Every vertex of positive cross-edge loss in their first switch is
proved to have old degree exactly `q+1`, while every loss is at most one.
The switched endpoints rise from `q-1` to `q`, and the third pole belongs to
neither deletion neighborhood and stays at `q-1`.  The checked theorem
`firstPairPoleSwitch_unique_defect` therefore proves that the dynamic first
switch leaves the third pair pole as the unique sub-`q` vertex.

## Tight-set obstruction to the second switch

The first switch preserves every surviving absolute point at degree exactly
`q`; this is checked by
`firstPairPoleSwitch_degree_surviving_absolute`.  Hence the intermediate
graph contains the explicit tight set of all `q-2` surviving absolutes in
addition to its unique defect.

The generic final-switch lemma
`crossEdgeLoss_eq_zero_of_tight_of_successful_crossEdgeSwitch` says that a
successful universal switch cannot delete any incident cross edge at a tight
vertex unless that vertex is one of the two new endpoints.  Its polarity
specialization `secondPairPoleSwitch_avoids_surviving_absolute` now proves:
if a second switch centered at the remaining pair-pole defect raises the
minimum degree to `q`, then every surviving absolute other than the chosen
partner has cross-edge loss zero.  Thus any one-switch completion must choose
a partner whose cross-deletion simultaneously avoids `q-3` (or `q-2` when
the partner is nonabsolute) specified tight vertices.  The finite searches
for `q=5,7,11` show that no partner satisfies this condition; the remaining
geometric target is to prove that impossibility uniformly from polarity
incidence.

Two further generic endpoint constraints are now checked.  A switch proposed
at an already adjacent pair is a subgraph of the old graph, since its inserted
edge was already present; a switch with equal endpoints is likewise a
subgraph.  Consequently `successful_crossEdgeSwitch_not_adjacent_at_defect`
and `successful_crossEdgeSwitch_ne_at_defect` show that repairing a strict
defect requires a distinct nonneighbor.  Applied to the second polarity
stage, only distinct nonneighbors of the remaining pair pole can be candidate
partners.  Computation over these reduced candidate sets still finds, for
every partner at `q=5,7,11`, at least one nonendpoint degree-`q` vertex with
positive cross-edge loss.  Proving that last incidence assertion uniformly
would rule out the entire two-switch repair scheme.

The defect endpoint has no loss budget either.  The generic theorem
`crossEdgeLoss_eq_zero_at_repaired_one_defect` observes that a vertex starting
at degree `q-1` must spend the entire one-unit gain from the inserted edge to
reach `q`; consequently its incident cross-edge loss is exactly zero.
`successful_crossEdgeSwitch_one_defect_constraints` bundles the three local
requirements on any proposed completion: the partner is distinct, the old
pair is nonadjacent, and the defect endpoint has zero loss.  Together with
the tight-set avoidance theorem, this gives a compact certificate that every
hypothetical second-stage partner must satisfy.

## Canonical tight anchor at the remaining defect

There is a distinguished vertex in the remaining pair pole's neighborhood:
the unique common neighbor of that `{b,c}` pole and the third deleted
absolute point `a`.  The new definition `pairPoleThirdAbsoluteAnchor`
packages this projective-line intersection, and `remainingPairPoleAnchor`
places it in the three-point core.  The checked lemmas prove that this anchor
is nonabsolute, is adjacent among the deleted points only to `a`, and has
three-point-core degree exactly `q`.  It is adjacent to neither endpoint of
the first switch, so it suffers zero first-stage loss and
`firstPairPoleSwitch_degree_remainingPairPoleAnchor` proves that it remains
degree `q` in the intermediate graph.

This identifies a single canonical tight neighbor of the remaining defect.
The finite computations show that every eligible partner off the tangent at
`a`, with a small adjacency subcase, damages this anchor.  Partners on that
tangent are nonabsolute secant points: except for the two old pair poles they
have a second surviving absolute neighbor, which is itself tight and is
damaged by the second cross deletion.  For the two old pair poles, the
previous `q-2` clean-neighbor path obstruction supplies the damaged tight
vertices.  These cases now give a concrete route to the uniform incidence
lemma rather than an undifferentiated search over all projective points.

That route is now formalized almost to its endpoint.  The first switch changes
no edge incident to the canonical anchor.  If a hypothetical successful
partner is different from and nonadjacent to the anchor, tight-set avoidance
also forces their intermediate common-neighbor intersection to be empty.
Projective-line intersection then proves that every point with these three
separation properties must lie on the tangent at `a`.  Thus
`successful_secondSwitch_partner_adj_deletedSharedAbsolute` reduces all
`q²+q-2` possible partners to the `q-1` surviving tangent points other than
the anchor.

The ordinary tangent points are now excluded as well.  In odd characteristic
every nonabsolute point incident with `a` lies on a two-secant of the conic.
Unless it is one of the pair poles `{a,b}` or `{a,c}`, its second absolute
neighbor survives the three deletions.  That absolute point stays degree `q`
after the first switch, while its unique intersection with the remaining
pair pole produces a positive second-stage cross loss.  This contradicts
tight-set avoidance.  The checked theorem
`successful_secondSwitch_partner_eq_firstPairPole_or_outerAC` therefore says
that a successful partner would have to be exactly one of the two endpoints
of the first switch.  Only those two symmetric endpoint cases remain; the
existing clean-neighbor path family is designed to eliminate them.

## Uniform exclusion of every second universal switch

The endpoint cases are now complete.  For partner `{a,b}`, the original
`q-2` clean center-neighbors have degree `q+1` in the three-point core, lose
exactly one edge in the first `{a,b}`--`{a,c}` switch, and hence are tight of
degree `q` in the intermediate graph.  Their distinct `{b,c}`-arm edge
survives stage one and is deleted at stage two, contradicting the tight loss
budget.  A mirrored family `outerACCleanCenterNeighbors`, also of cardinality
`q-2`, gives the same contradiction for partner `{a,c}`.

Combining these endpoint obstructions with the tangent/secant classification
gives the checked theorem `no_successful_secondPairPoleSwitch`: for every odd
finite field and every possible partner `w`, after the canonical first switch
there is no second universal cross-edge switch centered at the remaining
pair-pole defect whose final graph has degree at least `q` everywhere.  This
upgrades the exhaustive `q=5,7,11` computation to a uniform theorem.

This is an obstruction to the entire two-stage *universal cross-edge switch*
repair scheme, not a proof that no degree-`q` graph exists on `q²+q-2`
vertices and not a solution of eventual monotonicity.  Any successful
polarity repair at this order must now use a non-universal deletion pattern,
more than one further stage, or a different initial surgery.

The obstruction has also been propagated into arbitrary longer switch
programs.  `exists_lowDegree_after_secondPairPoleSwitch` extracts an actual
sub-`q` vertex after every possible second switch.  Since a vertex untouched
by later switch endpoints can only lose degree,
`exists_forced_endpoint_after_secondPairPoleSwitch` proves that any later
program which eventually recovers degree `q` everywhere must explicitly name
one of those second-stage defects as a subsequent endpoint.  Thus a longer
universal-switch cascade cannot bypass the failure; it must chase the defect
created at stage two.

## Exactness of the broader connected-pair surgery

The paired attachment framework has been strengthened from a sufficient
criterion to an exact one.  The new converse
`pairedAttachmentCompatible_of_not_containsC4` proves that if attaching a
connected pair along old-neighbor sets `S,T` is `C₄`-free, then `S` and `T`
must each be common-neighbor independent, their intersection must have size
at most one, and there can be no old edge crossing from `S` to `T`.
`pairedAttachment_not_containsC4_iff` packages the equivalence.

Consequently, a non-universal improvement cannot simply retain selected
cross edges while keeping the same attachment sets: every such edge creates
a four-cycle through the new pair.  A genuinely better extension must change
the attachment architecture itself, distribute compensation across more new
vertices, or alter the old graph and selectors together.

This optimality is now graph-order exact.  If `K ≤ H` is any spanning
subgraph compatible with attaching the pair along the fixed selectors
`S,T`, then `le_deleteCrossEdges_of_pairedAttachmentCompatible` proves

```text
K ≤ deleteCrossEdges H S T.
```

Thus canonical cross deletion is the *largest* compatible spanning subgraph,
and its degree loss is minimal among all repairs using those selectors.  The
companion degree theorem and the selector-wise cross-neighbor inequalities
make the unavoidable loss explicit.  Beating the failed polarity switch
therefore requires changing selectors or using a different multi-vertex
attachment graph, not merely a more selective deletion of the same cross
edges.

## Arbitrary gadget attachments and a new step at order 32

The extension theory now allows an arbitrary finite graph `F` of new
vertices, with a selector `A w` of old neighbors for each gadget vertex.
For the graph `attachGadget G F A`, its common-neighbor sets split into old
and new contributions in three ways:

* old--old: old common neighbors plus gadget selectors containing both;
* new--new: selector overlap plus common neighbors inside `F`;
* old--new: neighbors in the new selector plus adjacent gadget vertices whose
  selectors contain the old vertex.

`attachGadget_not_containsC4_iff_compatible` proves that requiring each of
these three exact sums to be at most one is necessary and sufficient for
`C₄`-freeness.  The degree formulas are also exact: an old vertex gains one
for each selector containing it, while a gadget vertex has degree
`|A w| + deg_F(w)`.  The theorem
`c4FreeMinDegreeWitness_add_of_gadgetCompatible` transports any such
construction to `Fin (n+m)` and packages it as a witness.

This broader architecture produces a positive result that the one- and
two-vertex schemes miss.  At `q=5`, delete four absolute points from the
31-point orthogonal polarity graph and attach a five-cycle.  Each new cycle
vertex uses three old neighbors.  Exhaustive checking of the exact budgets
found a compatible system covering all six degree-four pair poles.  The
resulting graph has 32 vertices, 90 edges, minimum degree five, and at most
one common neighbor for every distinct vertex pair.

The certificate is recorded as the explicit graph `polarityCycle32`, rather
than trusted as search output.  Lean checks its degree and full `32 × 32`
common-neighbor matrix and proves

```text
six_le_minDegreeForC4_thirtytwo : 6 ≤ minDegreeForC4 32
minDegreeForC4_thirtyone_le_thirtytwo :
  minDegreeForC4 31 ≤ minDegreeForC4 32
```

Thus the monotonicity step immediately after the order-five projective plane
is now verified.  This is still not eventual monotonicity: it is one new
finite step and, more importantly, evidence that delete-`k`/attach-`k+1`
cycle gadgets are a viable replacement architecture.  The next structural
question is whether the five-cycle selector pattern has a coordinate
description that generalizes from `q=5` to an infinite family.

### The five-cycle certificate does not scale directly

The exact gadget compatibility constraints were encoded over `GF(7)`.
For all tested four-absolute deletion configurations (including
representatives of all six pairwise-dot-square invariants), five selectors of
the required size `q-2=5` are unsatisfiable.  This computation is exploratory,
not part of the trusted proof.

It exposed a clean proof-level obstruction.  A large safe selector in the
four-deletion core has rank-two labels given by its deleted absolute
neighbours.  Any intersecting rank-two multifamily with at least four indexed
members is a star (singleton labels force this directly, while two-labels use
the checked pair-family star-or-triangle theorem).  Thus every selector of
size at least `q-2` for `q>=7` is routed into the surviving
`q`-point neighbour fibre of one of the four deleted absolutes.

Five selectors force two to use the same fibre.  Their intersection then has
size at least

```text
2(q-2)-q = q-4 >= 3,
```

whereas gadget compatibility permits two distinct selectors to intersect in
at most one old vertex.  Lean now checks both the rank-two star theorem and
this five-selector packing contradiction, together with a gadget-facing
theorem deriving selector size `q-2` from the degree-two five-cycle.
The geometric transport is now also complete.  For nonabsolute survivors,
the deleted-absolute label has size at most two; distinct points in one safe
selector share a deleted label, and equal two-labels force equal projective
points.  Each deleted-label fibre has size at most `q`.  Finally, a safe
selector containing a surviving absolute point has size at most two, so a
selector of required size `q-2 >= 5` is automatically entirely nonabsolute.
The theorem
`fiveCycleAttachment_impossible_of_four_absolute_deletions` therefore gives
an unconditional contradiction for every field of odd characteristic and
order at least seven.  The successful order-32 gadget is formally isolated
as a small-field exception rather than an infinite-family template.

The same argument has now been generalized beyond four points and a
five-cycle.  If `D` is any deleted set of absolute points and `F` is any
two-regular gadget with more vertices than `D`, then compatible selectors
whose new vertices all reach degree `q` are impossible for `q >= 6`.
Thus every delete-`k`/attach-more-than-`k` two-regular repair is excluded at
once; escaping this obstruction requires a denser new gadget, nonabsolute
deletions, edge surgery among survivors, or no net vertex gain.

The degree-two hypothesis can itself be removed.  If the new gadget has
maximum internal degree at most `r >= 2`, then every selector needed to raise
a new vertex to degree `q` has size at least `q-r`.  Pigeonholing more new
vertices than deleted absolute centres into their forced star fibres gives
two selectors with union at most `q`; compatibility gives intersection at
most one.  Hence `2(q-r) <= q+1`, contradicting `q >= 2r+2`.  Lean checks the
generic rank-two packing statement and its full polarity transport as
`boundedDegreeGadgetAttachment_impossible_of_absolute_deletions`.  In
particular, every fixed-bounded-degree, net-positive gadget family fails
eventually.  A scalable repair based only on absolute deletions must therefore
have internal gadget degree growing at least roughly `q/2`, or leave this
attachment model through nonabsolute deletions or survivor-edge surgery.

For the most relevant net-one case `|W|=|D|+1`, the bounded-degree theorem
has a sharp immediate consequence.  Every internal gadget degree is at most
`|D|`, so any successful absolute-deletion repair must satisfy

```text
q <= 2|D|+1,
```

or equivalently `|D| >= (q-1)/2`.  Thus no bounded-size deletion can underlie
an eventual construction, regardless of the attached gadget's shape.  Any
net-one repair remaining inside this polarity model must replace a linear
fraction of the absolute conic and use a correspondingly dense gadget.

The mixed compatibility budget supplies an additional local restriction for
that dense regime: selectors attached to two distinct neighbours of the same
gadget vertex are disjoint.  This is now isolated as
`GadgetAttachmentCompatible.disjoint_selectors_of_adjacent_to`.  In
particular, a high-degree hub forces a large family of pairwise-disjoint
selectors, which can now be combined with the polarity star-fibre description
to attack the remaining hub-heavy gadget shapes.

Both sides of the hub budget are now globally counted.  The selectors of the
neighbours of `w` are pairwise disjoint, giving

```text
sum_{u~w} |A_u| <= |V_old|.
```

On the gadget side, the sets `N_F(u)\{w}` for distinct `u~w` are pairwise
disjoint, giving

```text
sum_{u~w} (deg_F(u)-1) <= |W|-1.
```

When all gadget degrees are at most the target `q`, these combine into the
checked inequality

```text
deg_F(w)(q-1) <= |V_old|+|W|-1.
```

The polarity specialization also records the exact old order
`q^2+q+1-|D|`.  The next strengthening must exploit more than ambient vertex
count: star fibres for distinct deleted absolutes meet in distinct pair poles,
so disjoint hub-neighbour selectors must collectively omit at least one pole
for every pair of their centres.

The cardinal part of that final double count is now formalized independently
of the geometry.  If unordered centre pairs inject into omitted points in one
of their endpoint fibres, and selector `i` omits at most `deficit(i)` points,
then

```text
choose(|I|,2) <= sum_i deficit(i).
```

This is checked as
`choose_two_le_sum_deficit_of_injective_omission_route`.  What remains is to
construct the injection from polarity pair poles: the common neighbour of two
distinct deleted absolutes lies in both star fibres; disjoint selectors omit
it from at least one endpoint, and the rank-two label bound recovers the
unordered centre pair from the omitted point.

## Rigidity of any putative degree-six graph at order 32

The lower bound raises the natural exact-value question `f(32)=6` versus
`f(32)=7`.  The distance-layer machinery now gives a strong reduction of the
second case.  A new asymmetric Moore bound requires only minimum degree:

```text
1 + deg(x) + deg(x)(d-2) ≤ |V|
```

for every `C₄`-free graph of minimum degree at least `d`.  Consequently, a
`C₄`-free graph on 32 vertices with minimum degree six cannot have a vertex of
degree seven: its first two layers would already contain at least 36 vertices.
The checked theorem `degree_eq_six_of_thirtytwo_minDegree_six` therefore
forces exact 6-regularity.

Parity sharpens the local structure.  The graph induced by the six neighbors
of a vertex has maximum degree one.  Exact branch accounting, the 32-vertex
cap, and the handshake parity of that local graph force it to be a perfect
matching.  Thus every edge lies in a unique triangle
(`card_common_eq_one_of_thirtytwo_minDegree_six`), every second layer has
exactly 24 vertices, and precisely one vertex remains outside the first two
layers.  The latter has no adjacency and no common neighbor with the center.
The definitions and theorems `thirtyTwoAntipodes`,
`card_thirtyTwoAntipodes_eq_one`, `mem_thirtyTwoAntipodes_iff`, and
`mem_thirtyTwoAntipodes_comm` show that these unique antipodes symmetrically
pair the 32 vertices into 16 fibers.

Quotienting a hypothetical graph by these fibers yields a 6-regular graph on
16 vertices in which every two distinct quotient vertices have two common
neighbors, i.e. parameters `(16,6,2,2)`.  Edges between fibers form matchings,
and the lift signs must make every quotient four-cycle negative.  A separate
finite calculation shows that this signing system is inconsistent for both
classical `(16,6,2,2)` graphs (the rook and Shrikhande graphs).  That last
classification-and-signing step is not yet formalized, so the development
does **not** yet claim `f(32)=6`; it records the fully checked reduction up to
the antipodal quotient.

The antipodal reduction is now stronger still.  Unique existence defines a
canonical map `thirtyTwoAntipode`; it is checked to be fixed-point free and
involutive.  A general double-counting lemma
`sum_card_common_over_neighbors_comm` expresses symmetry of length-three
walk counts.  In the rigid order-32 graph, all common-neighbor counts equal
one except on the diagonal (six) and at the antipode (zero), so that identity
shows that moving an antipode from one endpoint of an adjacency to the other
preserves adjacency.  Consequently
`thirtyTwoAntipode_adj_iff` proves that the antipode involution is a graph
automorphism.  The 16-fiber quotient is therefore a canonical graph cover;
constructing that quotient and formalizing the final negative-signing
obstruction is the remaining exact-value task.

Equivalently, if `A` is the quotient adjacency matrix and `S` records the
matching choices with signs, then the rigid identities are
`A² = 4I + 2J` and `S² = 6I`, with `|S| = A`.  Thus the last object is a
balanced weighing matrix supported on a symmetric `2-(16,6,2)` design.  This
matrix formulation agrees with the direct negative-four-cycle calculation
and may offer a shorter formal nonexistence certificate than explicit graph
classification.

The canonical quotient has now been constructed in
`Erdos85ThirtyTwoQuotient`.  The equivalence relation is “equal or
antipodal”; every class is checked to contain exactly two vertices, hence the
quotient has cardinality 16.  Quotient adjacency records whether the two
fibers support an edge and is independent of representatives.  The checked
neighbor-image theorem shows the quotient is 6-regular.  Finally, lifting
common neighbors into the two possible orientations proves that every two
distinct quotient vertices have exactly two common neighbors
(`thirtyTwoQuotient_common_eq_two`).  Thus the full `(16,6,2,2)` strongly
regular parameter reduction is formal; only the nonexistence of the required
real signing remains outside Lean.

## Finite signing certificates

The signing obstruction has now been split into a graph-structure part and a
pure parity part.  `Erdos85SignedSRGObstruction` checks two parity certificates
inside Lean.  If the quotient contains a `K₄`, the three distinct four-cycles
on those vertices are all required to be negative; adding the three parity
equations cancels every edge sign and gives a contradiction.  In the
Shrikhande case, an explicit list of eleven endpoint/common-neighbor
quadruples similarly cancels every sign.  Lean verifies both contradictions,
and `noNegativeSigning1622_of_certificateDichotomy` shows that the structural
dichotomy between these two certificates would prove `NoNegativeSigning1622`.

There is also a classification-free computational route.  After relabeling a
chosen vertex as `0` and its six neighbors as `1,...,6`, a neighbor triangle
is the `K₄` case.  In the remaining case the induced 2-regular neighborhood
is a six-cycle, whose cyclic order can be fixed.  Switching signs at vertices
normalizes the zeroth sign row to zero.  The resulting problem is encoded by
two row-major 256-bit matrices.  Degree and common-neighbor constraints are
population counts, while negative common-path parity is the population-one
condition

```text
cpop ((rowA x & rowA y) & (rowS x xor rowS y)) = 1.
```

Lean's verified bit-vector/SAT procedure has checked that the normalized
constraints are inconsistent.  The theorem is
`no_bvNegativeCompact1622_of_normalizedCycle` in
`Erdos85SignedSRGSAT`.  What remains before claiming the exact value is to
formalize the transport from an arbitrary `(16,6,2,2)` signing to the
normalized Boolean matrices (finite relabeling, the local degree-two
dichotomy, and sign switching).  Thus `f(32)=6` is extremely close but is not
yet claimed here.

That transport has now been completed.  A second, much smaller verified SAT
lemma proves that every loopless symmetric 2-regular triangle-free graph on
six vertices has a cyclic ordering.  Applied to a quotient neighborhood, a
triangle gives the already-impossible `K₄` case; otherwise the local graph is
a six-cycle.  The seven named vertices (center plus cycle) are extended to a
global `Fin 16` labeling by a finite permutation.  The abstract signing is
converted entry-for-entry to Boolean matrices, and a vertex-switching gauge
is proved to preserve negative path parity while zeroing the zeroth sign row.

Consequently Lean now proves

```text
noNegativeSigning1622 : NoNegativeSigning1622
minDegreeForC4_thirtytwo_eq_six : minDegreeForC4 32 = 6
```

This **does** close the exact order-32 subproblem and gives the verified
monotonicity step `f(31) ≤ f(32)`.  It does not solve the full eventual
monotonicity problem Erdős 85; the general repair/extension theorem remains
open.

## Exact repair-reservoir accounting

The distance-layer analysis is now an identity rather than only an
inequality.  For every center `x`, the closed neighborhood, second layer, and
external repair candidates form an exhaustive disjoint partition of the
vertex set.  For a `d`-regular `C₄`-free graph, summing the exact branch
sizes gives

```text
|externalRepairCandidates(x)| + d² + 1
  = |V| + ∑_{y∈N(x)} deg_{G[N(x)]}(y).
```

Moreover `G[N(x)]` has maximum degree at most one, so it is a matching plus
isolated vertices.  Thus the correction term is exactly twice the number of
triangles through `x` and is at most `d`.  This pinpoints all slack in the
previous Moore-reservoir inequality: local triangles are the only mechanism
that can create external repair candidates below the girth-five Moore bound.
It also confirms that any successful general extension argument must exploit
more structure than the canonical one-reservoir repair criterion near the
orders where extremal witnesses are regular and locally sparse.

## Delete-set/add-gadget extension

Controlled deletion and arbitrary gadget attachment have now been composed
into a single exact surgery.  One may delete any `k` old vertices and add an
arbitrary `m`-vertex graph `F`.  Each new vertex `w` has an old attachment
selector `A(w)`.  The final order is `N-k+m`; a surviving old vertex is
required to pay exactly for its neighbors in the deleted set and is credited
exactly for the gadget vertices whose selectors contain it.  The existing
three common-neighbor budgets are necessary and sufficient for the final
graph to remain `C₄`-free.

The specialization `m=k+1` is a genuine order-raising surgery, and
`witnessExtension_of_delete_set_add_gadget` reduces one-step monotonicity to
finding such data uniformly for every witness.  The old delete-one/add-pair
repair is its `k=1` special case, but internal gadget degree can now replace
old attachments and deletion can remove a structured obstruction rather than
only one center.

Compatibility itself yields three useful necessary conditions, all now
formalized: every selector `A(w)` is common-neighbor independent; two distinct
selectors intersect in at most one vertex; and selectors belonging to
adjacent gadget vertices satisfy the same cross-anticompleteness condition as
the connected-pair construction.  Thus larger gadgets provide additional
internal degree, but their internal edges consume mixed common-neighbor
budget.  This is the precise tradeoff a future eventual construction must
exploit.

## Global gadget counting obstruction

Summing every mixed compatibility budget and double-counting incidences gives
a global restriction.  If the old graph has minimum degree `d`, every new
gadget vertex reaches degree `d`, and the internal gadget degrees are `r_w`,
then

```text
∑_w (d-r_w)(d+r_w) ≤ |V||W|.
```

For a nonempty `r`-regular gadget this simplifies to
`(d-r)(d+r) ≤ |V|`.  The connected pair has `r=1`, recovering the earlier
coarse obstruction `d²-1 ≤ |V|` from a much more general theorem.

More importantly, an `m`-vertex simple gadget has every `r_w ≤ m-1`.
Whenever `m-1 ≤ d`, compatibility therefore forces

```text
d² - (m-1)² ≤ |V|.
```

At the Moore-layer order `|V| = d(d-1)+1`, this implies
`(m-1)² ≥ d-1`.  Thus no bounded-size family of pure attachment gadgets
can establish eventual witness extension in this regime: gadget size must
grow at least on the square-root scale, or the construction must also modify
old edges.  This cleanly separates two viable future routes—large structured
gadgets versus combined attachment/switching surgery.

## Edge-compensated gadget surgery

The two remaining routes are now unified formally.  After deleting a set of
old vertices, the induced survivor graph may be replaced by any spanning
subgraph `K` before an arbitrary finite gadget is attached.  The exact degree
bookkeeping charges each survivor for both its deleted neighbors and every
additional incident survivor edge removed, then credits one unit for every
gadget selector containing it.  Taking a `k+1` vertex gadget after deleting
`k` vertices raises the order by one.  A uniform existence theorem for this
data implies `C4FreeWitnessExtension n`.

The global counting obstruction has a matching loss-corrected form.  If `H`
is the pre-deletion survivor graph, `K ≤ H`, and

```text
L = ∑_w ∑_{a∈A(w)} (deg_H(a)-deg_K(a)),
```

then compatibility forces

```text
∑_w (d-r_w)(d+r_w) ≤ |V||W| + L.
```

Thus old-edge deletion is not a free escape from the gadget obstruction: it
relaxes the bound by exactly its attachment-weighted degree loss.  At
`|V|=d(d-1)+1`, for an `m`-vertex gadget with `(m-1)² ≤ d-1`, Lean proves

```text
m (d-1-(m-1)²) ≤ L.
```

Every unit by which the gadget misses the square-root size threshold must be
paid once per gadget vertex through deletions incident to attachment
vertices.  Those same losses must then be compensated by the final
attachments, quantitatively linking the gadget-size obstruction to the
previous repair-cascade obstruction.

## Selector multiplicity obstruction

The weighted loss `L` cannot be concentrated without limit.  Let `t_x` be
the number of gadget selectors containing an old vertex `x`.  Since any two
distinct compatible selectors intersect in at most one old vertex,
double-counting pairs of selectors through old vertices gives

```text
∑_x choose(t_x,2) ≤ choose(m,2).
```

This is formalized by mapping each incidence `(x,{u,w})` to the selector pair
`{u,w}`; compatibility makes that map injective.

If `H` has degree exactly `d` at `x` and replacing `H` by `K` deletes
`ℓ_x` incident edges, final degree at least `d` forces `t_x ≥ ℓ_x`.
More generally, attachments must cover loss beyond the old degree surplus.
Consequently, for every `q`,

```text
#{x : deg_H(x)=d and ℓ_x≥q} * choose(q,2) ≤ choose(m,2).
```

In particular, at most `choose(m,2)` tight vertices can each suffer loss at
least two.  This is a global cascade restriction complementary to the
weighted-loss lower bound: small gadgets may need substantial old-edge loss
to overcome the Moore deficit, but compatibility prevents that loss from
being repaid at too many tight vertices with high selector multiplicity.

## Gadget degree-square obstruction

Compatibility forces not only every selector to be safe but also the gadget
graph `F` itself to be `C₄`-free.  Cherry counting inside `F` gives

```text
∑_w choose(r_w,2) ≤ choose(m,2),
```

and therefore `∑_w r_w² ≤ 2m(m-1)`.  Substituting this global bound into
the gadget counting inequality dramatically strengthens the earlier estimate:

```text
d² ≤ |V| + 2(m-1).
```

At `|V|=d(d-1)+1`, this first gives the linear requirement
`d-1 ≤ 2(m-1)`.  Applying Cauchy--Schwarz to the gadget degree sequence and
retaining the sharper identity
`∑ r_w² ≤ m(m-1)+∑ r_w` yields

```text
(d-m)² ≤ 2(m-1).
```

Hence every pure compatible replacement gadget at Moore-layer order has
`m = d - O(√d)`: it must contain almost `d` vertices.  This supersedes the
earlier square-root-size obstruction and shows that even moderately sized
attachment gadgets cannot establish eventual witness extension in the
critical regime.

The edge-compensated version is also sharpened.  Its degree-square balance is

```text
m d² ≤ |V|m + 2m(m-1) + L,
```

so below the linear threshold at Moore-layer order, old-edge deletion must pay
`m(d-1-2(m-1)) ≤ L`.  Thus the only way to use a substantially smaller gadget
is through a quantitatively large compensated edge surgery, still subject to
the selector-multiplicity cascade bounds above.

## True replacement-surgery obstruction

The compensated bounds are now stated directly for the actual order-raising
operation.  For a survivor `v`, its total replacement loss is

```text
|N_G(v) ∩ D| + (deg_{G-D}(v) - deg_K(v)),
```

combining neighbors lost with the deleted vertex set `D` and additional
survivor edges removed when passing to `K`.  Lean proves that final survivor
degree plus this quantity is exactly the original degree.

For an original graph of minimum degree `d`, delete-`k`/add-`k+1` repair at
the Moore-layer order `|V|=d(d-1)+1` must satisfy

```text
(k+1)(d-1-k)
  ≤ ∑_w ∑_{a∈A(w)} totalReplacementLoss(a).
```

This directly relevant version does not assume that the already-deleted
survivor graph still has minimum degree `d`.  When `k` is small relative to
`d`, the necessary weighted loss is linear in both `k+1` and `d`.

The selector cascade bound also extends to total replacement loss.  At every
original degree-`d` survivor, total loss is at most its attachment
multiplicity.  Hence for every `q`, the number of such survivors with total
loss at least `q`, multiplied by `choose(q,2)`, is at most `choose(k+1,2)`.
For an original `d`-regular graph the tightness condition is automatic.  True
replacement surgery therefore faces both a large aggregate-loss requirement
and a pair-design cap on how that loss can be distributed.

## Arbitrary delete-one/add-pair no-go

The true replacement bound has a sharp first specialization.  Delete a tight
vertex `x` of degree `d` from any graph of minimum degree at least `d`.  With
no additional survivor-edge deletion, total replacement loss is at most one
and is supported exactly on the `d` old neighbors of `x`.  Weighted
selector-incidence double counting
and the fact that two compatible selectors intersect in at most one vertex
give the upper bound

```text
∑_w ∑_{a∈A(w)} totalReplacementLoss(a) ≤ d+1
```

for every two-vertex gadget.  The Moore-order replacement theorem gives the
opposite bound `2(d-2)`.  Therefore Lean proves that for every `d ≥ 6`, no
compatible delete-one/add-two replacement exists at a tight vertex in any
minimum-degree-at-least-`d` graph on `d(d-1)+1` vertices when both new
vertices must reach degree `d`.  In particular, every graph of exact minimum
degree `d` has a minimum-degree vertex at which all such replacements fail;
regularity of the rest of the graph is unnecessary.

This is strictly broader than the earlier canonical repair-set obstruction:
both attachment selectors and the internal two-vertex gadget are arbitrary.
Thus the most immediate local order-raising surgery is ruled out uniformly in
the critical Moore-layer regime, not merely for the canonical neighborhood
choice.

## Fixed-`k` replacement obstruction

The delete-one/add-pair contradiction extends to every fixed deletion size.
With no additional survivor-edge deletion, double-counting the cut from a
deleted `k`-set of degree-`d` tight vertices gives total unweighted survivor
loss at most `kd`; no regularity is required away from the deleted set.  If
`t_v` is selector multiplicity, then

```text
loss(v) t_v ≤ loss(v) + k choose(t_v,2).
```

Summing and using the selector-pair bound yields

```text
weighted deleted-neighbor loss
  ≤ ∑_{x∈D} degree(x) + k choose(k+1,2).
```

Writing the deleted degrees as `kd` plus their surplus above the target gives
the fully nonregular necessary condition

```text
d - ((k+1)^2 + k choose(k+1,2))
  ≤ ∑_{x∈D} (degree(x)-d).
```

Thus a fixed-size deletion-only scheme in an arbitrary Moore-layer witness
must locate a deleted set whose total degree surplus grows linearly with `d`.
The tight-set no-go is the zero-surplus specialization.

Edge-minimal normalization makes this restriction genuinely structural.  If
`U` is the above-minimum layer and `T` the tight layer, every neighbor of a
vertex in `U` lies in `T`.  Swapping the endpoints of these incidences gives

```text
|U|(d+1) ≤ |T|d.
```

Consequently `|U|<|T|`: more than half the vertices are tight, and a tight
deletion set of every size `k` with `2k<n` exists.  Moreover, above the
replacement-polynomial threshold every successful deleted set must intersect
the smaller independent layer `U`; a strategy confined to the tight majority
cannot work.

At the Moore-layer order, the stronger C4-free cherry bound gives

```text
|U| choose(d+1,2) ≤ choose(|T|,2),
```

which Lean converts to the convenient rational estimate `5|U|<2n`, or
equivalently `3n<5|T|`.  Thus over three fifths of a normalized Moore-layer
witness is tight, and tight deletion sets exist for every `k` with `5k≤3n`.

## Moore-layer rigidity closes the degree-surplus escape

The asymmetric distance-layer estimate is stronger still.  In any C4-free
graph of minimum degree at least `d`, centering the disjoint branch count at
an arbitrary vertex `x` gives

```text
1 + degree(x) + degree(x)(d-2) ≤ |V|.
```

At exact Moore order `|V|=d(d-1)+1` and `d≥2`, this forces
`degree(x)≤d`.  Minimum degree gives the reverse inequality, so Lean proves

```text
∀ x, degree(x)=d.
```

Thus every genuine C4-free Moore-layer witness is automatically regular; the
above-minimum layer and deleted-degree surplus are actually zero.  Feeding
this rigidity into the replacement bound removes all normalization and
regularity hypotheses: whenever

```text
(k+1)^2 + k choose(k+1,2) < d,
```

no deletion-only delete-`k`/add-`k+1` compatible replacement works for any
deleted set in any C4-free minimum-degree-`d` witness at this order.  For
`k=1`, every vertex and every arbitrary two-vertex gadget fail once `d≥6`.

The equality case is in fact impossible beyond the triangle.  Exact reservoir
accounting forces the induced graph on every neighborhood to be one-regular
and leaves no vertex beyond distance two.  Hence adjacent and nonadjacent
pairs alike have exactly one common neighbor: the hypothetical graph is a
regular friendship graph.  Applying the repository's axiom-free formal
Friendship Theorem forces `d=2`.  Lean therefore proves the strict bound

```text
d(d-1)+2 ≤ |V|
```

for every nonempty C4-free graph of minimum degree at least `d≥3`, together
with the threshold form

```text
minDegreeForC4 (d(d-1)+1) ≤ d.
```

Accordingly, the natural C4-free-witness replacement statements at exact
Moore equality are vacuous for `d≥3`; their useful content survives in the
general loss inequalities and in near-Moore orders, while equality itself is
now completely classified.

```text
∑_w ∑_{a∈A(w)} replacementLoss(a)
  ≤ kd + k choose(m,2).
```

For true order raising `m=k+1`, comparison with the Moore-order lower bound
proves nonexistence whenever

```text
(k+1)² + k choose(k+1,2) < d.
```

Thus for every fixed `k`, arbitrary delete-`k`/add-`k+1` replacement without
extra survivor-edge surgery fails on tight deletion sets for all sufficiently
large target degrees.  The `k=1` case recovers the exact threshold `d≥6` for
the tight vertex that every exact-minimum-degree graph possesses.  Any
eventual extension strategy in this framework must therefore let `k` grow
with `d`, find enough degree surplus in the deleted set, or make essential use
of compensated old-edge modification.

## Quantitative bounded-replacement dichotomy

The fixed-`k` theorem now has both existence and compensated forms.  Any
compatible deletion-only replacement forces

```text
d ≤ (k+1)² + k choose(k+1,2) ≤ (k+1)³.
```

Thus the deletion size must grow at least on a cube-root scale even before
the stronger gadget-degree constraints are applied.

For a fully compensated repair, total replacement loss splits exactly into
deleted-neighbor loss and additional survivor-edge loss.  The former still
obeys `kd + k choose(k+1,2)`.  Comparing it with the Moore-order aggregate
lower bound proves

```text
d - ((k+1)² + k choose(k+1,2))
  ≤ ∑_w ∑_{a∈A(w)} (deg_{G-D}(a)-deg_K(a)).
```

Consequently, for fixed `k`, any repair beyond the deletion-only range must
perform attachment-weighted survivor-edge deletion growing linearly with
`d`.  This makes the earlier dichotomy quantitative: either replacement size
grows, or increasingly extensive old-edge surgery is unavoidable.

## Near-Moore stability and the first-order defect template

The asymmetric layer inequality gives more than rigidity at the now-excluded
equality point.  If

```text
|V| < (d+1)(d-1)+1 = d²,
```

then a vertex of degree at least `d+1` would already force too many vertices
in its first two distance layers.  Hence every C4-free graph of minimum degree
at least `d≥2` in this entire range is `d`-regular.  This has been formalized
as `regular_of_minDegree_card_lt_nextMooreLayer`.

At the first order left open by the strict bound,

```text
|V| = d(d-1)+2,
```

the exact regular reservoir identity reduces at every center `x` to

```text
|external(x)| + d = 1 + Σ_{y∈N(x)} deg_{G[N(x)]}(y).
```

The local degrees are at most one and their sum is even.  Lean now checks the
resulting parity dichotomy:

- if `d` is even, `G[N(x)]` is a perfect matching and there is exactly one
  vertex beyond distance two from `x`;
- if `d` is odd, `G[N(x)]` is a matching with exactly one isolated vertex and
  there is no vertex beyond distance two from `x`.

The odd case now has a formal defect-matching reduction.  The unique
triangle-free edge incident with each vertex forms a one-regular spanning
subgraph with adjacency matrix `M`.  Exact common-neighbor counts give the
Lean-checked identity

```text
A² = (d-1)I + J - M.
```

Lean also checks

```text
AM = MA,    M² = I,    tr(AM) = |V|.
```

On the orthogonal complement of the all-ones vector, the `M=+1` subspace has
`A²=d-2`, while the `M=-1` subspace has `A²=d`.  Since `tr(A)=0` and
`tr(AM)=|V|`, the traces on both subspaces are nonzero.  Characteristic
polynomials over the integers should therefore force both `d` and `d-2` to
be perfect squares, impossible for `d≥3`.

A useful basis-free route to the last statement is a reusable cubic-trace
lemma.  For an integer matrix `T`, if `T³=qT`, `q>0`, and `tr(T)≠0`, then the
quadratic factor `X²-q` must split over the rationals, hence `q` is a square.
Both matrix instantiations are checked in
`Erdos85OddFirstOrderSpectral`.  The matrix `A(I-M)` has cubic parameter `4d`
and trace `-|V|`.  The complementary matrix is

```text
|V| A(I+M) - 2dJ,
```

whose cubic parameter is `4|V|²(d-2)` and whose trace is
`|V|(|V|-2d)≠0`; these identities are formal too.  The earlier conditional
cubic-trace route is no longer needed.  If `p` is any prime divisor of odd
`d`, reducing `B=A(I-M)` modulo `p` turns `B³=4dB` into `B³=0`.  The trace of
a nilpotent matrix over `ZMod p` is zero, so `p` divides the integer trace
`-|V|`.  But `p∣d` and `|V|=d(d-1)+2` imply `p∣2`, hence `p=2`, contradicting
oddness.  Lean now checks this argument end to end.  Therefore
`d(d-1)+2` is impossible for every odd `d≥3`, giving the unconditional bounds

```text
d(d-1)+3 ≤ |V|,
minDegreeForC4 (d(d-1)+2) ≤ d.
```

The even first-order case now has an equally precise, but importantly
different, formal reduction.  The unique vertex beyond distance two from
each `x` defines a symmetric one-regular spanning graph, the antipodal
matching `P`.  Lean checks the full common-neighbor table and

```text
P² = I,    AP = PA,
A² = (d-1)I + J - P,    tr(AP) = 0.
```

Thus the odd modular trace contradiction does not simply repeat: the defect
matching in the odd case consists of edges and has `tr(AM)=|V|`, whereas the
even antipodal matching consists of nonedges and has zero mixed trace.

The displayed equations nevertheless expose a sharper spectral route.  On
the `P=+1` space (one coordinate per antipodal pair), the induced integral
quotient matrix `Q` satisfies

```text
Q² = (d-2)I + 2J,    Q 1 = d 1,    tr(Q)=0.
```

Consequently its nontrivial eigenvalues are `±sqrt(d-2)`.  Rationality of the
characteristic polynomial forces `d-2` to be a square; writing
`d-2=t²`, the trace multiplicities force `t | d=t²+2`, hence `t | 2`.
Since `d` is even, `t` is even, so `t=2` and `d=6`.  The already formalized
exact result `f(32)=6` then excludes this last case.  This program is now
formalized end to end.  Lean constructs the quotient graph on the two-element
antipodal fibers and checks

```text
|Q| = |V|/2,    degree_Q(X)=d,
|N_Q(X) intersection N_Q(Y)|=2  for X != Y,
Q^2 = (d-2)I + 2J.
```

The quotient is strongly regular with parameters
`(d(d-1)/2+1, d, 2, 2)`.  A rank-one determinant calculation gives the exact
product identity for its nontrivial characteristic factor.  Unique
factorization forces `d-2` to be a square, and splitting the factor over the
rationals plus the zero-trace coefficient proves `sqrt(d-2) | d`.  The
arithmetic contradiction above is checked as well.  Combining this even case
with the earlier odd modular-trace argument gives the new parity-free theorem

```text
d(d-1)+3 <= |V|,
minDegreeForC4 (d(d-1)+2) <= d
```

for every `d>=3`.

The next order `d(d-1)+3` also has an exact two-slack classification (for
`d>=4`).  If `E_x` is the number of vertices beyond distance two from `x`
and `S_x` is the degree sum in the induced neighborhood, Lean proves

```text
E_x + d = 2 + S_x,    E_x <= 2,    d-2 <= S_x <= d.
```

Because `S_x` is even, odd `d` forces `E_x=1` and `S_x=d-1` at every
vertex.  The beyond-distance-two graph would therefore be one-regular.  But
its vertex count `d(d-1)+3` is odd, contradicting the handshake lemma.  This
gives the additional checked odd-degree bounds

```text
d(d-1)+4 <= |V|,
minDegreeForC4 (d(d-1)+3) <= d.
```

For even `d`, the same classification leaves exactly two vertex types:
`(E_x,S_x)=(0,d-2)` or `(2,d)`.  Understanding the global interaction of
these two types is the next extremal obstruction.

There is already an unconditional modular consequence short of the full
square argument.  The centered plus-space matrix

```text
T = A ( |V|(I+P) - 2J )
```

now satisfies, in Lean,

```text
T³ = 4|V|²(d-2) T,    tr(T) = -2d|V|.
```

If a prime `p` divides `d-2`, reduction modulo `p` makes `T` nilpotent, so
`p | 2d|V|`.  But modulo such a prime, `d ≡ 2` and
`|V|=d(d-1)+2 ≡ 4`; hence `p | 16` and primality forces `p=2`.
This argument is formalized end to end, including the consequence

```text
d - 2 = 2^k
```

for some `k`.  This formerly surviving family is now eliminated by the
quotient characteristic-polynomial argument above.

The exact small-order results have also been transported from `Fin n` to
arbitrary finite vertex types.  They exclude `d=4` (order 14) and `d=6`
(order 32) directly.  Together with parity, Lean therefore sharpens the
surviving family to

```text
d = 2 + 2^k,    k ≥ 3.
```

In particular, once the quotient characteristic-polynomial argument forces
`k` even and its trace forces `k≤2`, the contradiction will close without
any further finite computation.

## Even second-order defect two-factor

The remaining even case at order `d(d-1)+3` has now been globalized.  Define
`D` as the union of two zero-common-neighbor relations:

```text
M: nonadjacent pairs beyond distance two,
N: adjacent pairs lying in no triangle,
D = M union N.
```

The local identity also gives

```text
|N(x)| + S_x = d.
```

Combined with the even local alternatives, this proves that every vertex has
degree two in `D`.  More sharply, its two incident defect edges always have
the same kind:

```text
(deg_M(x),deg_N(x)) = (0,2) or (2,0).
```

Therefore `D` is a spanning disjoint union of cycles, and every connected
defect cycle is monochromatic: it consists entirely of distant nonedges or
entirely of triangle-free edges of the original graph.

For every distinct pair `x,y`, Lean now checks the exact table

```text
|N_G(x) intersection N_G(y)| = 0  if xy is an edge of D,
                                1  otherwise.
```

Consequently, with `A` the original adjacency matrix,

```text
A^2 = (d-1)I + J - D.
```

Regularity then implies `AJ=JA=dJ`, so the defect matrix is a polynomial in
`A` and `J` and hence

```text
AD = DA.
```

This is the new spectral entry point.  Since `d` is even, the common order
`d(d-1)+3` is odd, so the two-factor has odd total order.  On the subspace
orthogonal to the all-ones vector the equation becomes

```text
A^2 = (d-1)I - D.
```

A determinant calculation predicts a useful cycle-parity constraint.  For a
cycle of length `r`,

```text
det((d-1)I - A(C_r)) =
  (d-3) * square                         if r is odd,
  (d-3)(d+1) * square                   if r is even.
```

The all-ones direction changes the `d-3` eigenvalue to `d^2`.  Since the
left side is `det(A)^2`, and `(d-3)(d+1)=(d-1)^2-4` is strictly between
consecutive squares for even `d>=4`, the number of even defect cycles should
be even.  This determinant/cycle factorization remains to be formalized; it
is a constraint rather than yet a contradiction.  The stronger prospective
route is to use `AD=DA` on the cyclotomic eigenspaces of each monochromatic
cycle and exploit that `A` is an integral square root of `(d-1)I-D` there.

The nonsingularity needed for the rank-one determinant step is now checked:
over `Q`, `(d-1)I-D` is strictly diagonally dominant, because every diagonal
entry has norm `d-1>=3` while every row has exactly two off-diagonal unit
entries.  Hence its determinant is nonzero.  This permits the matrix
determinant lemma to be applied to the addition of `J` without any unproved
spectral assumption.

The rank-one calculation and its square consequence are now also checked in
Lean.  Writing `B=(d-1)I-D`, the exact identities are

```text
(d-3) det(B+J) = d^2 det(B),
(d-3) det(A)^2 = d^2 det(B).
```

The second follows from the rational matrix version of `A^2=B+J`; that
version is proved entrywise rather than assumed from scalar extension.  In
particular Lean packages the consequence

```text
det(B) = (d-3) q^2
```

for an explicit rational `q=det(A)/d`.  Thus the proposed cycle-factor
argument now has a formally verified square target.  What remains is to
reindex the two-regular graph by its cycle components and prove the individual
cycle determinant formulas, after which comparison of rational square classes
will constrain the number and lengths of even defect cycles.

The polynomial part of those individual factors is now formalized too.  In
terms of mathlib's rescaled Chebyshev polynomials `C_m,S_m`, Lean proves

```text
C_m(X)^2 - 4 = (X^2-4) S_{m-1}(X)^2,
C_{2m}(X)-2 = (X-2)(X+2) S_{m-1}(X)^2,
C_{2m+1}(X)-2 = (X-2)(S_m(X)+S_{m-1}(X))^2.
```

After evaluation at `X=d-1`, an even cycle therefore contributes square
class `(d-3)(d+1)`, while an odd cycle contributes square class `d-3`.
These are checked polynomial identities, not numerical experiments.  The
remaining bridge is the standard but as yet unformalized identity
`charpoly(C_r)=C_r(X)-2` together with block factorization over the connected
components of the defect two-factor.

The square-class bookkeeping for a whole cycle list is now checked as well.
For a list `rs` of cycle lengths, Lean defines `evenCycleCount rs` and proves

```text
product_{r in rs} (C_r(d-1)-2)
  = (d-3)^{|rs|} (d+1)^{evenCycleCount(rs)} s^2
```

for an integer `s`.  It also proves that parity of the sum of the lengths is
parity of the number of odd lengths.  Combining these facts with the verified
global rational-square identity and the strict-between-squares lemma gives the
fully checked conditional conclusion:

```text
if sum(rs) is odd and the defect resolvent determinant is the above
cycle-factor product, then evenCycleCount(rs) is even.
```

Thus all arithmetic after the component/characteristic-polynomial bridge is
now formal; only that graph-to-block-polynomial bridge remains for this
particular obstruction.

The graph side of that bridge has now also been tightened.  Lean proves that
the triangle-free-edge summand contains no triangle, and in a `C4`-free
ambient graph it contains no simple four-cycle.  Hence every cycle component
of this color has length at least five.  More importantly, the pointwise
degree-two statement has been promoted to Mathlib's global `IsCycles`
predicate, and every connected component is now supplied with a simple closed
walk whose vertex set is exactly the component.  The remaining determinant
work therefore no longer needs to construct or justify the cycle
decomposition: it starts with an explicit spanning cycle for each component
and only needs to reindex its adjacency matrix and prove the Chebyshev
characteristic-polynomial identity.

That reindexing step is now formal as well.  For every simple closed walk
`p`, Lean constructs an explicit graph isomorphism

```text
cycleGraph(p.length) ≃g p.toSubgraph.coe.
```

The construction enumerates the duplicate-free `dropLast` of the walk's
support, proves that this list is exactly the vertex set of the traversed
subgraph, and checks both ordinary successor edges and the wraparound edge.
The induced matrix reindexing is proved to carry the standard cycle adjacency
matrix to the component adjacency matrix, so their characteristic polynomials
are equal.  Thus the graph/component half of the former bridge is closed.  Its
only remaining local ingredient is now the pure matrix identity
`charpoly(adj(C_r)) = C_r(X)-2`; after that, the already-formal square-class
bookkeeping applies component by component.

The global block factorization is now checked independently of that identity.
Lean constructs the canonical equivalence

```text
V ≃ Σ c : D.ConnectedComponent, c.supp
```

and proves that reindexing `D.adjMatrix` along it gives the dependent block
diagonal matrix of the adjacency matrices induced on the component supports.
Using the existing general determinant theorem for dependent block diagonals,
this yields, over every commutative ring,

```text
det(aI - adj(D))
  = product over components c of det(aI - adj(D induced on c.supp)).
```

Thus neither component enumeration nor determinant multiplicativity remains
conditional.

The standard individual cycle block has now been evaluated too.  A direct
Laplace-expansion proof first establishes the continuant recurrence

```text
charpoly(P_(n+2)) = X charpoly(P_(n+1)) - charpoly(P_n),
```

including both base cases, and hence identifies `charpoly(P_n)` with the
rescaled Chebyshev polynomial `S_n`.  Expanding the cycle matrix then leaves
the two path cofactors and two shifted triangular minors; the latter have
diagonal `-1` and supply exactly the two wraparound terms.  Lean consequently
proves, without `sorry` or `admit`,

```text
charpoly(adj(cycleGraph(n+3))) = C_(n+3)(X) - 2.
```

There was one subtle graph-theoretic gap between a *spanning cycle walk* and
the full induced component: a priori the induced component might contain
extra chords.  This is now closed by a general formal lemma.  If every vertex
of a finite graph has degree two and a simple cycle spans a vertex set, then
the cycle subgraph equals the graph induced on that set.  Indeed the cycle
neighbor set is contained in the ambient neighbor set and both have cardinality
two, so they are equal at every vertex.  Applied to the second-order defect
graph, each connected component is therefore genuinely an induced cycle.
The induced cycle characteristic polynomial is then the Chebyshev factor
above.

At this point the mathematical component-factor bridge is complete.  The
remaining Lean plumbing for the global headline is to transport matrices
across the equality between the spanning walk's vertex subtype and the
connected component's support subtype, then substitute the individual
Chebyshev factors into the already-proved dependent block product.  This is
an instance/reindexing issue rather than a remaining combinatorial or spectral
identity.

## Completed global cycle factorization and parity obstruction

That final transport is now checked.  Each component factor is indexed by its
actual support cardinality, and Lean proves the global identity

```text
det(aI-D) = product_c (C_{|c|}(a)-2).
```

Specializing to `a=d-1`, casting the integral determinant identity to the
rationals, and combining it with the already-proved rank-one square identity
and nonsingularity gives an unconditional theorem.  There is a list `rs`
of the actual defect-component orders such that every entry is at least
three,

```text
sum(rs) = |V| = d(d-1)+3,
Odd(sum(rs)),
Even(evenCycleCount(rs)).
```

Thus the former conditional bridge is completely discharged.  In particular,
the number of odd defect cycles is odd, and hence the total number of defect
components is odd.

This is still a structural obstruction rather than a contradiction.  A
further rational eigenspace audit explains why the determinant captures the
obvious square-root parity information: every nonexceptional eigenvalue of a
cycle occurs with multiplicity two.  The only simple cycle eigenvalues are
`2`, and additionally `-2` for even cycles; these yield respectively the
component-count and even-cycle-count parity conditions.  Further progress
therefore has to use integral lattice information, modular/Jordan structure,
the monochromatic defect coloring, or return to the witness-repair program,
rather than merely repeat the rational square-class calculation.

## Restart continuation: quotient and characteristic-two leads

The even second-order target must be stated with care.  It cannot be excluded
for every even degree: `d=4`, order `15`, is realized by `fifteenRegular`.
The meaningful classification target is therefore to prove that this is the
only even example, or to identify a higher-degree family.

Commutation of the original adjacency matrix `A` with the defect two-factor
`D` makes the partition into connected components of `D` equitable.  If `Q`
is the resulting component quotient and `r` is the column vector of component
orders, restriction of

```text
A^2 = (d-1)I + J - D
```

to vectors constant on each defect component gives the exact quotient
equation

```text
Q^2 = (d-3)I + 1 r^T,
Q 1 = d 1,
r_i Q_ij = r_j Q_ji.
```

For the checked 15-vertex example the defect components have colored lengths
`M:3`, `N:6`, `M:6`, and

```text
Q = [[0,2,2],
     [1,2,1],
     [1,1,2]].
```

This supplies the base case any proposed obstruction must permit.

There is a sharp characteristic-two obstruction under the **additional
circulant hypothesis**.  In that model the connection set `S=-S` satisfies the
group-ring difference equation with every nonzero difference represented
once except the two directions of the defect cycle.  Modulo two, squaring
`sum_{s in S} x^s` cancels all cross terms, leaving support `|S|=d`, whereas
the required right side has support `d(d-1)`.  Hence no even `d>2` *circulant*
example has a single cyclic defect component.  This does **not** settle the
one-component graph case: commuting with the adjacency matrix of a cycle does
not imply commuting with its oriented shift, because the nontrivial cycle
eigenvalues have multiplicity two.  Direct enumeration only confirms the
circulant subcase for `(d,n)=(4,15),(6,33),(8,59)`.

For the full multi-component case, reduction modulo two gives

```text
A^2 = I + J + D.
```

On a defect cycle, the exceptional kernel of `I+D` is controlled by cycle
lengths divisible by three.  The next promising audit is therefore to combine
the mod-two nullity/Jordan data with the monochromatic `M/N` coloring.  The
color is not visible in the completed rational determinant factorization and
is the main structural input not yet spent.

## Cubic color trace and the first degree-six sieve

The first higher color-sensitive trace is now formalized in
`Erdos85SecondOrderColorTrace.lean`.  In addition to `tr(A D) = 2s`, where
`s` is the total order of the triangle-free-edge (`N`) defect components,
Lean proves directly from the second-order matrix equation that

```text
tr(A^3) + tr(A D) = |V| d.
```

The previously informal sentence “`tr(A^3)` is six times the number of
triangles” has now been replaced by a fully checked graph-theoretic bridge.
Lean proves that every `C4`-free graph has edge-disjoint triangles, deletes
the edges lying in no triangle, and proves that the remaining spanning
subgraph is locally linear.  Mathlib's locally-linear double count then gives
three retained edges per triangle.  The handshake lemma, together with the
proved fact that the triangle-free summand is a union of cycles, yields the
natural-number identity

```text
6 T + 2 s = |V| d.
```

Thus the congruence is now an actual graph theorem, with no unproved trace
interpretation or arithmetic premise:

```text
s = |V| d / 2  (mod 3).
```

An audit found an arithmetic error in the original specialization: for
`d=6`, `|V|=33`, the right side is `99=0 (mod 3)`, not `2`.  The Lean and
Python sieves have been corrected accordingly.  Exact integer enumeration of
the three-component quotient equation before applying the corrected color
condition leaves the following length types:

```text
(3,12,18), (3,15,15), (5,8,20), (6,9,18), (11,11,11).
```

The audit also found that the old sieve discarded every partition whose
component lengths were all divisible by three.  That was valid only for the
incorrect target `s=2`; for the correct target `s=0`, such partitions are
automatically color-compatible.  After removing this stale filter and adding
the elementary antipodal-C5 obstruction, the exact search counts are:

```text
9 components: 0
7 components: 24
5 components: 12
3 components: 2
1 component:  1
```

The 11-component all-3 partition is not yet re-certified because the former
early rejection had hidden a much larger quotient search.  Therefore the
previous claim of a unique `(5,8,20)` survivor is withdrawn.  The earlier
Boolean checks and residual eight-vertex matching search assumed an invalid
color sieve and are no longer used as graph-theoretic evidence; their closed
finite Lean evaluations remain labeled historical.  Previously, in the obsolete length-5-`N` model, the absence of edges between the 5- and
8-components forces five perfect matchings on the 8-set to partition the
complement of its defect 8-cycle.  This forced 1-factorization is the most
promising hand-proof entry point for excluding the residual degree-six
quotient.

### Commutation-aware audit

The quotient sieve uses only the constant vector on each defect component.
The next audit added the full entrywise relation `AD=DA` and the exact
second-order common-neighbor equation to a temporary Z3 model for every
surviving quotient.  All 38 classified cases with 3, 5, or 7 components are
UNSAT (the two 3-component cases and all 12+24 cases), each in under one
second.  The single 33-cycle case is also UNSAT.  The eleven-triangle case
does not finish under the same unstructured SAT encoding, but has a cleaner
spectral obstruction: on the 22-dimensional sum of the nonconstant
3-cycle spaces, `A²=6I`, so its rational trace is zero; on the component-
constant space the quotient trace is six, contradicting `tr(A)=0`.

This computation is exploratory evidence, not yet a trusted certificate.
The reusable bridge needed by a sound classifier is now formalized in
`Erdos85SecondOrderEvenDefect.lean`:

```text
|N_D(y) ∩ N_G(x)| = |N_D(x) ∩ N_G(y)|.
```

It is proved entrywise from the already checked matrix commutation theorem.
Constraint minimization shows that commutation, quotient degrees, and the
requirement that each non-defect pair have exactly one common neighbor are
already enough for all 38 contradictions; the zero-common-neighbor equations
on defect edges are not needed.  Even more sharply, it suffices to impose the
one-common-neighbor equation on pairs in the same component and congruent
modulo three in a cyclic labeling.  This points toward a small Fourier/
recurrence lemma rather than a 33-vertex exhaustive certificate.

The residual local matching problem has now also been exhausted, independently
of the original 33-vertex SAT instance.  For a vertex `z` of the 20-component,
let `e(z)` be its two-element neighborhood in the 8-component.  Summing the
unique-common-neighbor condition over all eight vertices shows more than a
count: the following four pairs must partition the 8-set:

```text
P0(e(z)), e(w0), e(w+), e(w-).
```

Here `P0` is the internal perfect matching of the 8-component, `w0` is the
unique internal neighbor of `z` in its own 4-vertex fiber, and `w+`,`w-` are
its unique neighbors in the two nonconsecutive fibers.  There are exactly 38
one-factorizations of the complement of `C8`, 12 cyclic assignments after
rotation/reflection normalization, and 31 choices for `P0`.  Checking all
`38*12*31 = 14136` cases gives no solution even to these local partition
equations.  The reproducible verifier is
`computations/degree6_residual_matching.py` and prints
`NO LOCAL MODELS 14136`.

Thus every three-component degree-six quotient type is excluded once the
cubic color congruence and the local common-neighbor equations are combined.
The remaining work for a full degree-six nonexistence theorem is to prove a
complete quotient classification, including five or more components, and to
replace or formalize the finite 8-vertex matching lemma.

The quotient classification has since been completed by exact integer
backtracking in `computations/degree6_quotient_classification.py`.  The search
uses the row sum, detailed balance, diagonal and off-diagonal entries of
`Q^2`, cycle parity, and the colored length congruence.  A further elementary
condition is decisive: the induced graph on component `i` is `Q_ii`-regular,
so `r_i Q_ii` is even.  This immediately removes the five-component survivor
`(3,5,5,5,15)` (its 3-component has internal degree one) and all
`(11,11,11)` survivors (their diagonal entries are a permutation of
`1,2,3`).  No seven- or nine-component survivor exists.  Up to permutations,
the unique remaining quotient is therefore

```text
r = (5,8,20),  Q = [[2,0,4],[0,1,5],[1,2,3]].
```

The color congruence permits the 5- or 20-component to be `N`.  If the
20-component is `N`, then the 5-component is `M`; its internal degree is two.
The only 2-regular simple graph on five vertices disjoint from the defect
5-cycle is the complementary 5-cycle, but consecutive defect vertices then
have a common internal neighbor, contradicting their `M` status.  Hence only
the `N`-colored 5-cycle case reaches the finite matching lemma.

The matching verifier has also been simplified substantially: no SAT/SMT
solver is needed.  In every one of the 14,136 factorization/order/internal
matching cases, there is already a single edge `e` for which *no choices at
all* of the other three pairs can form the required partition of the 8-set.
Thus the obstruction is pointwise local; global consistency of the cross
matchings is never used.  The dependency-free verifier finishes in under one
second and prints `NO LOCAL MODELS 14136`.  This is now a realistic
`native_decide` target for Lean.

## Formal component-quotient bridge

`Erdos85SecondOrderQuotient.lean` now proves the algebraic input used by the
degree-six classifier.  For the connected components of the even
second-order defect graph, Lean constructs the integral quotient matrix `Q`
and proves:

```text
∑_e Q_ce = d,
r_c Q_ce = r_e Q_ec,
(Q^2)_ce = (d-3) [c=e] + r_e.
```

The square equation is obtained internally from `A S = S Q`, `D S = 2 S`,
`J S = 1 rᵀ`, and the already formalized identity
`A² = (d-1)I + J - D`.  Both real and natural-number versions are present;
the natural version is the intended interface to a finite `native_decide`
classifier.  The detailed-balance identity is proved by an explicit finite
double count of edges between two defect components.  The full
`Proofs.Erdos85Results` umbrella build succeeds with all 8,662 targets.

This removes the largest trust gap in the quotient computation.  The next
formal layer should package the remaining elementary constraints (component
orders sum to 33, odd cycle lengths, diagonal handshake parity, and the color
congruence), then certify that they leave only `(5,8,20)` with the displayed
quotient.  After that, the 8-vertex local matching obstruction can be a
separate small decidable theorem.

Both finite searches have now been ported into Lean.  The file
`Erdos85DegreeSixQuotientClassification.lean` constructs nondecreasing
partitions of 33 and quotient rows as weak compositions of six, then performs
the same exact row-domain/backtracking classification.  Closed
`native_decide` theorems prove that the 9-, 7-, and 5-component survivor lists
are empty and that the 3-component list is exactly

```text
[ ((5,8,20), ((2,0,4),(0,1,5),(1,2,3)), (mask 1, mask 4)) ].
```

The file `Erdos85DegreeSixResidualMatching.lean` independently generates all
31 perfect matchings of the complement of `C8`, all 38 one-factorizations,
and all 12 normalized cyclic orders.  Lean verifies the product count 14,136
and proves that the relaxed local-model list is empty.  Both files are
imported by `Erdos85Results.lean`; the full umbrella build now succeeds with
8,664 targets.

These are genuine closed kernel-checked computations, but assembly into a
graph-level degree-six nonexistence theorem still requires completeness
bridges: an arbitrary defect-component list and quotient satisfying the
formal graph identities must be shown to enter the generated backtracking
space, and the residual graph data must be mapped to the relaxed local
matching model.  Those bridges, rather than the finite calculations
themselves, are now the critical path.

## Ramsey inverse reformulation and an infinite-family target

A literature audit confirms that Problem 85 is still listed as open.  Write
`R(t)=R(C4,K_{1,t})`.  Directly from the definitions,

```text
minDegreeForC4(N) = N - max { t : R(t) <= N }.
```

Consequently eventual monotonicity of `minDegreeForC4` is equivalent to
eventual *strict* monotonicity of `R(t)`: a plateau `R(t+1)=R(t)` produces a
one-step drop of the minimum-degree threshold, and every such drop produces a
plateau.  This identifies the correct infinite obstruction; a finite exact
value such as the order-33 result cannot by itself resolve Problem 85.

Luis Boza's 2024 paper *Exact Values and Bounds for Ramsey Numbers of C4
Versus a Star Graph* proves that, for `m = 2 (mod 6)`, `m >= 8`,

```text
R(C4,K_{1,m^2+3}) <= m^2+m+4.
```

At first sight, an infinite family of `C4`-free graphs on `m^2+m+3` vertices
with minimum degree `m+1` would be decisive: it would give

```text
R(C4,K_{1,m^2+2}) = R(C4,K_{1,m^2+3}) = m^2+m+4,
```

and disprove eventual monotonicity.  However, setting `d=m+1` puts these at
the second-order size `d(d-1)+3` with `d=3 (mod 6)` odd.  The already
formalized theorem `containsC4_of_odd_secondOrder` rules them out completely:
the beyond-distance-two relation would be one-regular on an odd number of
vertices.  Thus Boza's congruence family cannot supply plateaus; the formal
parity obstruction explains exactly why the tempting lower-bound
construction is impossible.  Any counterexample family must occur at a
different offset or in the even-degree branch, together with a matching
Ramsey upper bound.

The same audit also corrects the interpretation of the degree-six target.
`minDegreeForC4` is the *forcing threshold*, not the largest attainable
minimum degree.  Excluding minimum degree six at order 33 proves
`minDegreeForC4(33) <= 6`; together with a minimum-degree-five construction it
gives equality, not a drop from the already formalized value at 32.  The
equivalent Ramsey value `R(C4,K_{1,27})=33` is already known (Boza obtains it
from the computed extremal bound `ex(33,C4)=96`).  Our quotient/matching route
would provide a new structural and formally verified proof of this finite
value, but it should not be presented as a resolution or counterexample to
Problem 85.

The Ramsey inverse has now been formalized precisely in
`Erdos85RamseyPlateau.lean`.  Define the order-`m` capacity

```text
cap(m) = m - minDegreeForC4(m).
```

Lean proves that, whenever the star fits, `C4StarRamseyAt m s` is equivalent
to `s <= cap(m)`, and that one-step monotonicity is equivalent to
`cap(m+1) <= cap(m)+1`.  More sharply, define a consecutive plateau at
`(m,s)` to mean that neither star size `s,s+1` is forced at order `m`, while
both are forced at order `m+1`.  The kernel-checked local theorem is

```text
minDegreeForC4(m+1) < minDegreeForC4(m)
  iff exists s, ConsecutiveC4StarPlateauAt m s.
```

It is lifted both to the eventual positive statement and to the negation:
Erdős 85 is exactly eventual absence of consecutive plateaus, while its
negation is the existence of arbitrarily large such plateaus.  This removes
all convention and inverse-function ambiguity from the global target.  The
full umbrella build, including this module, succeeds with 8,665 targets.

## Plateau-core normalization and Moore localization

The graph side of the plateau equivalence is now normalized as well.  A
`C4PlateauCore m d` is a C4-free graph on `m` vertices with minimum degree
exactly `d`, with every edge incident to a degree-`d` vertex, while every
graph on `m+1` vertices of minimum degree at least `d` contains a C4.  Lean
proves the exact equivalence

```text
minDegreeForC4(m+1) < minDegreeForC4(m)
  iff exists d, C4PlateauCore m d.
```

Thus Erdős 85 is also exactly the eventual absence of these edge-minimal
cores.  This is a substantially better structural target than arbitrary
C4-free graphs: the tight vertices form a vertex cover, and all edges among
non-tight vertices have already been deleted.

The first general restrictions on a core are kernel-checked.  Its degree is
at least two.  If `d >= 3`, the strict Moore arguments give

```text
d(d-1)+3 <= m.
```

If additionally `m < (d+1)(d-1)+1 = d^2`, near-Moore rigidity forces the
entire core to be `d`-regular.  At the boundary `m=d(d-1)+3`, odd `d>=4` is
impossible by the one-regular antipodal-graph parity obstruction.  Hence the
lowest possible core in a degree band must have even degree; odd-degree
cores start at least one order later.  The promising next target is therefore
the regular interval

```text
d(d-1)+3 <= m < d^2,
```

split into the even boundary case and positive-slack odd cases.  Any proof
that such regular graphs always admit a one-vertex extension preserving
minimum degree `d`, or that a nonregular core above this interval cannot have
its tight vertices cover every edge, would settle the corresponding degree
band and moves directly toward eventual monotonicity.

## Exact obstruction to attachment-only extension

The common-neighbour conflict formulation has now been connected directly to
plateau cores.  Lean proves that every `C4PlateauCore m d` has a normalized
witness `G` satisfying

```text
indepNum(commonNeighborConflict G) < d.
```

More importantly, the conflict graph can be counted exactly in the regular
near-Moore regime.  For each vertex `x`, length-two walks from `x` are split
according to their first edge.  C4-freeness makes these `d` branches pairwise
disjoint, and regularity gives `d-1` endpoints in each branch.  The new file
`Erdos85ConflictRegular.lean` formalizes the resulting identity

```text
degree(commonNeighborConflict G, x) = d(d-1).
```

It also proves the sharp elementary consequence

```text
indepNum(commonNeighborConflict G) <= |V(G)| - d(d-1).
```

Thus at second-order size `|V|=d(d-1)+3`, every safe attachment set has at
most three vertices.  For `d>=4`, simply adjoining a vertex to a safe set can
never preserve minimum degree `d`.  This corrects the previous suggestion
that a pure attachment argument might eliminate regular cores in this
interval.  Any successful proof near the Moore boundary must perform genuine
edge surgery: attach the new vertex to at least `d` old vertices while
deleting a controlled family of old edges that destroys all induced
common-neighbour conflicts and compensates every tight endpoint.

The structural target is consequently sharper.  Starting from a regular
core, choose an attachment set `S` and old edges to delete.  Every pair in
`S` that shared a common neighbour must lose at least one of its two incident
edges to that centre, while each old vertex can lose no more edges than its
new adjacency compensates.  This incidence-cover problem is the scalable
version of the residual-matching constraints already encountered in the
degree-six search.

## Tight-layer majority in every plateau core

The existing layered-witness theory yields a global constraint that is now
connected explicitly to plateau cores.  Write `T` for the degree-`d` vertices and `U` for the
vertices of degree strictly greater than `d`.  Since `T` covers every edge,
`U` is independent and every edge incident with `U` goes into `T`.  Double
counting this cut gives

```text
|U|(d+1) <= |T|d.
```

Together with the exact partition `|T|+|U|=|V|`, this proves `|U|<|T|`: a
normalized plateau core has a strict majority of tight vertices.  The earlier
restricted cherry packing simultaneously gives

```text
|U| * choose(d+1,2) <= choose(|T|,2).
```

`Erdos85RamseyPlateau.lean` now packages a core witness satisfying both
inequalities.  This is useful above the regular range `m<d^2`, where the core
may be nonregular: any counterexample must still have a large degree-`d`
vertex cover and a much smaller independent high-degree layer whose
neighbourhood pairs form a packing in that cover.

A literature comparison with graphs of defect/excess two uncovered a close
algebraic analogue but not an applicable classification theorem.  Classical
diameter-two defect-two graphs have order `d^2-1`, whereas our second strict
Moore order is `d(d-1)+3`; moreover our C4-free graphs may contain triangles.
Their generalized defect matrix is still two-regular, and our existing
cycle-factorization theorem already proves the analogous parity restriction
that the number of even defect cycles is even.  Published work treats full
cyclic-defect graphs or other diameter/girth hypotheses and explicitly leaves
broad defect-two cases open, so it cannot currently be imported as a
black-box nonexistence result for Erdős 85.

## Full-sequence divergence of the threshold

The polarity construction now gives more than an unbounded subsequence.
For a finite field of order `q`, the projective-plane graph supplies a
C4-free minimum-degree-`q` witness at order

```text
a = q^2+q+1,
```

and deletion of an absolute point supplies one at the consecutive order

```text
b = q^2+q.
```

Disjoint union preserves both C4-freeness and the minimum-degree lower
bound.  Since `a=b+1`, every `n>=b^2` has the explicit representation

```text
r*a + (k-r)*b = n,
where r=n mod b and k=n/b.
```

Indeed `r<b<=k`, so both coefficients are nonnegative.  Taking a Galois
field of order `q=2^(d+1)` for each target `d` proves, in Lean, that every
sufficiently large order has a C4-free graph of minimum degree at least `d`.
Equivalently,

```text
Tendsto minDegreeForC4 atTop atTop.
```

This rules out any infinite counterexample family with bounded threshold
degree: the canonical degrees `minDegreeForC4(m+1)` of hypothetical plateau
cores must themselves tend to infinity.  It does not yet exclude high-degree
cores, but it removes bounded-degree pathologies and justifies focusing on
scalable surgery in the `d -> infinity` regime.

The conductor has since been improved from quartic to cubic by using the
entire deletion band.  An interval-composition lemma proves that witnesses at
every order `A,...,A+L` generate witnesses at every order at least

```text
(A/L+1)A.
```

Choose by Bertrand a prime `p` with
`2(d+2)<p<=4(d+2)`.  The free polarity deletion band gives degree-at-least-`d`
witnesses throughout

```text
A = p^2+d  through  A+L = p^2+p,   L=p-d.
```

Thus every degree-`d` plateau core satisfies the kernel-checked localization

```text
m+1 < ((p^2+d)/(p-d)+1)(p^2+d)
```

for such a prime `p`.  Since `p=Theta(d)`, the right side is `O(d^3)`.
The relaxed arithmetic estimate has also been packaged without the auxiliary
prime:

```text
n >= 400(d+2)^3  implies  C4FreeMinDegreeWitness n d,
m+1 < 400(d+2)^3  for every C4PlateauCore m d.
```

Together with the Moore lower bound this confines all possible cores to a
quadratic-to-cubic window.  Closing that remaining factor of `d`, or deriving
a contradiction from the tight/high-layer packing inside this window, is now
the quantitative bottleneck.

## Kernel-checked cycle-block soundness

The full graph-to-periodicity bridge is now in place. A simple cycle walk in
any two-regular defect graph receives additive `ZMod` coordinates whose range
is exactly the walk's vertex set and whose two neighbors are the preceding
and succeeding coordinates. Restricting `AD=DA` to two such cycles gives the
rectangular recurrence, hence translation of the source coordinate by the
target cycle length preserves every adjacency into the target component.

The new graph-level quotient consequence is:

```text
q.length • 1 != 0 in ZMod p.length
  ==> componentQuotientMatrix G D c e <= 1.
```

Here `p` and `q` span the source and target connected components. The proof
identifies the cyclic parametrization range with the actual component support
before applying the `C4` common-neighbor bound, closing the main semantic gap
behind an individual `periodicCommonNeighborOK` term. The remaining
classifier-soundness task is to aggregate all target components having the
same nonconsecutive residue and transport an arbitrary finite component list
into the closed list classifier.

The primary-literature audit was also refreshed against version 2 (12 June
2026) of Boza's arXiv:2409.12770. Its exact table has strict Ramsey growth
through parameter 39 and explicitly reports no known counterexample to the
stronger lower bound `R(C4,K1,n) >= n + ceil(sqrt n)`. Its scalable upper
bound at `m^2+3`, `m = 2 mod 6`, remains the closest apparent plateau target,
but it lands in precisely the odd second-order family already excluded by our
parity theorem.

The periodicity consequence has since been strengthened from a single target
component to the exact grouped inequality used by the classifier.  If `es`
is any finite family of target components whose lengths induce one common
nonzero translation `s` on a fixed source cycle, Lean now proves

```text
sum (Q source target) over target in es <= 1.
```

The proof fixes one source orientation for every rectangular block, unions
the pairwise-disjoint component-neighbor finsets, and embeds that union into
the common-neighbor set of two distinct source vertices.  This avoids the
otherwise serious sign ambiguity from independently choosing a dihedral
coordinate system for each block.

An exploratory exact search generalized the quotient equations to arbitrary
even degree.  For three defect components, the quotient plus handshake and
grouped-periodicity constraints have no survivors for every even degree
`6 <= d <= 30` except `d=12`.  The sole exceptional quotient found is

```text
r = (15,60,60),
Q = ((4,4,4),(1,4,7),(1,7,4)).
```

Degree four has the expected genuine boundary survivor.  For degree eight,
the search also finds zero survivors with five or seven components; for
degree ten it finds zero with five components.  These computations do not
yet prove a uniform theorem, but they show that full block periodicity is a
scalable obstruction and isolate the `d=12` quotient as the first spectral
exception requiring separate analysis.  The parameterized verifier is
`even_second_order_quotient_probe.py`.

## Spectral elimination of the degree-twelve quotient candidate

The exceptional quotient has characteristic polynomial

```text
(X-12)(X-3)(X+3)
```

and therefore trace `12`.  On the 132-dimensional rational complement of
the three component-constant vectors, the matrix identity becomes

```text
A^2 = 11 I - D,
D = A(C15) direct-sum A(C60) direct-sum A(C60).
```

After removing the constant root `2` from each cycle characteristic
polynomial and substituting `11-X^2`, exact factorization over `Q` shows that
every irreducible factor is an even polynomial.  For `C15` the factors have
degrees `2,4,8`; for `C60` they have degrees
`2,2,2,2,4,4,4,8,8,8,16`.  In the combined resolvent every exponent is even.
Unique factorization then forces the characteristic polynomial of the
component-orthogonal restriction of `A` itself to be even, so that restriction
has trace zero.  Adding the quotient trace would give full adjacency trace
`12`, contradicting the zero diagonal of a simple graph.

The exact factorization and rational irreducibility checks are reproducible in
`degree12_spectral_exception.py`.  Lean now contains the reusable final step

```text
Matrix.trace_eq_zero_of_charpoly_eq_expand_two
```

which proves that an even-dimensional rational matrix whose characteristic
polynomial lies in `Q[X^2]` has trace zero.  The remaining formal work for the
candidate is to construct the rational invariant complement and transport the
explicit cycle-resolvent factorization to its characteristic polynomial.

The exact polynomial stage is now kernel-checked rather than merely
reproducible externally.  Lean verifies the degree-twelve `C15` and `C60`
resolvent identities, using `C60 = C4 ∘ C15` to avoid a prohibitively large
normalization.  It also verifies the degree-six `C33` identity and the
triangle identity

```text
(C3 - 2)(5-X^2) = (3-X^2)(X^2-6)^2.
```

## Invariant decomposition and the eleven-triangle frontier

The linear-algebra transport layer is now kernel-checked.  For two
complementary invariant rational subspaces, Lean proves both multiplication
of the restricted characteristic polynomials and additivity of the
restricted traces.

For the all-triangle defect case there is a particularly canonical
decomposition.  If `D^2=D+2I`, then

```text
P = (D+I)/3
```

is idempotent.  Lean now proves that `range P` and `ker P` are complementary,
that `D=2I` on the range and `D=-I` on the kernel, and that every `A`
commuting with `D` preserves both spaces.  It also contains the abstract final
trace contradiction: zero total trace, nonzero plus-space trace, and an even
characteristic polynomial on the kernel are inconsistent.  The remaining
eleven-triangle work is graph-specific: derive `D^2=D+2I`, identify the
plus-space trace as `6`, certify the kernel dimension as `22`, and force its
characteristic polynomial to `(X^2-6)^11` (or otherwise prove it is even).

The first and third of those obligations are now discharged.  Lean proves
that a 2-regular graph whose components all have order three is locally a
union of triangles, and from this proves `D^2=D+2I` over both `Z`, `Q`, and as
a rational endomorphism.  On 33 vertices it also proves that `(D+I)/3` has
trace and rank 11, hence that its kernel has dimension 22.

There is an elementary finite-field route to the remaining quotient trace
that may avoid a general rational canonical-form theorem.  For the
eleven-component quotient, `Q^2=3I+3J` and `QJ=JQ=6J`.  Frobenius invariance
of matrix trace gives, modulo 5 from `Q^5`, and modulo 7 from `Q^7`,

```text
trace(Q) = 6 mod 5,
trace(Q) = 6 mod 7.
```

The diagonal square equations make every quotient entry zero or one, so
`0 <= trace(Q) <= 11`; the two congruences therefore force `trace(Q)=6`.
This entire quotient-trace argument is now kernel-checked, including the
finite-field power identities, Frobenius trace congruences, exact natural
lift, and transport to the actual equitable quotient of the graph.  Equal
triangle-component sizes give quotient symmetry by detailed balance; then
the equality of each row sum with the corresponding diagonal entry of `Q^2`
forces every entry to be at most one.  The component count is no longer an
assumption: the connected-component partition and order-three hypothesis
formally give `33 = 3 * 11`.

Thus, in the eleven-triangle case, the only missing side of the final trace
contradiction is the trace-zero statement on the 22-dimensional kernel of
`(D+I)/3` (equivalently, evenness of its characteristic polynomial).
The same finite-field idea may also replace part of the complement
characteristic-polynomial argument, although an integral basis and a bound
would then be needed.

That trace-zero statement is now kernel-checked.  For a rational matrix `M`
with `M^2=6I`, Lean verifies the determinant identity implying

```text
charpoly(M) divides (X^2-6)^n.
```

It separately verifies that `X^2-6` is irreducible over `Q`.  Unique
factorization and the characteristic-polynomial degree therefore give, in
dimension 22,

```text
charpoly(M) = (X^2-6)^11,
trace(M) = 0.
```

Both matrix and endomorphism forms are available.  The triangle-projection
module now also proves directly that the restriction satisfies `A^2=6I`
from `A^2=5I+J-D`, `JD=2J`, and membership in the `-1` eigenspace of `D`.
Consequently the spectral half of the eleven-triangle contradiction is
complete.

The remaining trace interface is now kernel-checked as well.  Lean reindexes
the ambient diagonal sum over the connected-component dependent sum and
proves, for an equitable partition into components of order three,

```text
trace(A D) = 3 * trace(Q).
```

The finite-field certificate `trace(Q)=6` therefore gives `trace(A D)=18`.
Since `P=(D+I)/3` and `trace(A)=0`, the trace of `A` on `range P` is `6`.
The restriction to the 22-dimensional kernel has trace zero by the quadratic
certificate above, contradicting additivity of trace.  The graph-facing
theorem

```text
no_degreeSix_boundary_of_secondOrder_all_triangles
```

is kernel-checked.  Thus a 33-vertex, minimum-degree-six, `C₄`-free boundary
graph cannot have all second-order defect components of order three.  The
remaining cycle-length multisets are useful tests, but eliminating them one
at a time is not the main route: the proof now pivots back to statements
uniform in the degree.

Two such statements are now kernel-checked.  First, choosing one vertex from
each ordinary connected component gives a common-neighbor-independent set,
because vertices in different components cannot share a neighbor.  Hence

```text
number of connected components of G <= indepNum(commonNeighborConflict G),
```

and every degree-`d` plateau core has strictly fewer than `d` components.
This explains structurally why disconnected-union examples are the natural
barrier to a purely conflict-independence proof, rather than merely supplying
more small cases.

Second, the global cycle factorization now records the number as well as the
lengths of the second-order defect components.  At every even second-order
boundary, the sum of the defect-cycle lengths is odd, the number of even
cycles is even, and consequently the total number of defect components is
odd.  This is degree-uniform and does not enumerate partitions.  A promising
next strengthening is ordinary connectedness at near-Moore order: every
ordinary component should itself contain a Moore ball of at least
`d(d-1)+1` vertices, so order `d(d-1)+3` permits only one component for
`d >= 3`.

That strengthening is now kernel-checked, in a stronger componentwise form:
every ordinary connected component of a `C₄`-free minimum-degree-`d` graph
has at least `d(d-1)+3` vertices.  Consequently a graph at the second strict
Moore boundary has exactly one ordinary connected component.

Connectedness feeds directly into the second-order quotient.  Every original
edge gives a positive entry between the defect components containing its
endpoints.  Lifting an ordinary path through the defect-component map proves
that the positive-entry relation of the quotient is irreducible.  This bridge
is kernel-checked in `Erdos85BoundaryQuotientIrreducible`.

More importantly, periodicity now yields a degree-uniform structural theorem
instead of a list of allowed partitions.  If quotient entry `Q[c,e]` is
positive, then the two defect-cycle orders are comparable under divisibility:

```text
|c| divides |e|  or  |e| divides |c|.
```

For if neither divisibility holds, the rectangular-block periodicity theorem
forces both `Q[c,e]` and `Q[e,c]` to be at most one.  Positivity and detailed
balance make both entries one and then force `|c|=|e|`, a contradiction.
The full graph-facing statement is kernel-checked in
`Erdos85BoundaryQuotientDivisibility`.  Thus the support of the irreducible
quotient lies in the comparability graph of the divisibility poset on defect
cycle lengths.  This is the current general replacement for enumerating
degree-six cycle partitions.

The edge description is sharper when the lengths differ.  If `|c|<|e|`
and `Q[c,e]>0`, then the reverse periodicity bound and detailed balance give

```text
Q[e,c] = 1,
|c| divides |e|,
|c| * Q[c,e] = |e|.
```

Thus every unequal-length quotient edge is completely determined by its two
cycle orders: downward weight one, upward weight the integer length ratio.
This graph-facing strengthening is also kernel-checked.  Only edges between
equal-length cycles retain unconstrained quotient weights.

Subtracting the row-sum identity from the diagonal square identity now gives
the kernel-checked local excess formula

```text
sum_e (Q[c,e] Q[e,c] - Q[c,e]) = |c| - 3.
```

For a component of minimum order, every longer target has zero contribution:
the upward entry is the length ratio and the downward entry is one.  Equal
orders have symmetric quotient entries by detailed balance.  Hence

```text
|c| - 3 = sum_{|e|=|c|} Q[c,e] (Q[c,e] - 1).
```

Every summand on the right is a product of consecutive integers and is even.
It follows, uniformly and without a partition search, that every shortest
second-order defect cycle has odd order.  Both the minimum-component identity
and this oddness theorem are kernel-checked in
`Erdos85BoundaryQuotientExcess`.

The missing handshake constraint from the exploratory classifier is now also
graph-facing and kernel-checked:

```text
Even (|c| * Q[c,c]).
```

It follows by applying the degree-sum theorem to the original graph induced
on the vertices of one defect component; equitability makes that induced
graph `Q[c,c]`-regular.  Since every minimum component has odd order, its
diagonal quotient entry is therefore even.  This eliminates the remaining
equal-order abstract candidates seen in the small quotient probes without
appealing to a Boolean classifier.

As a consistency check rather than a proof step, the known degree-four
15-vertex witness has defect orders `(3,6,6)` and quotient

```text
[0 2 2]
[1 2 1]
[1 1 2].
```

This realizes the new rule exactly: unequal edges have downward weight one
and upward weight equal to the order ratio.  Exact quotient probes at degrees
6, 8, and 10 find no candidate after the divisibility, ratio, and handshake
constraints, suggesting that the degree-four template is the unique small
exception and that a uniform arithmetic obstruction may hold for all even
`d >= 6`.

### Correction: square-parameter quotient families

The probe originally hard-coded `trace(Q)=d`.  That trace equality is valid
after a nonsquare/minimal-polynomial argument, but when `d-3` is a square the
two rational eigenvalues `±sqrt(d-3)` can have unequal multiplicities.  The
probe has been corrected so this trace constraint is optional.

The three-component equations in fact contain an infinite square-parameter
family.  For even `a`, put

```text
d = (a-1)^2 + 3,
r = a(a-1) + 3,
t = (a^2 - 3a + 4)/2.
```

Then orders `(r,rt,rt)` support

```text
[a t t]
[1 e f]
[1 f e],
```

where `{e,f}={t,d-1-t}`; handshake parity selects a branch when `rt` is
odd.  The degree-four and degree-twelve quotients are early members.  The
next is

```text
d=28, orders=(33,363,363),
Q=((6,11,11),(1,16,11),(1,11,16)).
```

Degree 28 also has an equal-order quotient survivor with orders
`(253,253,253)` and diagonal/off-diagonal weights `6/11`.  The old probe
missed these because partial-trace pruning remained active even after the
final trace test was removed; both uses are fixed.  Degree twelve is thus the
first spectral exception, not an isolated one.  A parameterized spectral
theorem is required; finite quotient searches cannot close the even case.

The existence of this obstruction family is now itself kernel-checked in
`Erdos85SquareParameterQuotient`.  Reparameterizing `a=2(k+1)` removes all
natural-number subtraction.  Lean verifies symbolically for every `k`:

```text
d-3 = (2k+1)^2,
sum(component orders) = d(d-1)+3,
every quotient row sums to d,
r_i Q_ij = r_j Q_ji,
Q^2_ij = (d-3) delta_ij + r_j,
Even(r_i Q_ii).
```

Thus the exact quotient equations, the newly formalized divisibility-ratio
rules, and handshake parity are genuinely insufficient for a uniform
contradiction.  The next proof must rule out realization of this abstract
family by the full commuting cycle blocks.  For the small cycle of order
`r=a(a-1)+3`, this amounts to a parameterized version of the degree-twelve
fact that each irreducible factor of the transformed reduced cycle polynomial
is even.  Computations suggest the relevant real-cyclotomic norms are never
squares; establishing that uniformly appears to be the central number-theory
lemma.

### Uniform cycle-cover rigidity

There is a complementary combinatorial route that uses more of the actual
`0/1` cycle blocks.  In the square-parameter three-component family, each
vertex of either long cycle has exactly one neighbour in the short cycle,
while each short-cycle vertex has `t` neighbours in that long cycle.  After
cyclically parametrizing the components, write `f(y)` for the unique short
vertex adjacent to the long vertex `y`.  The block intertwining equation is

```text
e_{f(y)-1} + e_{f(y)+1} = e_{f(y-1)} + e_{f(y+1)}.
```

Since the short cycle has order at least three, its predecessor and successor
are distinct.  Thus every three-term segment of `f` is either consistently
forward or consistently backward.  Adjacent segments cannot reverse
orientation, since that would imply `2=0` in `ZMod r`.  The local orientation
and no-flip lemmas are now kernel-checked in
`Erdos85CycleCoverRigidity`.  The next graph-facing theorem should propagate
this orientation around the long cycle and identify the unequal block as the
standard cyclic covering `ZMod (rt) -> ZMod r`, up to translation and
reflection.

This applies uniformly to every unequal pair of defect-cycle components with
reverse quotient entry one.  Once the cover is normalized, the remaining
long-to-long block and the exact common-neighbour equation become a
parameterized cyclic difference-family problem.  Its Fourier transform
should recover the same spectral obstruction, while its combinatorial form
may admit a direct proof.

The closest published framework is Delorme and Pineda-Villavicencio, *On
graphs with cyclic defect or excess* (2010), arXiv:1010.5841.  Their real
cyclotomic factorization and reducibility obstruction support this method,
but their setting is a single cyclic defect component in a diameter/girth
Moore problem.  It does not directly settle the present three-component
square family or supply the needed uniform norm-nonsquare theorem.

### Literature audit (2026-08-04)

A targeted search under both formulations of the problem gives the following
picture.

* The current Erdős Problems entry still labels Problem 85 open and records no
  claimed partial or complete solution in its comments.  Its October 2025
  revision explicitly adds the weaker bounded-drop question.  The exact
  problem is equivalent to the behaviour of `R(C4,K_{1,n})`, but monotonicity
  of that Ramsey number is not the same statement and does not immediately
  settle minimum-degree monotonicity.
* Luis Boza, *Exact Values and Bounds for Ramsey Numbers of C4 Versus a Star
  Graph* (arXiv:2409.12770), is the most relevant recent paper found.  It
  determines all previously unknown values through star parameter 37, gives
  additional exact values and recurrences, and proves a congruence-family
  upper bound.  Its local triangle count is close in spirit to our boundary
  regularity argument, but it does not address eventual monotonicity.  Its
  theorem for `m = 2 mod 6` excludes a graph one vertex above a related Moore
  boundary and concerns the odd-degree side already covered more generally by
  our defect-spectrum argument.
* Chen's 1997 result proves only the two-step Lipschitz bound
  `R(C4,K_{1,n+1}) <= R(C4,K_{1,n})+2`.  Parsons' block-design bounds and the
  later polarity-graph papers primarily provide upper bounds/exact values and
  constructions.  None classifies the near-Moore boundary graphs needed here.
* Delorme--Pineda-Villavicencio and the broader excess/defect-two literature
  use the same matrix-polynomial/cyclotomic philosophy, but assume the
  diameter/girth Moore setting, usually a single cyclic defect.  Our defect is
  a union of cycles and permits triangles; this is the substantive gap, not a
  change of notation.
* Searches for the exact order `d(d-1)+3`, the matrix identity
  `A^2=(d-1)I+J-D`, and regular `C4`-free defect-cycle graphs found no prior
  general classification.  Recent exact-value computations use finite
  cyclotomic scans of precisely the kind that cannot dispose of our infinite
  square-parameter family.

The audit therefore does not reveal an existing solution we are duplicating.
It does identify two bodies of reusable technique: Boza's local
neighbourhood partition/counting arguments and the reducibility criteria for
cyclic defect/excess graphs.  Our new cyclic-cover/residue-partition reduction
appears to be the missing multi-component refinement connecting them.

#### Literature-audit correction and update (2026-08-05)

The June 12, 2026 revision of Boza's paper is now the version that should be
cited.  It determines the eight formerly unknown star-Ramsey values through
star parameter 38, proves `R(C4,K_{1,27})=33`,
`R(C4,K_{1,n})=n+7` for `28 <= n <= 33` and `n=37`, and gives the functional
inequalities stated there.  Its concluding table reports strict growth over
the settled initial range, but no eventual-monotonicity theorem.

More importantly, the order `d(d-1)+3` is exactly Moore bound plus two for a
*triangle-free* `d`-regular graph of girth five.  That narrower class is
standardly called a graph of type `(d,5,2)`, or a girth-five graph of excess
two.  The excess-two literature already proves regularity and obtains a
2-regular excess graph together with the commuting adjacency-matrix
identity; it also applies cyclotomic irreducibility and parity obstructions.
Consequently those ingredients cannot be advertised as new.

This does not subsume our boundary problem: Erdős 85 forbids `C4` but permits
triangles.  In our identity the 2-factor records both adjacency pairs lying in
no triangle and nonadjacent pairs with no common neighbour.  It is therefore
a genuine extension of the classical girth-five excess graph, not itself an
ordinary `(d,5,2)` graph.  The classical results remain directly applicable
to the triangle-free terminal branch and should be invoked there rather than
reproved.

The most relevant older sources located are Delorme--Pineda-Villavicencio,
*On graphs with cyclic defect or excess* (EJC 2010), and the subsequent paper
*On graphs with excess or defect 2* (Discrete Applied Mathematics 2015),
which explicitly attributes the girth-five odd-degree criterion to Kovacs.
Their published scope is spectral nonexistence for various degrees/girths,
not the triangle-permitting boundary classification or a descent proving
eventual monotonicity.  Thus the general target remains open, but our novelty
claim must be phrased as the triangle-permitting/multi-component refinement
and, ultimately, its monotonicity consequence.

### Characteristic-two obstruction and minimum-layer descent

The anticipated cyclotomic norm calculation is unnecessary for the explicit
square family. Normalizing both short-to-long blocks as cyclic covers makes
each Gram matrix equal to `t I`, and the short-short block becomes
`H^2 = (a-1) I + J - C_r`, where `r=a(a-1)+3`.

Every zero-diagonal self-intertwiner of an odd cycle is translation invariant,
so `H` is a circulant with binary connection function `s : ZMod r -> Nat`.
Its ordered differences occur once at every residue except `0,+1,-1`.
Modulo two, Frobenius sends its square to the doubled support. Doubling
permutes `ZMod r`, so the two sides have support cardinalities `a` and
`r-3=a(a-1)`, an impossibility for `a>=4`. This uniform argument is
kernel-checked in `Erdos85CyclicParityObstruction`; translation rigidity is
kernel-checked in `Erdos85CycleCoverRigidity`.

The block calculation has a broader structural consequence. Restrict to the
union of all minimum-length defect cycles. Every excursion to a longer cycle
is a cyclic cover with reverse degree one, hence has scalar Gram contribution.
If `b` is the degree retained inside the minimum layer, restriction gives
`H^2 = (b-1) I + J - D_min`. Thus the minimum layer is itself a smaller
second-boundary object of order `b(b-1)+3`; if a longer component exists,
irreducibility gives `b<d`. The general matrix step is kernel-checked as
`minimumLayer_square_descent` in `Erdos85SquareFamilyDescent`.

Consequently the remaining obstruction is no longer an enumeration of
quotient survivors. Infinite descent reduces a hypothetical graph to the
terminal case in which all defect cycles have the same odd length. For `m`
cycles of length `r`, the symmetric quotient satisfies
`Q 1 = d 1`, `Q^2 = (d-3) I + r J`, and `mr=d(d-1)+3`.
The associated matrix-valued cyclic difference family is now the central
unresolved classification problem.

### Equal-cycle binary block rigidity

One subtlety in the terminal case is essential: a rectangular block commuting
with an odd-cycle adjacency matrix need not be circulant over a general
coefficient ring. Its discrete d'Alembert form is
`B(x,y)=f(y-x)+g(y+x)`, so it may contain both a travelling and a reflected
wave. Consequently a naive `m`-dimensional Fourier restriction, and the claim
that odd `m` immediately forces a cyclotomic square, are not valid before the
binary structure is used.

For a `0/1` block, however, the two waves cannot both be nonconstant. Under
the odd-cycle coordinate bijection `(x,y) -> (y-x,y+x)`, all sums
`f(u)+g(v)` are binary. If both functions varied, a two-by-two additive
rectangle would have to be one of the crossed binary patterns, contradicting
the rectangle identity. Thus every nonzero equal-cycle block is either
circulant or reverse-circulant. The additive-rectangle dichotomy and the
orientation conclusion from a d'Alembert decomposition are kernel-checked in
`Erdos85BinaryCycleIntertwiner`.

The remaining step is to formalize the d'Alembert decomposition from the
cycle recurrence and then exploit compatibility of the block orientations.
Products occurring in an off-diagonal square block partition the all-ones
matrix. A nonempty circulant support intersects every nonempty
reverse-circulant support when the cycle order is odd, so all nonzero
two-block products in a fixed off-diagonal equation must have the same
orientation. This converts the terminal object into a signed quotient / gain
graph with a strong same-sign two-walk condition. It is the correct global
replacement for the invalid assumption that all blocks can immediately be
oriented circulantly.

The d'Alembert decomposition itself is now also kernel-checked: invariance of
a function on `ZMod r` under translation by two implies constancy for odd
`r`, and the cycle rectangle recurrence then integrates to `f(u)+g(v)`.
Together with the binary rectangle lemma this gives the complete abstract
binary block rigidity theorem, modulo only the routine coordinate bridge from
the graph block recurrence.

### Triangle terminal case and divisible design graphs

A further literature search identified the terminal case `r=3` with a
standard object. Since a 3-cycle makes every two distinct vertices in one
defect class have zero common neighbours, while vertices in different classes
have one, the graph is a divisible design graph with parameters

```text
(v,k,lambda1,lambda2,m,n)
= (d^2-d+3, d, 0, 1, (d^2-d+3)/3, 3).
```

Panasenko--Shalaginov's classification through 39 vertices explicitly
contains `(15,4,0,1,5,3)`, the line graph of the Petersen graph. Thus the
triangle terminal case is genuinely realizable at `d=4`; a blanket terminal
nonexistence claim would be false. Their table does not contain the candidate
`(33,6,0,1,11,3)`, agreeing with the independent degree-six obstruction in
this development. The DDG feasibility and construction literature is now a
necessary input for deciding whether this parameter family can persist for
large even `d`, and for understanding what replacement/extension operation is
available when it does.

The standard DDG trace condition initially says that `d` or `d-3` must be a
square, but the zero diagonal of the component quotient is much stronger here.
For a triangle row the local excess is zero, so equality of the first and
second row moments forces every quotient entry to be binary. Handshake parity
then makes every diagonal entry zero. Thus the quotient has trace zero and

```text
Q^2 = (d-3) I + 3 J.
```

If `d-3` were nonsquare, its conjugate eigenvalues would have equal
multiplicity and the quotient trace would be the uncancelled principal
eigenvalue `d`, contradiction. Hence `d-3=t^2`. Trace zero then gives `t|d`;
as `d=t^2+3`, one has `t|3`, leaving only `d=4` and `d=12`. Therefore no
triangle terminal exists at any even degree `d>=14`. The binary-moment lemma
and terminal arithmetic `d=4 or d=12` are kernel-checked in
`Erdos85TriangleTerminal`. The graph-facing spectral bridge remains to be
packaged, but the uniform mathematical classification is now clear.

The first graph-facing half is now packaged as well. Lean proves directly
from detailed balance, the quotient square equation, and the row sum that if
all defect components have order three then every quotient entry is at most
one. Combining this with the already checked handshake parity proves every
quotient diagonal entry is zero. These are
`secondOrder_triangleComponents_quotient_le_one` and
`secondOrder_triangleComponents_quotient_diagonal_zero` in
`Erdos85TriangleTerminal`. What remains for the fully checked `d=4 or 12`
theorem is only the rational spectral-conjugacy bridge from
`Q^2=(d-3)I+3J` and `trace Q=0`.

That spectral bridge is now available in parameter-uniform form. For every
nonsquare natural `c`, Lean proves that a rational matrix satisfying `M^2=cI`
has trace zero; equivalently its characteristic polynomial is a power of the
irreducible quadratic `X^2-c`. The endomorphism version and an abstract
complementary-subspace theorem show that zero total trace plus nonzero trace
on the constant space force `c` to be a square. These results are
kernel-checked in `Erdos85QuadraticTrace`. Instantiating its projection with
the all-ones quotient projection will complete the fully graph-facing
triangle classification.

The instantiation is now complete. `Erdos85TriangleTerminal` constructs the
normalized all-ones projection, proves its range and kernel trace identities,
casts the natural component quotient to `ℚ`, derives symmetry, both constant
sum identities, trace zero and the full square equation, and proves that the
zero-sum kernel is nontrivial from the exact component count. The resulting
graph-facing theorem is
`secondOrder_triangleComponents_degree_eq_four_or_twelve`.

### A uniform route through the equal-cycle orientation system

The signed orientation quotient appears substantially more rigid once the
*multiplicity* of two-step component paths is used. A pair of base components
cannot have a unique nonzero intermediate component. If it did, two regular
binary cyclic blocks of degrees `a,b` would have product `J_r`, so their
connection sets would factor `ZMod r` uniquely and `ab=r`. The `C4` bound
makes both connection sets Sidon: their nonzero ordered differences are all
distinct. Unique factorization also makes the two difference sets disjoint,
and hence

```text
a(a-1) + b(b-1) <= r-1 = ab-1.
```

This is impossible for `a,b>=2`; if one degree is one, the other is `r`,
which itself violates the Sidon bound for `r>=3`. Thus every pair of distinct
base components has at least two nonzero two-step intermediates.

The additive-combinatorial bridge is now kernel-checked in
`Erdos85UniqueSidonFactor`.  For finite connection sets `A,B` in an arbitrary
finite additive commutative group, it defines the ordered nonzero difference
sets, proves their exact sizes under the Sidon condition, proves that unique
`A+B` representation makes the two difference sets disjoint, and derives
nonexistence from `|A||B|=|Z|`.  The remaining graph-facing step is to extract
these connection sets from the two same-orientation cyclic blocks and derive
Sidonicity and unique representation from `C4`-freeness and the single
intermediate block-product equation.

That bridge has now been strengthened to the graph-facing circulant-block
form.  The checked theorem
`isOrderedSidon_of_c4Free_circulantBlock` turns a repeated ordered difference
directly into two distinct common neighbours of two distinct parametrized
vertices, hence a forbidden `C4`.  The theorem
`unique_pair_sums_of_convolution_card_eq_one` converts entrywise convolution
count one into unique additive representation.  Combining them,
`no_circulant_block_convolution_one` rules out two binary circulant blocks in
a `C4`-free graph whose convolution is identically one, uniformly over every
finite additive commutative coordinate group of order at least three.

Thus the only remaining boundary-specific work for the unique-intermediate
claim is bookkeeping: obtain the three common `ZMod r` parametrizations and
the convolution-cardinality equation from the actual component block of
`A^2=(d-1)I+J-D`.  No additional combinatorial or arithmetic case analysis is
needed.

The orientation bookkeeping has also now been made uniform and checked.
`binary_oddCycleIntertwiner_orientation` proves directly that every binary
matrix intertwining two equal odd cycles is circulant or reverse-circulant.
Its proof constructs the inverse-of-two coordinate change and feeds the
cycle recurrence into the discrete d'Alembert decomposition; it no longer
requires an externally assumed decomposition.  The graph wrapper
`graph_equalOddCycleBlock_orientation` obtains that recurrence from `AD=DA`
and the two cycle parametrizations.  Finally,
`exists_connectionSet_of_translationInvariantBlock` extracts the actual
finite cyclic connection set from the circulant branch.  Consequently the
remaining instantiation only needs (i) coordinate reflection in the common
reverse/reverse branch and (ii) the entrywise isolation of the unique
intermediate summand in the global square equation.

Both pieces have now advanced.  Four checked reflection identities show
exactly how source or target negation toggles circulant and
reverse-circulant blocks, so the two blocks can be normalized successively
without an orientation case surviving in the final statement.  More
substantively, the new graph-facing theorem
`secondOrder_unique_common_neighbor_in_only_intermediate` is checked in
`Erdos85UniqueIntermediateBoundary`: for distinct defect components `c,e`,
the off-diagonal square identity gives a unique common `G`-neighbor; if `k`
is the only quotient component with positive entries on both sides, that
neighbor lies in `k`.  The proof uses quotient equitability to exclude every
other component, not an enumeration of vertices or cycles.

What remains to finish the unique-intermediate contradiction is now only the
final coordinate assembly: choose the three equal-cycle parametrizations,
normalize their two block orientations by the checked reflections, extract
the two connection sets, transport the unique middle vertex to a unique
middle coordinate, and invoke `no_unique_middle_circulant_blocks`.

Together with the already proved fact that all contributions to a fixed
off-diagonal square block have the same orientation, this initially suggested
that the signed support graph might be switching-equivalent either to the
all-positive (circulant) signing or to the all-negative (reverse-circulant)
signing. **That purely signed inference is false.** A signed windmill can have
different triangle signs while satisfying the same-sign condition whenever a
two-walk exists, and duplicating each base vertex makes every pair have at
least two intermediates without repairing the imbalance. Thus multiplicity
of intermediates, by itself, is insufficient. Any valid switching theorem
must use the full quotient weights/Sidon geometry, not merely signed support.
The two branches below remain useful conditional obstructions, but they are
not yet an exhaustive dichotomy.

The two uniform terminal branches then have sharp algebraic obstructions.

* In the all-reverse branch, every diagonal block is zero: a
  reverse-circulant block has form `s(x+y)`, and its diagonal values sample
  every residue because doubling is invertible for odd `r`. Over
  characteristic two, evaluating the block group-algebra matrix at a
  nontrivial `r`-th root `zeta` gives an odd-order symmetric zero-diagonal
  (hence alternating) matrix `S(zeta)`. It is singular, while the square
  identity gives
  `S(zeta) S(zeta^-1) = (1+zeta+zeta^-1) I`. Therefore every nontrivial
  `r`-th root satisfies `1+zeta+zeta^-1=0`, so it has order three. This forces
  `r=3` and rules out the reverse branch uniformly for `r>=5`.

* In the all-circulant branch, Fourier evaluation over characteristic zero
  gives a Hermitian `m x m` matrix, where
  `m=(d(d-1)+3)/r` is odd, whose square is
  `(d-1-zeta-zeta^-1)I`. Taking determinants forces the real cyclotomic norm
  factor
  `P_s(d-1)` to be a square, where `r=2s+1` and
  `P_0=1`, `P_1=x+1`, `P_s=x P_{s-1}-P_{s-2}` (equivalently
  `P_s(x)=U_s(x/2)+U_{s-1}(x/2)`). Computation over all admissible parameters
  through `d=200`, and more broadly for odd `x`, finds no square for
  `x>=3,s>=2`. The remaining mathematical target is a uniform nonsquare
  theorem for this Lehmer/Chebyshev sequence, preferably an elementary
square-sandwich or Jacobi-symbol proof. This is now the precise arithmetic
bottleneck rather than a family of cycle-length cases.

## Recovery and aggregate difference packing (2026-08-05)

After the external-volume interruption, the orientation-free final assembly
in `Erdos85UniqueIntermediateBoundary` was checked directly.  The theorem
`secondOrder_no_only_intermediate_of_equalOddCycleParams` passes Lean: all
four apparent orientation combinations are absorbed by coordinate
reflections, and the unique-intermediate Sidon obstruction therefore holds
without an orientation hypothesis.  The earlier long wait was an I/O failure,
not an elaboration problem.

The more general direction is now formalized in
`Erdos85DifferencePacking`.  Fix one cyclic source component and normalize
each of an arbitrary family of target blocks independently to circulant
coordinates.  If two target connection sets shared a nonzero ordered
difference, the corresponding two source vertices would have two common
neighbours lying in distinct target components, contradicting `C4`-freeness.
Consequently all target ordered-difference sets are pairwise disjoint.  Since
each block is Sidon, the checked aggregate inequality is

`sum_k |A_k| (|A_k|-1) <= r-1`.

Combining this packing with the minimum-component local-excess equality
`sum_k q_ik(q_ik-1)=r-3` leaves exactly two unused nonzero residues.  The
abstract two-hole conclusion is also checked in Lean as
`card_unused_orderedDifferences_eq_two`.  This avoids enumerating quotient
rows: the next target is to identify how the two-hole complements for
different source components transform under the block orientations and the
off-diagonal square equations.  That linked difference-family geometry is
the leading route to a global mixed-orientation obstruction.

The two holes are now identified, not merely counted.  In actual defect-cycle
coordinates, displacement `1` cannot occur in any target connection set's
ordered differences: it would give consecutive defect vertices a common
`G`-neighbour, contradicting the zero entry prescribed by the global square
identity.  Negation symmetry gives the same for `-1`, and the two-hole count
then proves that the leave is exactly `{1,-1}`.  The checked graph-facing
theorem is
`unusedOrderedDifferences_eq_one_negOne_of_secondOrder_cycleBlocks`.

Undirected diagonal blocks give another uniform restriction.  A circulant
self-block has a negation-closed support.  Any negation-closed ordered Sidon
set contains at most one inverse pair: the pairs `(a,b)` and `(-b,-a)` have
the same ordered difference.  A reverse-circulant self-block on an odd cycle
is zero by looplessness.  Hence every diagonal entry of the equal-odd-cycle
component quotient is at most two; this is checked as
`secondOrder_equalOddCycleComponent_diagonal_le_two`.

Finally, `Erdos85EqualCycleTerminal` now packages the complementary spectral
bound.  For a rational quotient satisfying
`Q^2=(d-3)I+kJ` with row and column sum `d`, if `d-3` is nonsquare then the
zero-sum restriction has trace zero, so `trace(Q)=d`.  Combining this with
the diagonal bound gives `d <= 2m`, where `m` is the number of common-length
components.  Since `mr=d(d-1)+3`, this bounds the common cycle length by
roughly `2d` in the nonsquare branch without enumerating quotient rows.

The design-theory search found the right general vocabulary (cyclic
difference packings and linked systems of designs), but no theorem that
directly rules out this linked variable-block-size system with leave a cycle.
The classical excess/defect-two literature uses related commuting-cycle
matrix equations, but its standard orders (`d^2+3` or `d^2-1`) and equations
differ from the present `d(d-1)+3` boundary.  It supplies useful spectral
templates, not a ready-made resolution.

The off-diagonal normalization has now been isolated abstractly in
`Erdos85TaggedFactorization`.  Once a fixed source--target pair is oriented,
the intermediate channels produce a dependent tagged type
`Sigma k, A_k x B_k`; unique common neighbours identify its addition map
bijectively with `ZMod r`.  The checked consequences are

* `sum_k |A_k||B_k|=r`;
* each channel addition map is injective;
* sumsets from distinct tags are disjoint; and
* within each tag, the two ordered-difference sets are disjoint.

For the graph-facing application, all active channels can indeed be put in
this form simultaneously.  Each two-block product is circulant or
reverse-circulant.  Opposite product orientations cannot coexist in the
same binary off-diagonal square block.  Reflect the target once if their
common product orientation is reverse, then reflect each intermediate cycle
as necessary to make its first block circulant; the second block becomes
circulant automatically.  The remaining formalization task is to package
this normalization together with the unique common-neighbour theorem.

The relevant additive-design terminology is close to generalized/strong
external difference families, but the present object is more rigid and
linked: every row is an internal cyclic difference packing with leave
`{+/-1}`, while every pair of rows gives a unique tagged sum factorization.
No searched result directly classifies that combination.
### Tagged boundary and per-channel leave bound (verified 2026-08-05)

The graph-facing coordinate bridge is now formalized in
`Proofs/Erdos85TaggedBoundary.lean`.  For two distinct defect components,
after parametrizing every component by the common cyclic coordinate type,
every source--target coordinate pair has a unique intermediate
`(component, coordinate)` tag.  The proof uses the off-diagonal entry of the
second-order square identity and component support disjointness; the file
passes Lean.

In `Proofs/Erdos85TaggedFactorization.lean`, unique tagged sums together with
the canonical leave `{1,-1}` gives, in every channel `k`,

`|Diff(A_k)| + |Diff(B_k)| <= r - 3`,

and hence for Sidon channel supports

`a_k(a_k-1) + b_k(b_k-1) <= r - 3`.

These statements are Lean-verified.  The cardinal inequality alone is not
yet terminal: each row already has total quadratic excess `r-3`, so the
real additional content is the *setwise disjointness* of the two channel
difference sets.  The next useful abstraction should retain that geometry,
most naturally as a group-ring/Fourier identity after orientation
normalization, rather than reduce immediately to scalar inequalities.

### Symmetric difference-array breakthrough

There is a stronger way to retain the setwise geometry.  Write `D_ij` for
the ordered-difference set of the cyclic connection set in block `(i,j)`.
The canonical leave says that every row partitions

`R = ZMod r \ {0,1,-1}`.

The tagged off-diagonal uniqueness says that, for fixed target `j`, the
sets `D_ij` belonging to different sources are pairwise disjoint; the
quotient square equation gives the matching total cardinality `r-3`, so
every column partitions `R` as well.  Transposing a graph block only negates
or reflects its connection set, neither of which changes its *ordered*
difference set.  Hence `D_ij=D_ji`.

Fix `delta in R`.  Unique occurrence in each row defines a permutation
`pi_delta` by `delta in D_(i,pi_delta(i))`.  Symmetry and row uniqueness give
`pi_delta^2=1`.  The number `m` of equal odd defect components is odd, so
this involution has a fixed point.  Therefore every allowed difference
occurs in some diagonal block.  It follows that

`r-3 <= sum_i |D_ii|`.

In the nonsquare branch, the trace identity and the diagonal bound sharpen
to exactly `d/2` diagonal quotient entries equal to two.  Each corresponding
Sidon self-block has exactly two ordered differences, and the other
diagonal blocks have none.  Consequently

`r-3 <= d`, i.e. `r <= d+3`.

The abstract involution argument and its cardinal corollary are now
Lean-verified in `Proofs/Erdos85DifferenceArray.lean`; the exact count of
diagonal-two entries is Lean-verified in
`Proofs/Erdos85EqualCycleTerminal.lean`.  The remaining work is the
graph-facing construction of the symmetric array, especially making the
transpose-invariance and column uniqueness independent of coordinate
reflection choices.  This is a general structural reduction, not a cycle
length enumeration.

### Orientation-free graph assembly completed

The previously remaining graph construction is now Lean-verified.  The
canonical support of a block is defined intrinsically as its zero-row
support.  A circulant transpose negates this support, while a
reverse-circulant transpose preserves it; ordered differences are invariant
under negation.  Thus the difference array is symmetric without any global
switching or balanced-sign hypothesis.

The same zero-row device gives orientation-free graph theorems asserting
that every block support is Sidon, omits difference `1`, and that distinct
targets out of a common source have disjoint ordered-difference sets.  The
four local orientation combinations are absorbed by reflecting only the
relevant target parametrization.  These facts feed a new purely
combinatorial packing lemma and prove the canonical leave `{1,-1}` directly
for the intrinsic graph supports.

Files added or strengthened:

* `Erdos85ZeroRowDifference.lean`: reflection/Sidon/forbidden-step/pairwise
  packing and intrinsic graph canonical leave;
* `Erdos85DifferenceArray.lean`: full abstract terminal theorem and diagonal
  trace-to-difference-mass lemma;
* `Erdos85DifferenceArrayBoundary.lean`: graph-facing assembly proving
  `r <= d+3` from the standard equal-cycle quotient excess, odd component
  count, and diagonal mass, plus the exact equality between zero-row support
  cardinality and the component quotient entry.

All targeted files build successfully.  Consequently the tagged
factorization is no longer needed merely to establish `r<=d+3`; its stronger
sumset information remains available for the eventual contradiction.

There is also a further parity refinement not yet formalized.  For each
allowed difference `delta`, the induced permutation of components is an
involution, hence has an odd number of fixed points.  Since `delta` and
`-delta` induce the same involution and each nonzero diagonal block accounts
for one negative pair, the exact diagonal count predicts

`d/2 == (r-3)/2 (mod 2)`, equivalently `r == d+3 (mod 4)`.

This congruence alone does not eliminate the remaining divisors of
`d(d-1)+3`; computational inspection confirms that infinitely patterned
arithmetic candidates remain.  The terminal step must therefore exploit
more of the involution factorization or the tagged sumsets, rather than only
the scalar bound and divisibility.

### Fully assembled nonsquare graph theorem

The quotient bridge is now complete.  `Erdos85DifferenceArrayBoundary.lean`
proves:

* zero-row support cardinality equals the corresponding component quotient
  entry;
* the equal-order rational quotient is symmetric and satisfies
  `Q^2=(d-3)I+rJ`;
* when `d-3` is nonsquare, its trace is `d`;
* the local quotient square identity gives every row's exact excess `r-3`;
* even diagonal quotient entries, the bound `q_ii<=2`, Sidonicity, and trace
  `d` give total diagonal ordered-difference mass exactly `d`.

These are assembled in the checked theorem
`secondOrder_equalOddCycle_length_le_degree_add_three_of_nonsquare`, which
starts from the actual graph boundary hypotheses and a parametrization of
all common odd defect cycles and concludes `r<=d+3`.  No anonymous excess,
diagonal-mass, orientation, or quotient-trace assumptions remain.

A literature search located partitioned difference families, starters,
Howell designs, and frame difference families as neighboring objects.  Their
broad existence theory is evidence that the symmetric difference array by
itself should not be expected to contradict existence.  The next terminal
argument should combine its involution factorization with the rigid quotient
square equation or with the unique tagged sumsets.

### Fourier norm polynomial: structural identification and modular tests

Write `r=2s+1`, `x=d-1`, and define

`P_0=1`, `P_1=x+1`, `P_s=x P_{s-1}-P_{s-2}`.

This is the dilated Chebyshev polynomial of the fourth kind,

`P_s(x)=W_s(x/2)=sin((2s+1)theta/2)/sin(theta/2)` for `x=2 cos(theta)`.

Equivalently it is the odd Dirichlet-kernel polynomial and has the real
cyclotomic factorization

`P_s(x)=prod_{e | (2s+1), e>1} Psi_e(x)`.

The paper Hone--Jeffery--Selcoe, *On a Family of Sequences Related to
Chebyshev Polynomials*, J. Integer Sequences 21 (2018), Article 18.7.2,
studies exactly these polynomials (their `s_k(n)`).  It supplies the Lehmer
sequence interpretation, cyclotomic factorizations, and the useful exact
floor formula

`P_s(x)=floor(lambda^(s+1)/(lambda-1))`,

where `lambda=(x+sqrt(x^2-4))/2`, for `x>5/2`.  It does not state the
perfect-square nonexistence needed here.

Two special-value congruences are particularly clean:

* `P_s(x) = 2s+1 (mod x-2)`, because `P_s(2)=2s+1`;
* `P_s(x) = (-1)^s (mod x+2)`, because `P_s(-2)=(-1)^s`.

The second formula corrects an earlier exploratory calculation which had
incorrectly inserted a factor `2s+1` at `x=-2`.  Also `P_s(x)` modulo `x`
cycles as `1,1,-1,-1` with period four.  Consequently, if `x` is odd and
`P_s(x)` is a square, elementary nonresiduacity of `-1` gives:

* for odd `s`, necessarily `x=3 (mod 4)`;
* for `s=2 (mod 4)`, necessarily `x=1 (mod 4)`;
* `s=3 (mod 4)` is impossible (use `x+2` when `x=1 mod 4`, and `x`
  when `x=3 mod 4`).

Thus the real-cyclotomic norm is automatically nonsquare when
`r=7 (mod 8)`.  These congruences are uniform, but the remaining residue
classes occur among the admissible divisors `r | x^2+x+3`, so they do not
by themselves close the argument.

The difference-array parity refinement admits a useful arithmetic
parameterization.  If

`r = d+3-4a`,

then `a` is exactly half the surplus number of diagonal anchors (or the sum
of `(f_delta-1)/2` over representatives of the pairs `{delta,-delta}`).
The divisibility `r | d(d-1)+3` becomes

`r | 16a^2-28a+15`.

In particular `a=1` is impossible (for `r>=5`) and `a=0` forces `r | 15`.
An earlier scratch calculation incorrectly factored this remainder as
`(4a-3)(4a-5)`; the displayed quadratic is the corrected identity.  A terminal
combinatorial bound `a<=1` would therefore reduce the whole branch to the
two tiny divisors `r=5,15`; obtaining such a bound, rather than enumerating
quotient rows, is now a promising alternative to the square-value theorem.

### Prime-order Fourier correction and the order-five branch

For composite `r`, nonsquareness of the total Dirichlet-kernel value
`P_{(r-1)/2}(x)` is not by itself enough: that value is a product of the
norms belonging to all orders dividing `r`, whereas Fourier inversion would
need control of the relevant character orbit.  The correct reduction is
prime-order.  If `p | r` is prime, evaluate on characters of order `p`.
Nonsquareness of

`P_{(p-1)/2}(x) = Norm(x-zeta_p-zeta_p^{-1})`

forces trace zero throughout that Galois orbit.  The diagonal-anchor
multiset is then uniform after projection `Z/r -> Z/p`, so `p | d`.  Since
also `p | r | d(d-1)+3`, this forces `p | 3`.  Therefore any prime divisor
`p>=5` for which this norm is proved nonsquare eliminates the entire cycle
parameter `r`.

The first case is completely elementary and Lean-verified in
`Erdos85DifferenceArrayArithmetic`:

`P_2(x)=x^2+x-1`

lies strictly between `x^2` and `(x+1)^2` for `x>=2`.  Thus every branch
with `5 | r` is eliminated once the prime-order Fourier bridge is
formalized.

McDaniel's *Square Lehmer Numbers* (Colloq. Math. 66 (1993), 85--93)
studies the representation

`P_s(x)=U_{2s+1}(sqrt(x+2),1)`.

Its strongest square classification assumes congruence classes of the
Lehmer parameter `Q` not containing our `Q=1` first-sequence case; the paper
explicitly notes that the remaining parameter classes require a different
approach.  It is therefore useful methodology, but not a theorem that can
be cited to close our norm problem.

The primitive order-nine norm is also uniformly nonsquare.  For `x=2v+3`,

`P_4(x)=x^4+x^3-3x^2-2x+1`

has the exact form

`A^2+B`, where `A=4v^2+13v+8`, `B=7v^2+22v+12`,

and `(A+1)^2-P_4(x)=v^2+4v+5>0`.  Hence it lies strictly between
consecutive squares.  This sandwich and its identification with `P_4` are
Lean-verified in `Erdos85DifferenceArrayArithmetic`.

This closes every `9 | r` branch at the arithmetic level.  Primitive
order-nine trace vanishing makes the projected anchor counts constant on
each residue class modulo three, hence `3 | d`.  If `d` is a square, then
`9 | d`; if `d` is nonsquare, order-three trace vanishing makes the full
mod-nine projection uniform and again gives `9 | d`.  But then
`d(d-1)+3 = 3 (mod 9)`, contradicting `9 | r | d(d-1)+3`.  The final
dichotomy is Lean-verified as `orderNine_boundary_contradiction`; the
remaining formal task is the Fourier-to-uniformity bridge.

There was also a tempting proposed global-orientation propagation from the
nonzero diagonal anchors.  The local theorem
`oddCycle_no_disjoint_opposite_orientations` does prove that all two-step
contributions to a fixed source--target block have one product orientation.
However, an abstract signed-support search produces odd unbalanced sign
systems satisfying this local condition even in the presence of loops.
Thus a global all-circulant normalization does not follow from that local
lemma alone; any such argument must use the numerical quotient equation,
not just support and orientation consistency.

### Terminal prime-frequency dichotomy: the square branch also contradicts parity

The apparent need for a uniform Lehmer nonsquare theorem can be removed.
Fix a prime `p | r` and a primitive `p`-th root `zeta`, and put

`lambda = x-zeta-zeta^-1`, with `x=d-1`.

Let `c_h` be the number of diagonal-anchor support elements whose cyclic
coordinate projects to `h in Z/p`, and `H(zeta)=sum_h c_h zeta^h`.  The
mixed frequency-pair operator has square `lambda I` and trace `2H(zeta)`.

* If `lambda` is nonsquare in the real cyclotomic field, its trace is zero.
  Prime cyclotomic irreducibility makes all `c_h` equal, hence `p | d`;
  together with `p | d(d-1)+3`, this forces `p=3`.
* If `lambda` is a square, diagonalization gives
  `2H=2u sqrt(lambda)` for an integer `u` (the half-difference of the two
  eigenvalue multiplicities).  Hence

  `H(zeta)^2 = u^2 (x-zeta-zeta^-1)`.

  Applying prime cyclotomic irreducibility to this Laurent-polynomial
  identity says that the cyclic convolution `c*c` is constant at all
  residues other than `0,+1,-1`.

The symmetric difference array supplies an incompatible mod-two pattern.
For a projected ordered difference `b`, the number of its lifts in
`Z/r \ {0,+1,-1}` is odd unless `b` is `0,+1,-1`, when it is even.  Every
diagonal two-set is `{h,-h}` and has ordered differences `{2h,-2h}`.
Since doubling is invertible modulo odd `p`, this gives

`c_h odd  <=>  h notin {0,+1/2,-1/2}`.

Write `b_h` for this zero-one parity pattern.  Cyclic convolution modulo
four depends only on parity:

`(c*c)(t) = (b*b)(t) (mod 4)`.

Indeed `c=b+2e`, and the two cross-convolutions agree, so their contribution
is a multiple of four.  If `E={0,+a,-a}` with `a=1/2`, then

`(b*b)(t)=p-6+#{(e,f) in E^2 : e+f=t}`.

Thus at `t=a` (which is not `0,+1,-1`) the value is `p-4`, while at any
`g` outside `{0,+a,-a,+1,-1}` it is `p-6`.  They differ by two modulo four,
contradicting the convolution constancy.  Such `g` exists for every
`p>=7` because the excluded set has five elements.

Consequently every prime `p>=7` divisor of `r` is impossible in both the
square and nonsquare cyclotomic branches.  Prime five is handled by the
verified order-five norm sandwich, and powers of three by the verified
order-nine argument.  This is now the leading terminal route for the whole
equal odd-cycle branch; unlike the earlier norm plan, it uses the full
difference-array parity and requires no unproved classification of square
Lehmer values.
# 2026-08-05 recovery checkpoint: mod-four branch verified

The generic parity engine for the square-cyclotomic branch is now checked by
Lean in `Erdos85CyclicConvolutionParity.lean`.  In particular, on any finite
abelian group,

```text
c = b + 2e  ==>  (c*c)(t) = (b*b)(t) (mod 4).
```

The terminal wrapper is also formalized: constancy of `c*c` at two residues
is impossible if the corresponding values of `b*b` differ by two modulo
four.  Consequently the remaining `p >= 7` task is cleanly separated into
two structural lemmas: the projected-anchor parity pattern is the complement
of `{0, +/-1/2}`, and that three-hole pattern has convolution values `p-4`
and `p-6` at suitable nonspecial residues.  No enumeration by prime is
needed.

The entire finite cyclic calculation is now formalized in
`Erdos85PrimeConvolutionObstruction.lean`.  For every modulus `p >= 7` and
every `a` with `2a=1`, Lean verifies:

* `{0,a,-a}` has three elements;
* its indicator convolution is `2` at `a`;
* a residue outside the five-element sumset `{0,a,-a,1,-1}` exists;
* its indicator convolution is `0` there; and
* therefore no integral multiplicity with the complementary parity pattern
  can have constant self-convolution at these nonspecial residues.

`Erdos85ProjectedMultiplicityParity.lean` now supplies the next bridge in an
abstract, reusable form.  An odd-cardinality-fiber projection preserves a
pulled-back parity pattern, and the resulting natural multiplicity is
automatically written as `b+2e`.  Its final theorem reduces the full square
branch to exactly three graph-facing inputs: odd quotient fibers, the base
anchor parity pattern, and convolution constancy.  Thus no arithmetic or
mod-four work remains hidden in the graph layer.

## 2026-08-05: parity bridge strengthened and made graph-facing

The earlier thought that exact diagonal coverage was needed was unnecessarily
restrictive.  For a fixed allowed difference, row uniqueness defines an
involution on the component indices.  Its non-fixed indices occur in pairs,
so an odd component set has an **odd number of fixed indices**, not merely at
least one.  These fixed indices are exactly the diagonal blocks carrying the
difference.  This survives arbitrary diagonal surplus.

This refinement is now Lean-verified in
`Erdos85DifferenceArrayParity.lean`, including the iff statement: the
diagonal occurrence count is odd exactly for differences outside
`{0,+/-1}`, and is zero for the forbidden differences.

The graph translation is also complete and checked:

* `Erdos85GraphDiagonalAnchor.lean` proves that every diagonal zero-row
  support is inverse-closed.  The circulant case uses graph symmetry; the
  reverse-circulant case is zero by odd-cycle looplessness.
* A support has size at most two and excludes zero, hence `h` lies in it iff
  its ordered-difference set contains `2h`.
* `Erdos85GraphAnchorParity.lean` assembles the canonical leave, block
  disjointness, involution parity, and inverse-pair description to prove the
  actual graph theorem

```text
Odd(number of diagonal anchors containing h)
  <-> 2h notin {0,+/-1}.
```

Thus the base anchor parity input to the prime projection is no longer a
conjectural bridge: it is graph-facing Lean code.  The remaining parity-side
task is only the routine cyclic quotient fiber calculation (odd when `r/p`
is odd); the genuinely deep outstanding input is Fourier convolution
constancy in the square branch.

## 2026-08-05: cyclic projection and full conditional graph terminal

The projection subtlety is now handled correctly.  Base parity is not the
literal pullback of the three-hole pattern: the fiber over each exceptional
residue contains exactly one forbidden lift.  Since every reduction fiber
has odd size `r/p`, deleting that unique lift makes precisely the exceptional
fibers even.

Lean now verifies all parts of this statement:

* `card_projectionFiber_zmod_castHom`: reduction `ZMod r -> ZMod p` has
  fiber size `r/p`;
* the three forbidden half-steps map injectively onto the three exceptional
  quotient residues;
* projected anchor multiplicity is odd exactly off `{0,+/-1/2}`;
* this parity pattern produces the integral presentation `c=b+2e`; and
* together with convolution constancy it contradicts the uniform mod-four
  obstruction for every `p >= 7`.

The final graph-facing theorem is
`false_of_graph_projectedAnchor_convolution_constancy` in
`Erdos85GraphProjectedConvolutionTerminal.lean`.  It discharges every graph,
difference-array, fiber, parity, and mod-four assumption.  Its sole
substantive remaining hypothesis is the square-Fourier conclusion that the
projected anchor self-convolution is constant away from the special
coefficients.  This sharply identifies the remaining proof bottleneck.

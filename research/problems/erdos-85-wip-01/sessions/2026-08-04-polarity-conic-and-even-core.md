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

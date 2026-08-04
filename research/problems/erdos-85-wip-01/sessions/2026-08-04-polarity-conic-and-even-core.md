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

# Session 2026-08-07: paired-block Hall bound closes to equality

Collaboration: Codex + Claude/Fable, via the repository Squad room.

## Setting

Work in the unique-high order-49 sector.  The outer graph `R` has eight
five-point branches, indexed by the neighbors of the high vertex.  Those
indices are paired by the perfect matching in the high vertex's neighborhood.
Write `bar s` for the mate of `s`.

Between nonpaired branches, adjacency in `R` is a partial matching.  Let

* `m_{s,u}` be its deficiency from a perfect matching;
* `M_s = sum_{u far from s} m_{s,u}`.

The existing row-sum theorem identifies `M_s` with the number of vertices of
`B_s` covered by its internal matching.  The miss matrix is symmetric.  The
outer second-order defect graph is 9-regular, contains a `K5` on every branch,
and consequently has exactly 25 ordered cross-branch defect incidences out of
each branch.

## Paired block

For the paired branches `s, bar s`, every common neighbor of a pair
`(x,y) in B_s x B_bar_s` lies in one of the six other branches.  C4-freeness
makes the resulting two-step paths injective into the 25 ordered endpoint
pairs.  The deficient fan/saver argument gives

```
|D(B_s, B_bar_s)| <= M_s + M_bar_s - 5.                 (1)
```

This is the quantitative version of the clean-sector pigeonhole: with no
deficiencies, six endpoints would have to fit in a five-point target fiber.

## Far block

Now let `u` be far from `s`.  Common neighbors of `(x,y) in B_s x B_u` can
occur in four genuinely intermediate branches, or in either endpoint branch.
All these path sets are disjoint by C4-freeness.

The four intermediate compositions contribute at least

```
20 - (M_s - m_{s,u} - m_{s,bar u})
   - (M_u - m_{s,u} - m_{u,bar s}).
```

The two endpoint-branch compositions contribute at least

```
(M_s - m_{s,u}) + (M_u - m_{s,u}).
```

After cancellation, at least

```
20 + m_{s,bar u} + m_{u,bar s}
```

of the 25 endpoint pairs have a common neighbor.  Therefore

```
|D(B_s, B_u)| <= 5 - m_{s,bar u} - m_{u,bar s}.         (2)
```

## Global closure

Sum (2) over the six branches far from `s`.  Pairing permutes this six-element
set and symmetry turns the two correction sums into `M_s` and `M_bar_s`:

```
sum_{u far from s} |D(B_s,B_u)| <= 30 - M_s - M_bar_s.  (3)
```

Adding (1) gives at most 25 external defect incidences from `B_s`.  The
already-verified defect-regularity theorem gives exactly 25.  Hence every
inequality above is an equality, including every summand of (2):

```
|D(B_s, B_bar_s)| = M_s + M_bar_s - 5,

|D(B_s, B_u)| = 5 - m_{s,bar u} - m_{u,bar s}.
```

For the surviving paired profiles this says:

* type A `(M_s,M_bar_s)=(2,4)` has exactly one paired-block defect pair;
* type B `(4,4)` has exactly three paired-block defect pairs.

More importantly, equality propagates backward through every partial-matching
intersection estimate.  Thus the missing points in successive blocks are not
merely subject to parity: the relevant transported missing sets are disjoint,
and the saver injections attain their precise slack.  This is the marked
defect data needed by the current holonomy/cohomology route.

## Formalization target

1. Prove the far-block estimate (2) by a common-neighbor selector/counting
   lemma, reusing `card_le_of_commonNeighbor_selectors` and the branch miss-row
   identities.
2. Sum it and combine with
   `card_branch_le_add_matchedCounts_of_paired` and
   `orderFortyNine_outerDefect_crossDegree_eq_five`.
3. Expose both exact block-cardinality formulas as graph-facing theorems.
4. Extract equality cases for the partial-matching intersections only as they
   are needed by the finite holonomy argument.

The derivation is conceptual and parameterized; no multiplicity-table
enumeration is used.

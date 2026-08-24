# SIZE-TWO-CYCLIC: three-cap valuation-change audit

## The proposed collision alternative was too weak

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

Write

```text
K((x,t),(y,u)) = card (SizeTwoCyclicBaseResolvedRoute code x t y u).
```

The quadratic cap proved by
`sizeTwoCyclicBaseResolvedRoute_row_innerProduct_le_one` is

```text
sum_(y,u) K((x,t),(y,u)) K((x+d,t),(y,u)) <= 1.
```

Consequently, the second alternative proposed in
`SIZE_TWO_CYCLIC_BINARY_MECHANISM_AUDIT.md` -- two distinct source rows
owning one precise target cell -- does **not** contradict the cap.  It is
exactly one summand equal to one, hence is the extremal allowed case.  The
contradictory alternative must instead exhibit two *distinct* target cells
owned by the same ordered source pair:

```text
(y,u) != (y',u')
K((x,t),(y,u)) = K((x+d,t),(y,u)) = 1
K((x,t),(y',u')) = K((x+d,t),(y',u')) = 1.
```

This distinction matters for any proposed valuation descent.  A state
consisting only of a collision cell and its two owners does not remember a
second cell and therefore cannot terminate directly in the packing cap.

## Correct theorem shape

A terminal-facing valuation-change lemma must carry a *row pair together
with its accumulated common-target support*.  At each step it must produce
one of:

1. the same row pair with a second, distinct common target cell;
2. a new row pair at strictly smaller positive `v2` separation, together
   with a common target cell and an injective/monotone transport of the
   previously accumulated support; or
3. an independently contradictory event, stated explicitly rather than as
   "two owners of one cell".

Strict descent of a bare common-target witness is insufficient: it can end
at valuation zero with inner product exactly one at every level.  Likewise,
counting many common-target witnesses globally is insufficient unless a
pigeonhole argument keeps the source row pair fixed.  These are precisely
the base correlations lost by the displacement and valuation marginals.

## Bounded falsifier

Before formalization, test any candidate transport on the reduced q=8 and
q=16 models while recording the tuple

```text
(source fiber, source base pair, target cell, separation valuation).
```

The candidate survives only if every transition either preserves a fixed
source pair while growing its set of distinct target cells, or supplies a
proved injection carrying that support to a lower valuation.  A histogram
by valuation, target cell, or source pair separately cannot validate the
claim.  The q16 empty-middle control remains decisive for the particular
four-cap subtree: a SAT verdict kills that forcing statement even if some
more general binary packing theorem remains true.

## Literature boundary

Wang's special near-orthomorphisms show that the individual punctured
permutation blocks exist on cyclic binary groups.  Searches for orthogonal
orthomorphisms lead to full Latin-square orthogonality, whose pairwise
difference-permutation condition is stronger and differently punctured
than the present moving-hole reciprocal tensor.  No located result supplies
the required support-preserving descent, so importing an orthomorphism
nonexistence theorem here would be unjustified.

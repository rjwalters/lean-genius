/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerNDimOQ02

/-
# General-`d` canonical facet-incidence: the "two sides exist" lower bound (issue #39076)

Spinoff of #8998 (Sperner Part 2).  The `d = 1` base case in
`Proofs.SpernerGridFaithfulD1` machine-checks that each geometric
`(d-1)`-facet of the canonical grid complex is incident to exactly **1**
canonical cell (boundary) or exactly **2** (interior).  This file takes the
first fully-dependency-satisfied step of the general-`d` generalization: the
**lower bound** `incidence ≥ 2` at every facet that carries a partner cell.

## Framing: `GridSimplex`-direct for `d ≥ 2`

The `d = 1` file counts incidence over the `IsCanon` (`CanonSimplex`) subtype
because at `d = 1` the oriented chain encoding double-covers the geometry and
`IsCanon` selects one representative.  For `d ≥ 2` the situation is different
and *simpler*: `SpernerNDimOQ02.eq_of_range_eq` proves that a `GridSimplex` is
already determined by its vertex *range* with **no** `IsCanon` hypothesis
(the `miss` direction and base are geometry-intrinsic once `d ≥ 2`), and in
fact the `CanonSimplex` subtype *fails existence* for `d ≥ 2`
(`SpernerNDimOQ02Obstruction.sBad_no_canon_rep`).  So above dimension one the
correct carrier is `GridSimplex` directly — each geometric Freudenthal cell is
exactly one `GridSimplex` — and the incidence count is taken over
`GridSimplex × Fin (d+1)` pairs, using the `gridVertices`/`gridFacet` Kuhn
carrier of `SpernerNDimOQ02`.

## What is proved here (0-sorry, 0-axiom)

`facetIncidence F` counts the encoded `(cell, facet-index)` pairs whose Kuhn
facet is `F`.  We establish the **existence half** of the redesign target —
that at least two cells are incident — at each of the three sites that carry a
partner, reusing the already-verified pivot machinery of `SpernerNDimOQ02`:

* `two_le_facetIncidence_of_interior` — a chain-**interior** facet
  (`0 < k < d`) is incident to `≥ 2` cells, via the Freudenthal pivot
  neighbour (`exists_neighbor_of_isInteriorFacet`).  Unconditional.
* `two_le_facetIncidence_zero_of_feasible` — the bottom facet `k = 0` in the
  feasible (geometrically-interior) regime is incident to `≥ 2` cells, via the
  facet-`0` cross-chain partner (`zeroPivotCell_shares_facet_zero`, part of the
  proven pivot reciprocity `topPivotCell_zeroPivotCell` /
  `zeroPivotCell_topPivotCell`).
* `two_le_facetIncidence_last_of_feasible` — the top facet `k = Fin.last d` in
  the feasible regime is incident to `≥ 2` cells, via the dual top-facet
  cross-chain partner (`topPivotCell_shares_facet_last`).

## What is deliberately *not* claimed

This is only the `≥ 2` (existence-of-a-second-side) direction — it does **not**
claim exactly `2`.  The matching **upper bound** ("at most two cells share a
facet", and "exactly one" on the geometric boundary `∂Δ_N`) is the hard
geometric both-sides theorem (the piece open on mathlib4#34310); it is out of
scope for this increment and remains for the general `boundary_doors_odd`
induction tracked in #8998.  No overclaiming per the Axiom Integrity Policy.
-/

open Finset

namespace SpernerNDimOQ02

variable {d N : ℕ}

/-- The **facet-incidence count**: the number of encoded `(cell, facet-index)`
pairs whose Kuhn facet is the given `(d-1)`-face `F`.  This is the general-`d`,
`GridSimplex`-direct analogue of `SpernerGrid.orientedFacetIncidence`; for
`d ≥ 2` the encoding is faithful (`eq_of_range_eq`), so it also counts distinct
*geometric* incident cells (each with the one facet index realizing `F`). -/
noncomputable def facetIncidence (F : Finset (SpernerNDim.Vertex d N)) : ℕ :=
  (univ.filter
    (fun p : SpernerGrid.GridSimplex d N × Fin (d + 1) => gridFacet p.1 p.2 = F)).card

/-- **Two distinct incident pairs force `facetIncidence ≥ 2`.**  Packaging
lemma: if two cells `s, t` are distinct and each carries `F` as a facet
(at indices `k`, `l`), the incidence count of `F` is at least two. -/
theorem two_le_facetIncidence_of_pair
    {s t : SpernerGrid.GridSimplex d N} {k l : Fin (d + 1)}
    {F : Finset (SpernerNDim.Vertex d N)}
    (hst : s ≠ t) (hs : gridFacet s k = F) (ht : gridFacet t l = F) :
    2 ≤ facetIncidence F := by
  rw [facetIncidence]
  have hmem_s : (s, k) ∈ univ.filter
      (fun p : SpernerGrid.GridSimplex d N × Fin (d + 1) => gridFacet p.1 p.2 = F) := by
    simp only [mem_filter, mem_univ, true_and]; exact hs
  have hmem_t : (t, l) ∈ univ.filter
      (fun p : SpernerGrid.GridSimplex d N × Fin (d + 1) => gridFacet p.1 p.2 = F) := by
    simp only [mem_filter, mem_univ, true_and]; exact ht
  have hne : (s, k) ≠ (t, l) := by
    intro h; exact hst (congrArg Prod.fst h)
  exact Finset.one_lt_card.mpr ⟨(s, k), hmem_s, (t, l), hmem_t, hne⟩

/-- **Interior facet ⇒ incidence ≥ 2.**  A chain-interior Kuhn facet
(`IsInteriorFacet k`, i.e. `0 < k < d`) of any cell `s` is incident to at least
two distinct cells: `s` itself and its Freudenthal pivot neighbour across that
facet (`exists_neighbor_of_isInteriorFacet`).  This is the unconditional
"the interior facet has a second side" existence datum — the lower-bound half
of the `d = 1` `orientedFacetIncidence = 2`, now for general `d`. -/
theorem two_le_facetIncidence_of_interior (s : SpernerGrid.GridSimplex d N)
    {k : Fin (d + 1)} (hk : IsInteriorFacet k) :
    2 ≤ facetIncidence (gridFacet s k) := by
  obtain ⟨t, _hglued, hne, hfacet⟩ := exists_neighbor_of_isInteriorFacet s hk
  exact two_le_facetIncidence_of_pair (fun h => hne h.symm) rfl hfacet

/-- **Bottom facet, feasible regime ⇒ incidence ≥ 2.**  In the feasible
(geometrically-interior) regime the bottom Kuhn facet `k = 0` — which the
within-chain neighbour map leaves unpaired, yet is never a `∂Δ_N` door
(`zero_facet_not_on_boundary`) — is incident to at least two distinct cells:
`s` and its facet-`0` cross-chain partner `zeroPivotCell s`, which shares
`gridFacet s 0` as its own top facet (`zeroPivotCell_shares_facet_zero`).
This reuses the proven pivot reciprocity `topPivotCell_zeroPivotCell` /
`zeroPivotCell_topPivotCell` (the partner is a genuine adjacency involute). -/
theorem two_le_facetIncidence_zero_of_feasible (s : SpernerGrid.GridSimplex d N)
    (hd1 : 0 < d) (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    2 ≤ facetIncidence (gridFacet s 0) := by
  obtain ⟨hne, hfacet⟩ := zeroPivotCell_shares_facet_zero s hd1 hfeas
  exact two_le_facetIncidence_of_pair hne.symm rfl hfacet

/-- **Top facet, feasible regime ⇒ incidence ≥ 2.**  Dually, in the feasible
regime the top Kuhn facet `k = Fin.last d` is incident to at least two distinct
cells: `u` and its top-facet cross-chain partner `topPivotCell u`, which shares
`gridFacet u (Fin.last d)` as its own facet `0` (`topPivotCell_shares_facet_last`).
Reciprocal to `two_le_facetIncidence_zero_of_feasible`. -/
theorem two_le_facetIncidence_last_of_feasible (u : SpernerGrid.GridSimplex d N)
    (hd1 : 0 < d) (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    2 ≤ facetIncidence (gridFacet u (Fin.last d)) := by
  obtain ⟨hne, hfacet⟩ := topPivotCell_shares_facet_last u hd1 hfeas
  exact two_le_facetIncidence_of_pair hne.symm rfl hfacet

end SpernerNDimOQ02

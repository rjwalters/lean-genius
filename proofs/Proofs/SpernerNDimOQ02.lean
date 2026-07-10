import Proofs.SpernerNDim
import Proofs.SpernerGridBase

/-
# sperner-ndim-oq-02: BaryPoint ≃ Vertex coordinate bridge

The abstract Sperner framework `SpernerNDim` indexes grid points by
`SpernerNDim.Vertex d N` — *Kuhn coordinates*: a function `Fin d → ℕ` with
`∑ ≤ N`, where the last (omitted) barycentric coordinate is the slack `N - ∑`.
The concrete Freudenthal grid in `SpernerGrid` uses *full barycentric
coordinates* `SpernerGrid.BaryPoint d N` — a function `Fin (d+1) → ℕ` with
`∑ = N`.

These two coordinate systems are canonically isomorphic:

* drop the last barycentric coordinate to obtain a Kuhn vertex
  (`toVertex`), and
* append the slack `N - ∑` as the last coordinate to recover the
  barycentric point (`toBary`).

This file establishes that `Equiv` (`baryEquivVertex`) together with the
matching `onFace` correspondence (`onFace_toVertex`). It is the foundational
bridge of "Option C" for `sperner-ndim-oq-02`: it lets the complete (0-sorry)
`SpernerNDim` framework be reused over `BaryPoint` without re-deriving it. See
`research/problems/sperner-ndim-oq-02/` for the full plan.

On top of the coordinate bridge this file also carries the Phase-1
`SpernerTriangulation`-instance machinery for the Freudenthal grid:

* the `CanonSimplex` carrier (canonical-orientation cells) with its facet
  algebra (`facet`, `baryFacet`, `facet_eq_iff_baryFacet_eq`,
  `canon_eq_of_facet_and_vertex`);
* the barycentric boundary/interior analysis
  (`boundary_face_iff_coords_zero`, `coord_incDir_eq_zero_iff`,
  `miss_coord_eq_zero_iff`, `IsInteriorFacet`/`IsBoundaryFacet`,
  `isInteriorFacet_iff`); and
* the within-chain pivot and neighbour data (`pivotSimplex`,
  `pivot_involutive`, `GridGlued`, `gridNeighbor`, `gridNeighbor_spec`,
  `exists_neighbor_of_isInteriorFacet`).

**Regression-recovery note (2026-06-30).** The pivot/neighbour/boundary
machinery listed above (≈1300 lines, ~70 declarations, all previously
verified 0-axiom in #31443/#31495) was inadvertently clobbered when the
older barycentric-facet-algebra branch #30947 was squash-merged from a
stale base, dropping the file from 1772 back to 464 lines. This revision
restores the lost declarations and re-integrates them with the newer
barycentric-facet section, so both live in one compiling file again.

No new axioms or sorries are introduced.
-/

open Finset BigOperators

namespace SpernerNDimOQ02

variable {d N : ℕ}

/-- Forward map: drop the last barycentric coordinate.
    A barycentric point `(b₀, …, b_d)` with `∑ = N` maps to the Kuhn vertex
    `(b₀, …, b_{d-1})`, whose coordinate sum is `N - b_d ≤ N`. -/
def toVertex (b : SpernerGrid.BaryPoint d N) : SpernerNDim.Vertex d N where
  coords := fun i => b.coords i.castSucc
  valid := by
    have hsum : ∑ i : Fin (d + 1), b.coords i = N := b.sum_eq
    rw [Fin.sum_univ_castSucc] at hsum
    have : ∑ i : Fin d, b.coords i.castSucc ≤ N := by omega
    exact this

/-- Backward map: append the slack `N - ∑` as the last barycentric coordinate.
    A Kuhn vertex `(x₀, …, x_{d-1})` with `∑ ≤ N` maps to the barycentric point
    `(x₀, …, x_{d-1}, N - ∑)`, whose coordinate sum is exactly `N`. -/
def toBary (v : SpernerNDim.Vertex d N) : SpernerGrid.BaryPoint d N where
  coords := Fin.snoc v.coords (N - ∑ i, v.coords i)
  sum_eq := by
    have hv : ∑ i, v.coords i ≤ N := v.valid
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    omega

@[simp]
theorem toVertex_coords (b : SpernerGrid.BaryPoint d N) (i : Fin d) :
    (toVertex b).coords i = b.coords i.castSucc := rfl

@[simp]
theorem toBary_coords_castSucc (v : SpernerNDim.Vertex d N) (i : Fin d) :
    (toBary v).coords i.castSucc = v.coords i := by
  simp [toBary]

@[simp]
theorem toBary_coords_last (v : SpernerNDim.Vertex d N) :
    (toBary v).coords (Fin.last d) = N - ∑ i, v.coords i := by
  simp [toBary]

/-- `toBary` is a left inverse of `toVertex` (round-trip on barycentric points).
    Recovering the dropped last coordinate from `∑ = N` reconstructs `b`. -/
theorem toBary_toVertex (b : SpernerGrid.BaryPoint d N) :
    toBary (toVertex b) = b := by
  apply SpernerGrid.BaryPoint.ext
  funext i
  cases i using Fin.lastCases with
  | last =>
    have hsum : ∑ i : Fin (d + 1), b.coords i = N := b.sum_eq
    rw [Fin.sum_univ_castSucc] at hsum
    simp only [toBary_coords_last, toVertex_coords]
    omega
  | cast j => simp

/-- `toBary` is a right inverse of `toVertex` (round-trip on Kuhn vertices).
    Dropping the appended slack coordinate reconstructs `v`. -/
theorem toVertex_toBary (v : SpernerNDim.Vertex d N) :
    toVertex (toBary v) = v := by
  apply SpernerNDim.Vertex.ext
  funext i
  simp

/-- **The coordinate bridge.** Barycentric lattice points on the `d`-simplex
    are in canonical bijection with Kuhn vertices, via dropping/appending the
    last barycentric coordinate. -/
def baryEquivVertex (d N : ℕ) : SpernerGrid.BaryPoint d N ≃ SpernerNDim.Vertex d N where
  toFun := toVertex
  invFun := toBary
  left_inv := toBary_toVertex
  right_inv := toVertex_toBary

@[simp] theorem baryEquivVertex_apply (b : SpernerGrid.BaryPoint d N) :
    baryEquivVertex d N b = toVertex b := rfl

@[simp] theorem baryEquivVertex_symm_apply (v : SpernerNDim.Vertex d N) :
    (baryEquivVertex d N).symm v = toBary v := rfl

/-- `toVertex` is injective (it is the forward map of the bridge `Equiv`).
    Needed for the `vertices_injective` field of the Phase-1 Freudenthal
    `SpernerTriangulation` instance, whose vertices are `toVertex ∘ verts`. -/
theorem toVertex_injective : Function.Injective (toVertex : SpernerGrid.BaryPoint d N → _) :=
  (baryEquivVertex d N).injective

/-- `toBary` is injective (it is the inverse map of the bridge `Equiv`). -/
theorem toBary_injective : Function.Injective (toBary : SpernerNDim.Vertex d N → _) :=
  (baryEquivVertex d N).symm.injective

/-- **Face correspondence.** A barycentric point lies on face `k` of the
    `d`-simplex exactly when its image Kuhn vertex does. For `k < d` both
    conditions say "the `k`-th coordinate is `0`"; for `k = d` (the last face)
    the barycentric condition `b_d = 0` matches the Kuhn condition `∑ = N`. -/
theorem onFace_toVertex (b : SpernerGrid.BaryPoint d N) (k : Fin (d + 1)) :
    SpernerNDim.onFace (toVertex b) k ↔ b.onFace k := by
  unfold SpernerNDim.onFace SpernerGrid.BaryPoint.onFace
  split
  · -- k < d : both sides are "the k-th coordinate is 0"
    rename_i h
    have hcast : (⟨(k : ℕ), h⟩ : Fin d).castSucc = k := by
      apply Fin.ext
      simp
    simp only [toVertex_coords, hcast]
  · -- k = last d : ∑ = N  ↔  b_d = 0
    rename_i h
    simp_rw [toVertex_coords]
    have hsum : ∑ i : Fin (d + 1), b.coords i = N := b.sum_eq
    rw [Fin.sum_univ_castSucc] at hsum
    have hk : k = Fin.last d := by
      apply Fin.ext
      have hlt := k.isLt
      simp only [Fin.val_last]
      omega
    rw [hk]
    omega

/-- The bridge transports Sperner colorings: a coloring of the barycentric grid
    is Sperner iff the corresponding coloring of Kuhn vertices is. -/
theorem isSperner_iff (c : SpernerNDim.Vertex d N → Fin (d + 1)) :
    SpernerNDim.IsSperner c ↔
      SpernerGrid.IsSperner (fun b => c (toVertex b)) := by
  constructor
  · intro hc b k hbk
    exact hc (toVertex b) k ((onFace_toVertex b k).mpr hbk)
  · intro hc v k hvk
    have hb : (toBary v).onFace k := by
      have hov : SpernerNDim.onFace (toVertex (toBary v)) k := by
        rw [toVertex_toBary]; exact hvk
      exact (onFace_toVertex (toBary v) k).mp hov
    have h2 := hc (toBary v) k hb
    simp only [toVertex_toBary] at h2
    exact h2

-- ============================================================
-- SECTION: Phase-1 carrier skeleton (`CanonSimplex`)
-- ============================================================
-- The abstract `SpernerNDim.SpernerTriangulation d N` carrier is the
-- subtype of *canonical* grid simplices (one representative per
-- geometric Freudenthal cell).  `SpernerGridBase` already discharges
-- every geometric obligation of the *easy* triangulation fields:
--
--   * `Simplex`               := `CanonSimplex d N` (below)
--   * `simplex_decidableEq`   := `DecidableEq (GridSimplex)` + `Subtype`
--   * `simplex_fintype`       := `gridSimplexFintype` + decidable `IsCanon`
--   * `vertices`              := `toVertex ∘ verts` (the bridge map)
--   * `vertices_injective`    := `verts_injective` + `toVertex_injective`
--
-- and the orientation-free "one representative per cell" property
-- (`IsCanon.geometry_unique`) lifts across the injective bridge to
-- `canon_eq_of_vertices_range` below.  The remaining obligations for a
-- full `SpernerTriangulation` instance are exactly the facet-adjacency
-- field `adj` and its five compatibility axioms plus `boundary_face`
-- — none of which this section claims.  This keeps the file 0-sorry,
-- 0-axiom while pinning down the entire *vertex/geometry* half of the
-- carrier.

/-- The Phase-1 Freudenthal carrier: canonical grid simplices.  By
`IsCanon.geometry_unique` each geometric cell has exactly one inhabitant,
so this subtype is the orientation-free `Simplex` type the abstract
`SpernerNDim.SpernerTriangulation` requires. -/
def CanonSimplex (d N : ℕ) := {s : SpernerGrid.GridSimplex d N // SpernerGrid.IsCanon s}

instance (d N : ℕ) : DecidableEq (CanonSimplex d N) :=
  Subtype.instDecidableEq

noncomputable instance (d N : ℕ) : Fintype (CanonSimplex d N) :=
  Subtype.fintype _

/-- Vertex map of a canonical cell: the `k`-th grid vertex pushed to Kuhn
coordinates through the bridge `toVertex`.  This is the `vertices` field
of the abstract triangulation. -/
def vertices (s : CanonSimplex d N) (k : Fin (d + 1)) : SpernerNDim.Vertex d N :=
  toVertex (s.1.verts k)

/-- The `d+1` vertices of a single canonical cell are distinct (the
`vertices_injective` field).  Combines per-cell vertex injectivity
(`GridSimplex.verts_injective`) with injectivity of the bridge. -/
theorem vertices_injective (s : CanonSimplex d N) :
    Function.Injective (vertices s) := by
  intro i j h
  exact s.1.verts_injective (toVertex_injective h)

/-- **One representative per geometry (Kuhn side).** Two canonical cells with
the same *Kuhn* vertex set are equal.  Lifts `IsCanon.geometry_unique` (stated
over barycentric `BaryPoint`s) across the injective bridge `toVertex`: equal
image-sets under an injection have equal pre-image sets, then geometry
uniqueness gives equality of the underlying grid simplices, and `Subtype.ext`
finishes.  This is what makes the door-counting adjacency well defined: there
is no orientation ambiguity in which canonical cell carries a given facet. -/
theorem canon_eq_of_vertices_range {d N : ℕ} {s t : CanonSimplex d N}
    (h : Set.range (vertices s) = Set.range (vertices t)) : s = t := by
  have key : ∀ u : CanonSimplex d N,
      Set.range (vertices u) = toVertex '' Set.range u.1.verts := by
    intro u
    have huc : vertices u = toVertex ∘ u.1.verts := rfl
    rw [huc, Set.range_comp]
  rw [key s, key t] at h
  have hbary : Set.range s.1.verts = Set.range t.1.verts :=
    Set.image_injective.mpr toVertex_injective h
  exact Subtype.ext (SpernerGrid.IsCanon.geometry_unique s.2 t.2 hbary)

-- ============================================================
-- SECTION: Facet structure of a canonical cell
-- ============================================================
-- The abstract `adj` field of a `SpernerTriangulation` is a *facet*
-- adjacency: `adj s k` names the neighbour glued to `s` across the
-- `(d-1)`-face obtained by deleting vertex `k`.  Two of its compatibility
-- obligations are phrased directly in terms of that deleted-vertex set:
--
--   * `adj_vertices` equates the deleted-vertex *images* of glued cells,
--     `(univ.erase k).image (vertices s) = (univ.erase k').image (vertices s')`;
--   * `adj_unique_facet` needs the `d + 1` facets of a *single* cell to be
--     distinct, so that a neighbour can be glued across at most one of them.
--
-- This section pins down that facet combinatorics for `CanonSimplex`
-- independently of how `adj` is eventually defined: each cell has `d + 1`
-- facets, each a `d`-vertex set, the deleted vertex is the unique vertex
-- absent from its own facet, and the facet map `k ↦ facet s k` is injective.
-- None of this depends on the adjacency geometry, so it stays 0-sorry,
-- 0-axiom while supplying the exact lemmas the `adj` discharge will cite.

/-- The `k`-th **facet** of a canonical cell: the `d`-vertex set obtained by
deleting vertex `k` and pushing the rest through the Kuhn bridge.  This is the
common-face vertex set that the abstract `adj_vertices` field equates across a
glued pair of cells. -/
def facet (s : CanonSimplex d N) (k : Fin (d + 1)) : Finset (SpernerNDim.Vertex d N) :=
  (Finset.univ.erase k).image (vertices s)

/-- Membership in a facet: a Kuhn vertex lies on facet `k` exactly when it is
the image of some vertex `j ≠ k`. -/
theorem mem_facet_iff (s : CanonSimplex d N) (k : Fin (d + 1))
    (v : SpernerNDim.Vertex d N) :
    v ∈ facet s k ↔ ∃ j : Fin (d + 1), j ≠ k ∧ vertices s j = v := by
  simp only [facet, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]

/-- The deleted vertex is the unique vertex of the cell **absent** from its own
facet: `vertices s k ∉ facet s k`.  (Were it present, two distinct vertices of
the cell would coincide, contradicting `vertices_injective`.) -/
theorem vertices_not_mem_facet (s : CanonSimplex d N) (k : Fin (d + 1)) :
    vertices s k ∉ facet s k := by
  rw [mem_facet_iff]
  rintro ⟨j, hjk, hj⟩
  exact hjk (vertices_injective s hj)

/-- Each facet carries exactly `d` vertices (the cell's `d + 1` vertices minus
the deleted one).  Uses per-cell vertex injectivity to count the image. -/
theorem facet_card (s : CanonSimplex d N) (k : Fin (d + 1)) :
    (facet s k).card = d := by
  rw [facet, Finset.card_image_of_injective _ (vertices_injective s),
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- **The `d + 1` facets of a single cell are distinct.**  If `facet s k₁ =
facet s k₂` then `k₁ = k₂`: otherwise `vertices s k₁` would lie in
`facet s k₂ = facet s k₁`, contradicting `vertices_not_mem_facet`.  This is the
within-cell half of `adj_unique_facet` — a neighbour can be glued across at most
one facet of `s`. -/
theorem facet_injective (s : CanonSimplex d N) :
    Function.Injective (facet s) := by
  intro k₁ k₂ h
  by_contra hne
  have hmem : vertices s k₁ ∈ facet s k₂ :=
    (mem_facet_iff s k₂ _).mpr ⟨k₁, hne, rfl⟩
  rw [← h] at hmem
  exact vertices_not_mem_facet s k₁ hmem

/-- Reconstructing the deleted index from the facet: vertex `j` lies off
facet `k` (i.e. `vertices s j ∉ facet s k`) exactly when `j = k`.  Together with
`facet_injective` this says the facet set and the cell together determine which
vertex was removed — the data `adj` must keep coherent. -/
theorem not_mem_facet_iff (s : CanonSimplex d N) (k j : Fin (d + 1)) :
    vertices s j ∉ facet s k ↔ j = k := by
  constructor
  · intro hj
    by_contra hne
    exact hj ((mem_facet_iff s k _).mpr ⟨j, hne, rfl⟩)
  · rintro rfl
    exact vertices_not_mem_facet s _

-- ============================================================
-- SECTION: Facet reconstruction of a canonical cell
-- ============================================================
-- `adj` records, for each interior facet of a cell, the neighbouring
-- cell glued across it together with that neighbour's opposite vertex
-- index.  For this stored data to be coherent the *cell* must be
-- recoverable from a single (facet, opposite-vertex) pair.  These
-- lemmas pin that down: the full vertex set of a canonical cell is its
-- `k`-facet plus the deleted vertex `vertices s k`, and consequently a
-- canonical cell is determined by any one facet together with its
-- opposite vertex (`canon_eq_of_facet_and_vertex`).  This is the
-- cross-cell companion of `facet_injective` (which handled the
-- within-cell direction) and the precise statement that makes the
-- (facet, opposite-vertex) payload of `adj` well defined.  All
-- 0-sorry, 0-axiom.

/-- The full vertex set of a canonical cell is its `k`-th facet
together with the deleted vertex `vertices s k`.  Splitting `univ` as
`insert k (univ.erase k)` and pushing through `vertices s` recovers the
cell's `d + 1` vertices from the `d`-vertex facet and the one removed
vertex. -/
theorem image_univ_eq_insert_facet (s : CanonSimplex d N) (k : Fin (d + 1)) :
    Finset.univ.image (vertices s) = insert (vertices s k) (facet s k) := by
  rw [facet, ← Finset.image_insert, Finset.insert_erase (Finset.mem_univ k)]

/-- The Finset vertex set of a canonical cell coerces to the range of
its vertex map.  Bridges the Finset-level facet algebra above to the
`Set.range` interface of `canon_eq_of_vertices_range`. -/
theorem coe_image_univ_vertices (s : CanonSimplex d N) :
    (↑(Finset.univ.image (vertices s)) : Set (SpernerNDim.Vertex d N))
      = Set.range (vertices s) := by
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- **A canonical cell is determined by one facet and its opposite
vertex.**  If two canonical cells share a facet (`facet s k = facet t l`)
together with the matching deleted vertex (`vertices s k = vertices t l`),
then they are equal.  Both cells then have the same full vertex set
(facet ∪ {opposite vertex}), and `canon_eq_of_vertices_range` collapses
that to cell equality.  This is the coherence underlying `adj`: the
(facet, opposite-vertex) pair the adjacency stores pins down the cell
uniquely, so a glued neighbour cannot be ambiguous. -/
theorem canon_eq_of_facet_and_vertex {s t : CanonSimplex d N}
    {k l : Fin (d + 1)}
    (hface : facet s k = facet t l)
    (hvert : vertices s k = vertices t l) : s = t := by
  apply canon_eq_of_vertices_range
  rw [← coe_image_univ_vertices s, ← coe_image_univ_vertices t,
    image_univ_eq_insert_facet s k, image_univ_eq_insert_facet t l,
    hface, hvert]

/-- **Global facet/opposite-vertex coherence.**  The pair `(facet s k, vertices s k)` — a
facet of a canonical cell together with its opposite (deleted) vertex — identifies both the
cell `s` and the index `k` uniquely across the *entire* carrier.  This packages the two
halves of the facet section into the single injectivity fact the door-counting adjacency
reasons with: the cross-cell direction `canon_eq_of_facet_and_vertex` collapses the cell
(`s = t`), then the within-cell direction `facet_injective` collapses the index (`k = l`).
The consequence is that the `(facet, opposite-vertex)` payload an `adj` entry stores can
name at most one `(cell, facet)` slot — there is no orientation or gluing ambiguity. -/
theorem facet_vertex_injective :
    Function.Injective
      (fun p : CanonSimplex d N × Fin (d + 1) => (facet p.1 p.2, vertices p.1 p.2)) := by
  rintro ⟨s, k⟩ ⟨t, l⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hface, hvert⟩ := h
  obtain rfl : s = t := canon_eq_of_facet_and_vertex hface hvert
  obtain rfl : k = l := facet_injective s hface
  rfl

-- ============================================================
-- SECTION: Interior Freudenthal pivot (neighbour existence)
-- ============================================================
-- The search-based `adj` reads off, for each facet of a canonical
-- cell, the unique *other* canonical cell glued across it (or
-- `none` on the geometric boundary).  Its `boundary_face` field is
-- the contrapositive obligation: an *interior* facet must actually
-- have a neighbour.  This section supplies the geometric heart of
-- that existence for the chain-interior facets — the **Freudenthal
-- pivot**: deleting an interior vertex `a.succ` of a Kuhn cell, the
-- neighbour glued across the remaining `d`-vertex facet is obtained
-- by swapping the two consecutive increment steps `a` and `b`
-- (`b.castSucc = a.succ`).  Only the pivoted vertex changes; it
-- moves along the "other diagonal" of the local square
-- `verts a.castSucc → verts a.succ → verts b.succ`.
--
-- We build that neighbour as an honest `GridSimplex`
-- (`pivotSimplex`, all five Kuhn axioms discharged), and prove it
-- (i) keeps the deleted-vertex facet fixed (`pivot_facet_eq`) and
-- (ii) genuinely moves the opposite vertex (`pivot_opposite_ne`),
-- hence is a *different* cell (`pivot_ne`).  This is the
-- `GridSimplex`-level existence statement; canonicalising the
-- pivot (re-selecting the lex-min base) to land it back in
-- `CanonSimplex`, and the two boundary-chain pivots `a.succ ∈ {0,d}`,
-- remain for the full `adj`.  Everything here is 0-sorry, 0-axiom.

open SpernerGrid

/-- A `Fin` index never equals the successor it casts up to: `x.castSucc ≠ x.succ`. -/
theorem Fin_castSucc_ne_succ {d : ℕ} (x : Fin d) : x.castSucc ≠ x.succ := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.coe_castSucc, Fin.val_succ] at hv
  omega

/-- Two consecutive Kuhn steps are distinct: if `a.succ = b.castSucc`
then `a ≠ b` (else `a.succ = a.castSucc`, impossible). -/
theorem pivot_ab_ne {a b : Fin d} (hb : a.succ = b.castSucc) : a ≠ b := by
  rintro rfl
  exact absurd hb.symm (Fin_castSucc_ne_succ a)

/-- The **pivoted vertex**.  Relative to the deleted vertex
`s.verts a.succ`, it decrements the coordinate raised at step `a`
(`incDir a`) and increments the coordinate raised at step `b`
(`incDir b`) — i.e. it is `verts a.castSucc + e_{incDir b} - e_miss`,
the opposite corner of the local square.  The total mass is
preserved (`incDir a` falls by 1, `incDir b` rises by 1), and the
`incDir a` coordinate is `≥ 1` (step `a` raised it), so the nat
subtraction is exact. -/
def pivotPoint (s : SpernerGrid.GridSimplex d N) (a b : Fin d) (hab : a ≠ b) :
    SpernerGrid.BaryPoint d N where
  coords := fun j =>
    if j = s.incDir a then (s.verts a.succ).coords j - 1
    else if j = s.incDir b then (s.verts a.succ).coords j + 1
    else (s.verts a.succ).coords j
  sum_eq := by
    have hpos : 1 ≤ (s.verts a.succ).coords (s.incDir a) := by
      have := s.step_inc a; omega
    have hne : s.incDir a ≠ s.incDir b := fun h => hab (s.inc_injective h)
    -- Move-one-unit identity: "+[=incDir a]" on the pivot balances "+[=incDir b]" on the original.
    have key : ∀ j : Fin (d + 1),
        (if j = s.incDir a then (s.verts a.succ).coords j - 1
          else if j = s.incDir b then (s.verts a.succ).coords j + 1
          else (s.verts a.succ).coords j)
        + (if j = s.incDir a then 1 else 0)
        = (s.verts a.succ).coords j + (if j = s.incDir b then 1 else 0) := by
      intro j
      by_cases h1 : j = s.incDir a
      · subst h1
        rw [if_pos rfl, if_pos rfl, if_neg hne]
        omega
      · by_cases h2 : j = s.incDir b
        · subst h2
          rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]
        · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
    have hone_a : (∑ j : Fin (d + 1), (if j = s.incDir a then (1 : ℕ) else 0)) = 1 := by simp
    have hone_b : (∑ j : Fin (d + 1), (if j = s.incDir b then (1 : ℕ) else 0)) = 1 := by simp
    have hsum :
        (∑ j : Fin (d + 1),
            (if j = s.incDir a then (s.verts a.succ).coords j - 1
              else if j = s.incDir b then (s.verts a.succ).coords j + 1
              else (s.verts a.succ).coords j)) + 1
          = (∑ j : Fin (d + 1), (s.verts a.succ).coords j) + 1 := by
      calc
        (∑ j : Fin (d + 1),
            (if j = s.incDir a then (s.verts a.succ).coords j - 1
              else if j = s.incDir b then (s.verts a.succ).coords j + 1
              else (s.verts a.succ).coords j)) + 1
            = (∑ j : Fin (d + 1),
                (if j = s.incDir a then (s.verts a.succ).coords j - 1
                  else if j = s.incDir b then (s.verts a.succ).coords j + 1
                  else (s.verts a.succ).coords j))
              + (∑ j : Fin (d + 1), (if j = s.incDir a then (1 : ℕ) else 0)) := by rw [hone_a]
          _ = ∑ j : Fin (d + 1),
                ((if j = s.incDir a then (s.verts a.succ).coords j - 1
                    else if j = s.incDir b then (s.verts a.succ).coords j + 1
                    else (s.verts a.succ).coords j)
                  + (if j = s.incDir a then (1 : ℕ) else 0)) := by rw [Finset.sum_add_distrib]
          _ = ∑ j : Fin (d + 1),
                ((s.verts a.succ).coords j + (if j = s.incDir b then (1 : ℕ) else 0)) :=
                Finset.sum_congr rfl (fun j _ => key j)
          _ = (∑ j : Fin (d + 1), (s.verts a.succ).coords j)
                + (∑ j : Fin (d + 1), (if j = s.incDir b then (1 : ℕ) else 0)) := by
                rw [Finset.sum_add_distrib]
          _ = (∑ j : Fin (d + 1), (s.verts a.succ).coords j) + 1 := by rw [hone_b]
    rw [(s.verts a.succ).sum_eq] at hsum
    omega

theorem pivotPoint_coords_eq_incA (s : SpernerGrid.GridSimplex d N)
    (a b : Fin d) (hab : a ≠ b) :
    (pivotPoint s a b hab).coords (s.incDir a)
      = (s.verts a.succ).coords (s.incDir a) - 1 := by
  have h : (pivotPoint s a b hab).coords (s.incDir a)
      = if s.incDir a = s.incDir a then (s.verts a.succ).coords (s.incDir a) - 1
        else if s.incDir a = s.incDir b then (s.verts a.succ).coords (s.incDir a) + 1
        else (s.verts a.succ).coords (s.incDir a) := rfl
  rw [h, if_pos rfl]

theorem pivotPoint_coords_eq_incB (s : SpernerGrid.GridSimplex d N)
    (a b : Fin d) (hab : a ≠ b) :
    (pivotPoint s a b hab).coords (s.incDir b)
      = (s.verts a.succ).coords (s.incDir b) + 1 := by
  have hne : s.incDir b ≠ s.incDir a := fun h => hab (s.inc_injective h).symm
  have h : (pivotPoint s a b hab).coords (s.incDir b)
      = if s.incDir b = s.incDir a then (s.verts a.succ).coords (s.incDir b) - 1
        else if s.incDir b = s.incDir b then (s.verts a.succ).coords (s.incDir b) + 1
        else (s.verts a.succ).coords (s.incDir b) := rfl
  rw [h, if_neg hne, if_pos rfl]

theorem pivotPoint_coords_eq_other (s : SpernerGrid.GridSimplex d N)
    (a b : Fin d) (hab : a ≠ b) (j : Fin (d + 1))
    (hja : j ≠ s.incDir a) (hjb : j ≠ s.incDir b) :
    (pivotPoint s a b hab).coords j = (s.verts a.succ).coords j := by
  have h : (pivotPoint s a b hab).coords j
      = if j = s.incDir a then (s.verts a.succ).coords j - 1
        else if j = s.incDir b then (s.verts a.succ).coords j + 1
        else (s.verts a.succ).coords j := rfl
  rw [h, if_neg hja, if_neg hjb]

/-- The **interior Freudenthal pivot**.  For consecutive steps `a`, `b`
(`a.succ = b.castSucc`), the neighbour of `s` glued across the facet
opposite vertex `a.succ`: same base/`miss`, the two increment steps
`a`, `b` swapped (`incDir ∘ swap a b`), and the single vertex `a.succ`
replaced by `pivotPoint`.  All five Kuhn axioms are discharged: the
`miss` coordinate is untouched everywhere (so `step_dec` is inherited);
the only steps whose endpoints move are `a` and `b`, handled by the
local-square computation. -/
def pivotSimplex (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) : SpernerGrid.GridSimplex d N where
  verts := Function.update s.verts a.succ (pivotPoint s a b (pivot_ab_ne hb))
  incDir := s.incDir ∘ Equiv.swap a b
  miss := s.miss
  miss_ne_inc := fun k => s.miss_ne_inc (Equiv.swap a b k)
  inc_injective := s.inc_injective.comp (Equiv.swap a b).injective
  step_dec := by
    have hab : a ≠ b := pivot_ab_ne hb
    -- The `miss` coordinate is unchanged at every vertex.
    have hconst : ∀ v : Fin (d + 1),
        (Function.update s.verts a.succ (pivotPoint s a b hab) v).coords s.miss
          = (s.verts v).coords s.miss := by
      intro v
      by_cases hv : v = a.succ
      · subst hv
        rw [Function.update_self]
        exact pivotPoint_coords_eq_other s a b hab s.miss
          (fun h => s.miss_ne_inc a h.symm) (fun h => s.miss_ne_inc b h.symm)
      · rw [Function.update_of_ne hv]
    intro k
    rw [hconst, hconst]
    exact s.step_dec k
  step_inc := by
    have hab : a ≠ b := pivot_ab_ne hb
    intro k
    by_cases hka : k = a
    · rw [hka]
      have hIa : (s.incDir ∘ ⇑(Equiv.swap a b)) a = s.incDir b := by
        simp [Equiv.swap_apply_left]
      rw [hIa, Function.update_self,
        Function.update_of_ne (Fin_castSucc_ne_succ a),
        pivotPoint_coords_eq_incB s a b hab]
      have hstep : (s.verts a.succ).coords (s.incDir b)
          = (s.verts a.castSucc).coords (s.incDir b) :=
        s.step_same a (s.incDir b) (fun h => hab (s.inc_injective h).symm) (s.miss_ne_inc b)
      omega
    · by_cases hkb : k = b
      · rw [hkb]
        have hIb : (s.incDir ∘ ⇑(Equiv.swap a b)) b = s.incDir a := by
          simp [Equiv.swap_apply_right]
        have hbc : b.castSucc = a.succ := hb.symm
        have hsucc_ne : b.succ ≠ a.succ := fun h => hab (Fin.succ_inj.mp h).symm
        rw [hIb, Function.update_of_ne hsucc_ne, hbc, Function.update_self,
          pivotPoint_coords_eq_incA s a b hab]
        have hpos : 1 ≤ (s.verts a.succ).coords (s.incDir a) := by
          have := s.step_inc a; omega
        have hstep : (s.verts b.succ).coords (s.incDir a)
            = (s.verts a.succ).coords (s.incDir a) := by
          have h := s.step_same b (s.incDir a) (fun h => hab (s.inc_injective h)) (s.miss_ne_inc a)
          rwa [hbc] at h
        omega
      · have hIk : (s.incDir ∘ ⇑(Equiv.swap a b)) k = s.incDir k := by
          simp [Equiv.swap_apply_of_ne_of_ne hka hkb]
        have hcs_ne : k.castSucc ≠ a.succ := by
          rw [hb]; exact fun h => hkb (Fin.castSucc_inj.mp h)
        have hsc_ne : k.succ ≠ a.succ := fun h => hka (Fin.succ_inj.mp h)
        rw [hIk, Function.update_of_ne hsc_ne, Function.update_of_ne hcs_ne]
        exact s.step_inc k
  step_same := by
    have hab : a ≠ b := pivot_ab_ne hb
    intro k j hjI hjm
    by_cases hka : k = a
    · rw [hka] at hjI ⊢
      have hIa : (s.incDir ∘ ⇑(Equiv.swap a b)) a = s.incDir b := by
        simp [Equiv.swap_apply_left]
      rw [hIa] at hjI
      rw [Function.update_self, Function.update_of_ne (Fin_castSucc_ne_succ a)]
      by_cases hja : j = s.incDir a
      · subst hja
        rw [pivotPoint_coords_eq_incA s a b hab]
        have := s.step_inc a
        omega
      · rw [pivotPoint_coords_eq_other s a b hab j hja hjI]
        exact s.step_same a j hja hjm
    · by_cases hkb : k = b
      · rw [hkb] at hjI ⊢
        have hIb : (s.incDir ∘ ⇑(Equiv.swap a b)) b = s.incDir a := by
          simp [Equiv.swap_apply_right]
        rw [hIb] at hjI
        have hbc : b.castSucc = a.succ := hb.symm
        have hsucc_ne : b.succ ≠ a.succ := fun h => hab (Fin.succ_inj.mp h).symm
        rw [Function.update_of_ne hsucc_ne, hbc, Function.update_self]
        by_cases hjb : j = s.incDir b
        · subst hjb
          rw [pivotPoint_coords_eq_incB s a b hab]
          have hss := s.step_inc b
          rw [hbc] at hss
          omega
        · rw [pivotPoint_coords_eq_other s a b hab j hjI hjb]
          have hss := s.step_same b j hjb hjm
          rw [hbc] at hss
          exact hss
      · have hIk : (s.incDir ∘ ⇑(Equiv.swap a b)) k = s.incDir k := by
          simp [Equiv.swap_apply_of_ne_of_ne hka hkb]
        rw [hIk] at hjI
        have hcs_ne : k.castSucc ≠ a.succ := by
          rw [hb]; exact fun h => hkb (Fin.castSucc_inj.mp h)
        have hsc_ne : k.succ ≠ a.succ := fun h => hka (Fin.succ_inj.mp h)
        rw [Function.update_of_ne hsc_ne, Function.update_of_ne hcs_ne]
        exact s.step_same k j hjI hjm

/-- **The pivot keeps the facet fixed.**  The `d` vertices off the
deleted vertex `a.succ` are untouched by the pivot, so `s` and its
pivot share the facet opposite `a.succ` as vertex sets.  This is the
`adj_vertices`-style common-face equality for the interior pivot. -/
theorem pivot_facet_eq (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) :
    (Finset.univ.erase a.succ).image (pivotSimplex s a b hb).verts
      = (Finset.univ.erase a.succ).image s.verts := by
  apply Finset.image_congr
  intro j hj
  have hjne : j ≠ a.succ := by simpa using hj
  show Function.update s.verts a.succ (pivotPoint s a b (pivot_ab_ne hb)) j = s.verts j
  rw [Function.update_of_ne hjne]

/-- **The pivot moves the opposite vertex.**  The pivoted vertex
differs from the deleted vertex at coordinate `incDir a` (it drops by
one, from a value `≥ 1`).  So the pivot is a genuinely different
filling of the shared facet. -/
theorem pivot_opposite_ne (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) :
    (pivotSimplex s a b hb).verts a.succ ≠ s.verts a.succ := by
  have hab : a ≠ b := pivot_ab_ne hb
  intro h
  have hpos : 1 ≤ (s.verts a.succ).coords (s.incDir a) := by
    have := s.step_inc a; omega
  have hcoord : ((pivotSimplex s a b hb).verts a.succ).coords (s.incDir a)
      = (s.verts a.succ).coords (s.incDir a) := by rw [h]
  have hval : (pivotSimplex s a b hb).verts a.succ = pivotPoint s a b hab := by
    show Function.update s.verts a.succ (pivotPoint s a b hab) a.succ = _
    rw [Function.update_self]
  rw [hval, pivotPoint_coords_eq_incA s a b hab] at hcoord
  omega

/-- **The interior pivot is a different cell.**  Immediate from
`pivot_opposite_ne`: equal simplices would have equal vertex
functions, hence equal opposite vertices.  Together with
`pivot_facet_eq` this is exactly the `GridSimplex`-level neighbour
existence the search-based `adj` needs at chain-interior facets. -/
theorem pivot_ne (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) :
    pivotSimplex s a b hb ≠ s := by
  intro h
  exact pivot_opposite_ne s a b hb (by rw [h])

/-- `GridSimplex` extensionality on the three data fields (the structure carries no
`@[ext]`; the proof fields are discharged by definitional proof irrelevance). -/
private theorem gridSimplex_ext {s t : SpernerGrid.GridSimplex d N}
    (hv : s.verts = t.verts) (hi : s.incDir = t.incDir) (hm : s.miss = t.miss) :
    s = t := by
  cases s; cases t; cases hv; cases hi; cases hm; rfl

/-- **The interior pivot is an involution.**  Pivoting twice across the *same* facet
(opposite `a.succ`, with the same consecutive step pair `a, b`) returns the original
cell.  Two ingredients combine: the direction permutation `Equiv.swap a b` is its own
inverse (`incDir` returns to `s.incDir`), and the second `pivotPoint` exactly undoes
the first — in the pivoted cell `t` the roles of the two move directions are swapped
(`t.incDir a = s.incDir b`, `t.incDir b = s.incDir a`), so the second pivot moves
`incDir a` *up* and `incDir b` *down*, reversing the original move and restoring
`s.verts a.succ`.  This is the geometric heart of the adjacency symmetry `adj_symm`
for chain-interior facets: the neighbour relation built from `pivotSimplex` is
symmetric, with each facet-flip its own reverse. -/
theorem pivot_involutive (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) :
    pivotSimplex (pivotSimplex s a b hb) a b hb = s := by
  have hab : a ≠ b := pivot_ab_ne hb
  set t := pivotSimplex s a b hb with ht
  -- Roles of the move directions are swapped in `t`.
  have hia : t.incDir a = s.incDir b := by
    show (s.incDir ∘ ⇑(Equiv.swap a b)) a = s.incDir b
    simp [Equiv.swap_apply_left]
  have hib : t.incDir b = s.incDir a := by
    show (s.incDir ∘ ⇑(Equiv.swap a b)) b = s.incDir a
    simp [Equiv.swap_apply_right]
  have hva : t.verts a.succ = pivotPoint s a b hab := by
    show Function.update s.verts a.succ (pivotPoint s a b hab) a.succ = _
    rw [Function.update_self]
  have hne : s.incDir a ≠ s.incDir b := fun h => hab (s.inc_injective h)
  have hpos : 1 ≤ (s.verts a.succ).coords (s.incDir a) := by
    have := s.step_inc a; omega
  -- The doubly-pivoted vertex returns to the original deleted vertex.
  have hpt : pivotPoint t a b hab = s.verts a.succ := by
    ext j
    by_cases h1 : j = s.incDir a
    · subst h1
      have hL : (pivotPoint t a b hab).coords (s.incDir a)
          = (t.verts a.succ).coords (t.incDir b) + 1 := by
        rw [← hib]; exact pivotPoint_coords_eq_incB t a b hab
      rw [hL, hva, hib, pivotPoint_coords_eq_incA s a b hab]
      omega
    · by_cases h2 : j = s.incDir b
      · subst h2
        have hL : (pivotPoint t a b hab).coords (s.incDir b)
            = (t.verts a.succ).coords (t.incDir a) - 1 := by
          rw [← hia]; exact pivotPoint_coords_eq_incA t a b hab
        rw [hL, hva, hia, pivotPoint_coords_eq_incB s a b hab]
        omega
      · have hja : j ≠ t.incDir a := by rw [hia]; exact h2
        have hjb : j ≠ t.incDir b := by rw [hib]; exact h1
        rw [pivotPoint_coords_eq_other t a b hab j hja hjb, hva,
          pivotPoint_coords_eq_other s a b hab j h1 h2]
  -- Assemble the three field equalities.
  refine gridSimplex_ext ?_ ?_ rfl
  · show Function.update t.verts a.succ (pivotPoint t a b hab) = s.verts
    have htv : t.verts = Function.update s.verts a.succ (pivotPoint s a b hab) := rfl
    rw [hpt, htv, Function.update_idem, Function.update_eq_self]
  · show (s.incDir ∘ ⇑(Equiv.swap a b)) ∘ ⇑(Equiv.swap a b) = s.incDir
    funext k
    simp [Equiv.swap_apply_self]

/-- **The interior pivot fixes the base vertex.**  The pivot only updates the
vertex `a.succ`, and `a.succ ≠ 0`, so the lex-base `verts 0` is untouched. -/
theorem pivot_base_eq (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) :
    (pivotSimplex s a b hb).verts 0 = s.verts 0 := by
  show Function.update s.verts a.succ (pivotPoint s a b (pivot_ab_ne hb)) 0 = s.verts 0
  rw [Function.update_of_ne (Fin.succ_ne_zero a).symm]

/-- **Canonicality of the interior pivot reduces to a single lex test.**  The pivot
fixes every vertex except the moved one (`a.succ`), in particular the lex-base
`verts 0` (`pivot_base_eq`).  Since `s` is canonical, all unchanged vertices already
dominate that shared base, so the pivot is canonical **iff** its one moved vertex —
the pivot point — also dominates the base.  This replaces the `d + 1` canonicality
conditions of the pivoted cell by the single comparison a recanonicalization step
must check, isolating exactly when the interior pivot already lands on the canonical
representative of its geometric cell. -/
theorem pivot_isCanon_iff (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) (hs : SpernerGrid.IsCanon s) :
    SpernerGrid.IsCanon (pivotSimplex s a b hb)
      ↔ (s.verts 0).lexLE (pivotPoint s a b (pivot_ab_ne hb)) := by
  have hpiv : (pivotSimplex s a b hb).verts a.succ
      = pivotPoint s a b (pivot_ab_ne hb) := by
    show Function.update s.verts a.succ (pivotPoint s a b (pivot_ab_ne hb)) a.succ = _
    rw [Function.update_self]
  constructor
  · intro hcanon
    have h := hcanon a.succ
    rwa [pivot_base_eq, hpiv] at h
  · intro hpivLE k
    rw [pivot_base_eq]
    by_cases hk : k = a.succ
    · subst hk; rw [hpiv]; exact hpivLE
    · have hvk : (pivotSimplex s a b hb).verts k = s.verts k := by
        show Function.update s.verts a.succ (pivotPoint s a b (pivot_ab_ne hb)) k = s.verts k
        rw [Function.update_of_ne hk]
      rw [hvk]; exact hs k

-- ============================================================
-- SECTION: At most one neighbour across a facet (adj_unique_facet)
-- ============================================================
-- The abstract `adj_unique_facet` field requires that two *distinct*
-- facets of a cell `s` cannot both be glued to the *same* neighbour `t`
-- — geometrically, two `d`-simplices share at most one common
-- `(d-1)`-face.  This section proves exactly that, purely from the facet
-- combinatorics and per-geometry uniqueness already established, so the
-- eventual `adj` discharge can cite it directly.  The key step is that
-- the union of two distinct facets of a cell is its *entire* vertex set;
-- if both facets also lie in a second cell `t`, then `t`'s `d + 1`
-- vertices contain `s`'s `d + 1` vertices, forcing equal vertex sets and
-- hence `s = t`.  All 0-sorry, 0-axiom.

/-- **The union of two distinct facets is the full vertex set.**  Facet
`k₁` omits only vertex `k₁` and facet `k₂` omits only vertex `k₂`; when
`k₁ ≠ k₂` each omitted vertex is supplied by the other facet, so the
union recovers all `d + 1` vertices of the cell. -/
theorem facet_union_facet (s : CanonSimplex d N) {k₁ k₂ : Fin (d + 1)}
    (h : k₁ ≠ k₂) :
    facet s k₁ ∪ facet s k₂ = Finset.univ.image (vertices s) := by
  rw [facet, facet, ← Finset.image_union]
  congr 1
  apply Finset.eq_univ_of_forall
  intro a
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
  by_cases ha : a = k₁
  · exact Or.inr ⟨ha ▸ h, Finset.mem_univ _⟩
  · exact Or.inl ⟨ha, Finset.mem_univ _⟩

/-- A canonical cell has exactly `d + 1` distinct Kuhn vertices: the
image of `univ` under the injective vertex map. -/
theorem image_univ_card (s : CanonSimplex d N) :
    (Finset.univ.image (vertices s)).card = d + 1 := by
  rw [Finset.card_image_of_injective _ (vertices_injective s), Finset.card_univ,
    Fintype.card_fin]

/-- **At most one neighbour across a facet (`adj_unique_facet`).**  If a cell
`s` shares two facets `k₁, k₂` with the *same* other cell `t`
(`facet s k₁ = facet t l₁`, `facet s k₂ = facet t l₂`, `s ≠ t`), then in fact
`k₁ = k₂`.  Otherwise the two distinct facets of `s` would union to all of `s`'s
vertices while both lying inside `t`'s vertex set; equal cardinalities then force
`s` and `t` to have the same vertex set, so `canon_eq_of_vertices_range` gives
`s = t`, contradicting `s ≠ t`.  This is exactly the content of the abstract
`adj_unique_facet` compatibility field: a neighbour is glued across at most one
facet of `s`. -/
theorem facet_unique_neighbor {s t : CanonSimplex d N}
    {k₁ k₂ l₁ l₂ : Fin (d + 1)} (hne : s ≠ t)
    (h₁ : facet s k₁ = facet t l₁) (h₂ : facet s k₂ = facet t l₂) :
    k₁ = k₂ := by
  by_contra hk
  have hs : Finset.univ.image (vertices s) = facet s k₁ ∪ facet s k₂ :=
    (facet_union_facet s hk).symm
  have hsub : Finset.univ.image (vertices s) ⊆ Finset.univ.image (vertices t) := by
    rw [hs, h₁, h₂]
    apply Finset.union_subset
    · rw [facet]; exact Finset.image_subset_image (Finset.erase_subset _ _)
    · rw [facet]; exact Finset.image_subset_image (Finset.erase_subset _ _)
  have hcard :
      (Finset.univ.image (vertices t)).card ≤ (Finset.univ.image (vertices s)).card := by
    rw [image_univ_card, image_univ_card]
  have heq : Finset.univ.image (vertices s) = Finset.univ.image (vertices t) :=
    Finset.eq_of_subset_of_card_le hsub hcard
  apply hne
  apply canon_eq_of_vertices_range
  rw [← coe_image_univ_vertices s, ← coe_image_univ_vertices t, heq]

-- ============================================================
-- SECTION: The canonical base of a cell (canonicalization target)
-- ============================================================
-- Every previous section established *uniqueness* of the canonical
-- representative of a geometry (`canon_eq_of_vertices_range`,
-- `IsCanon.geometry_unique`).  The dual *existence* direction —
-- recanonicalizing an arbitrary `GridSimplex` (e.g. the interior
-- Freudenthal pivot `pivotSimplex`, which need not be canonical) into the
-- `CanonSimplex` carrier — starts by selecting the new base: the lex-minimal
-- vertex of the cell.  Last session closed the order theory making this
-- well-posed (`exists_lex_min` + the lex linear order).  This section names
-- that base as a *function of the geometry* and proves the two properties the
-- recanonicalization map needs:
--
--   * it is determined by the vertex set alone (`baseOf_eq_of_range_eq`), so
--     the canonicalization map is well-defined; and
--   * on an already-canonical cell it is the recorded base `verts 0`
--     (`isCanon_baseOf_eq`), so canonicalization is the identity on the
--     carrier — a prerequisite for `adj` returning into `CanonSimplex`.
--
-- Everything here is order-theoretic bookkeeping over `exists_lex_min`; it adds
-- no axioms (only `Classical.choice`, via `Exists.choose`) and no sorries.

open SpernerGrid in
/-- The vertex set of a grid simplex, as a `Finset` of barycentric points. -/
def vertexSet (s : GridSimplex d N) : Finset (SpernerGrid.BaryPoint d N) :=
  Finset.univ.image s.verts

theorem mem_vertexSet (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    s.verts k ∈ vertexSet s := by
  simp only [vertexSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨k, rfl⟩

theorem vertexSet_nonempty (s : SpernerGrid.GridSimplex d N) :
    (vertexSet s).Nonempty :=
  ⟨s.verts 0, mem_vertexSet s 0⟩

/-- The lex-minimal base of a cell's vertex set.  Noncomputable choice from the
existence lemma `exists_lex_min`; it is well-defined *as a function of the
geometry* by `baseOf_eq_of_range_eq` below. -/
noncomputable def baseOf (s : SpernerGrid.GridSimplex d N) :
    SpernerGrid.BaryPoint d N :=
  (SpernerGrid.BaryPoint.exists_lex_min (vertexSet s) (vertexSet_nonempty s)).choose

theorem baseOf_mem (s : SpernerGrid.GridSimplex d N) :
    baseOf s ∈ vertexSet s :=
  (SpernerGrid.BaryPoint.exists_lex_min (vertexSet s) (vertexSet_nonempty s)).choose_spec.1

theorem baseOf_lexLE (s : SpernerGrid.GridSimplex d N) :
    ∀ x ∈ vertexSet s, (baseOf s).lexLE x :=
  (SpernerGrid.BaryPoint.exists_lex_min (vertexSet s) (vertexSet_nonempty s)).choose_spec.2

/-- **Uniqueness of the lex-min base.**  Any vertex of the cell that is
lex-`≤` every vertex equals `baseOf s` (the lex order has a unique minimum,
`lexLE_antisymm`).  This is what makes `baseOf` characterizable without
unfolding the noncomputable choice. -/
theorem baseOf_unique (s : SpernerGrid.GridSimplex d N)
    {b : SpernerGrid.BaryPoint d N} (hb : b ∈ vertexSet s)
    (hmin : ∀ x ∈ vertexSet s, b.lexLE x) : b = baseOf s :=
  SpernerGrid.BaryPoint.lexLE_antisymm (hmin _ (baseOf_mem s)) (baseOf_lexLE s _ hb)

/-- **The canonical base is determined by the vertex `Finset`.**  Two cells with
the same vertex set share the same lex-min base. -/
theorem baseOf_eq_of_vertexSet_eq {s t : SpernerGrid.GridSimplex d N}
    (h : vertexSet s = vertexSet t) : baseOf s = baseOf t := by
  apply baseOf_unique t
  · rw [← h]; exact baseOf_mem s
  · rw [← h]; exact baseOf_lexLE s

/-- **The canonical base is geometry-determined.**  Phrased over `Set.range`
to match `IsCanon.geometry_unique`: cells with the same vertex *range* have the
same lex-min base.  This is the well-definedness the recanonicalization map
requires — the base of the canonical representative depends only on the cell's
point set, not on the (arbitrary) chain ordering of `s`. -/
theorem baseOf_eq_of_range_eq {s t : SpernerGrid.GridSimplex d N}
    (h : Set.range s.verts = Set.range t.verts) : baseOf s = baseOf t := by
  apply baseOf_eq_of_vertexSet_eq
  apply Finset.coe_injective
  simp only [vertexSet, Finset.coe_image, Finset.coe_univ, Set.image_univ]
  exact h

/-- **On a canonical cell the lex-min base is the recorded base `verts 0`.**
Hence `baseOf` recovers the canonical base, and the recanonicalization map is the
identity on cells that are already canonical — exactly what is needed for the
`adj` neighbour to land back inside the `CanonSimplex` carrier. -/
theorem isCanon_baseOf_eq {s : SpernerGrid.GridSimplex d N}
    (hs : SpernerGrid.IsCanon s) : baseOf s = s.verts 0 := by
  symm
  apply baseOf_unique s (mem_vertexSet s 0)
  intro x hx
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
  exact hs k

/-- The lex-min base of a `CanonSimplex` is its base vertex. -/
theorem baseOf_canon (s : CanonSimplex d N) : baseOf s.1 = s.1.verts 0 :=
  isCanon_baseOf_eq s.2

-- ============================================================
-- The recanonicalization base of the interior pivot
-- ============================================================
-- `baseOf` names the lex-min base a recanonicalization step selects.
-- For the interior pivot (`pivotSimplex`, the neighbour the `adj`
-- search produces at a chain-interior facet) we can now pin that base
-- down in *both* outcomes of the single canonicality test
-- `pivot_isCanon_iff`:
--
--   * already canonical → `baseOf` is the untouched base `s.verts 0`
--     (`pivot_base_eq`), so recanonicalization is the identity;
--   * not canonical → the one moved vertex, the `pivotPoint`, has
--     dropped lex-below `s.verts 0` and so becomes the new lex-min
--     base of the neighbour's vertex set.
--
-- Together these say *exactly which vertex* the recanonicalization map
-- must promote to the base in every interior-pivot case — the remaining
-- input that step needs beyond the already-proven well-definedness
-- (`baseOf_eq_of_range_eq`) and identity-on-canonical
-- (`isCanon_baseOf_eq`) facts.

/-- **Recanonicalization base of a canonical interior pivot.**  When the
interior pivot already lands on the canonical representative, its lex-min
base is the untouched base `s.verts 0` (the pivot fixes vertex `0`,
`pivot_base_eq`).  So the recanonicalization map is the identity here. -/
theorem baseOf_pivot_of_canon (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc)
    (hcanon : SpernerGrid.IsCanon (pivotSimplex s a b hb)) :
    baseOf (pivotSimplex s a b hb) = s.verts 0 := by
  rw [isCanon_baseOf_eq hcanon, pivot_base_eq]

/-- **Recanonicalization base of a non-canonical interior pivot.**  When the
single lex test of `pivot_isCanon_iff` fails — i.e. the moved vertex
`pivotPoint` is *not* lex-dominated by the base `s.verts 0` — the pivot is
non-canonical, and the `pivotPoint` is precisely its new lex-min base.

The pivot's vertices are the moved `pivotPoint` together with the `d`
untouched vertices `s.verts j` (`j ≠ a.succ`).  Failure of the test makes
`pivotPoint` lex-`≤` the old base `s.verts 0` (lex totality), which in turn
is lex-`≤` every `s.verts j` (`s` is canonical); so `pivotPoint` dominates
all vertices and, lying in the cell, is the unique lex-min base
(`baseOf_unique`).  This identifies the vertex the recanonicalization map
must promote to the base whenever the interior pivot leaves the carrier. -/
theorem baseOf_pivot_of_not_canon (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) (hs : SpernerGrid.IsCanon s)
    (hp : ¬ (s.verts 0).lexLE (pivotPoint s a b (pivot_ab_ne hb))) :
    baseOf (pivotSimplex s a b hb) = pivotPoint s a b (pivot_ab_ne hb) := by
  -- The moved vertex `a.succ` is the `pivotPoint`.
  have hpiv : (pivotSimplex s a b hb).verts a.succ
      = pivotPoint s a b (pivot_ab_ne hb) := by
    show Function.update s.verts a.succ (pivotPoint s a b (pivot_ab_ne hb)) a.succ = _
    rw [Function.update_self]
  -- Test failure + lex totality: `pivotPoint` lex-≤ the old base.
  have hple0 : (pivotPoint s a b (pivot_ab_ne hb)).lexLE (s.verts 0) := by
    rcases SpernerGrid.BaryPoint.lexLE_total (s.verts 0)
        (pivotPoint s a b (pivot_ab_ne hb)) with h | h
    · exact absurd h hp
    · exact h
  symm
  apply baseOf_unique (pivotSimplex s a b hb)
  · -- `pivotPoint` is a vertex of the pivoted cell.
    rw [← hpiv]; exact mem_vertexSet (pivotSimplex s a b hb) a.succ
  · -- `pivotPoint` lex-dominates every vertex of the pivoted cell.
    intro x hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
    by_cases hj : j = a.succ
    · subst hj; rw [hpiv]; exact SpernerGrid.BaryPoint.lexLE_refl _
    · have hxj : (pivotSimplex s a b hb).verts j = s.verts j := by
        show Function.update s.verts a.succ
          (pivotPoint s a b (pivot_ab_ne hb)) j = s.verts j
        rw [Function.update_of_ne hj]
      rw [hxj]
      exact SpernerGrid.BaryPoint.lexLE_trans hple0 (hs j)

-- ============================================================
-- SECTION: The orientation ambiguity is a `d ≤ 1` phenomenon
-- ============================================================
-- `IsCanon.geometry_unique` (in `SpernerGridBase`) shows two *canonical*
-- `GridSimplex`es with the same vertex set are equal — it must assume
-- `IsCanon` on both because, in general, a geometric cell admits several
-- chain encodings (the Session-1 `d = 1` reversal counterexample: an edge
-- `{a, b}` is encoded both as `a → b` and `b → a`, with opposite `miss`).
--
-- This section pins down *exactly* where that ambiguity lives.  For `d ≥ 2`
-- the `miss` direction is **geometry-intrinsic**: it is the unique
-- coordinate that takes all `d + 1` distinct values across the cell (every
-- *non*-`miss` coordinate is incremented exactly once, so it takes only the
-- two values `c, c + 1`).  Hence for `d ≥ 2` the whole encoding is forced by
-- the vertex set alone — `eq_of_range_eq` gives per-geometry uniqueness with
-- **no `IsCanon` hypothesis**, so recanonicalization is the identity on every
-- cell and the orientation doubling is confined to the inductive base cases
-- `d ≤ 1`.  The three steps mirror the canonical proof but drop the base-
-- sharing assumption that `IsCanon.base_unique` used to supply:
--
--   1. `miss_intrinsic`     — `miss` recovered from the vertex *range* alone
--      (counting distinct coordinate values, needs `d ≥ 2`);
--   2. `base_eq_of_miss`    — with `miss` shared, the base is the unique
--      maximal-`miss`-coordinate vertex of the (shared) cell;
--   3. `eq_of_range_eq`     — feed the recovered base/`miss` to the existing
--      `verts_eq` / `incDir_eq` / `eq_of_base_miss_incDir`.
--
-- Everything is `GridSimplex` arithmetic over the already-proven recovery
-- lemmas; it adds no axioms (only `Classical.choice`, transitively) and no
-- sorries.

open SpernerGrid in
/-- **The `miss` direction is geometry-intrinsic for `d ≥ 2`.**  Two
`GridSimplex`es with the same vertex *range* share their `miss` direction —
*without* assuming a shared base (contrast `GridSimplex.miss_unique`, which
needs `hbase`).  Proof: along the chain the `miss` coordinate takes the `d + 1`
distinct values `base, base − 1, …, base − d` (`miss_coord_at`, injective since
`base ≥ d`), whereas every non-`miss` coordinate is incremented exactly once
and so takes only the two values `c, c + 1` (`coord_incDir_at`).  If the two
cells had different `miss`, the coordinate `t.miss` would be some `s.incDir k`
on the `s`-side; computed over the shared vertex set it would then have both
`d + 1` and `≤ 2` distinct values — impossible once `d + 1 > 2`. -/
theorem miss_intrinsic (hd : 2 ≤ d) {s t : SpernerGrid.GridSimplex d N}
    (hset : Set.range s.verts = Set.range t.verts) :
    s.miss = t.miss := by
  by_contra hne
  -- On the `s`-side the coordinate `t.miss` is some increment direction.
  obtain ⟨k, hk⟩ := s.incDir_surj_complement t.miss (fun h => hne h.symm)
  -- The two cells share their vertex `Finset`.
  have hVS : Finset.univ.image s.verts = Finset.univ.image t.verts := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hset
  -- The `Finset` of values taken by coordinate `t.miss` over the shared cell.
  set F : Finset ℕ :=
    (Finset.univ.image t.verts).image (fun v => v.coords t.miss) with hF
  -- Over the `t`-vertices this has exactly `d + 1` distinct values.
  have hinj : Function.Injective ((fun v => v.coords t.miss) ∘ t.verts) := by
    intro a b hab
    simp only [Function.comp] at hab
    rw [t.miss_coord_at a, t.miss_coord_at b] at hab
    have hbge := t.base_miss_ge_d
    have ha := a.isLt; have hb := b.isLt
    exact Fin.ext (by omega)
  have hcardF : F.card = d + 1 := by
    rw [hF, Finset.image_image, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]
  -- Over the `s`-vertices the same coordinate is `s.incDir k`, taking `≤ 2` values.
  have hsub : F ⊆ {(s.verts 0).coords (s.incDir k),
      (s.verts 0).coords (s.incDir k) + 1} := by
    rw [hF, ← hVS, Finset.image_image]
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp] at hx
    obtain ⟨m, rfl⟩ := hx
    rw [← hk, s.coord_incDir_at k m]
    by_cases h : k.val < m.val
    · rw [if_pos h]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rw [if_neg h]
      exact Finset.mem_insert_self _ _
  have hcardF2 : F.card ≤ 2 := by
    refine (Finset.card_le_card hsub).trans ?_
    exact (Finset.card_insert_le _ _).trans (by simp)
  rw [hcardF] at hcardF2
  omega

open SpernerGrid in
/-- **Base recovery without canonicality.**  Two `GridSimplex`es sharing their
`miss` direction and vertex range share their base vertex.  The base is the
unique vertex whose `miss` coordinate is maximal (`miss_coord_at`: it is
`base − m` at chain index `m`), and that is determined by the shared geometry.
This drops the `IsCanon` assumption of `IsCanon.base_unique`. -/
theorem base_eq_of_miss {s t : SpernerGrid.GridSimplex d N}
    (hmiss : s.miss = t.miss)
    (hset : Set.range s.verts = Set.range t.verts) :
    s.verts 0 = t.verts 0 := by
  -- `s.verts 0 = t.verts m` and `t.verts 0 = s.verts m'` (shared range).
  obtain ⟨m, hm⟩ : s.verts 0 ∈ Set.range t.verts := by rw [← hset]; exact ⟨0, rfl⟩
  obtain ⟨m', hm'⟩ : t.verts 0 ∈ Set.range s.verts := by rw [hset]; exact ⟨0, rfl⟩
  -- Compare the (shared) `miss` coordinate at the two bases.
  have e1 : (s.verts 0).coords s.miss
      = (t.verts 0).coords t.miss - m.val := by rw [hmiss, ← hm]; exact t.miss_coord_at m
  have e2 : (t.verts 0).coords t.miss
      = (s.verts 0).coords s.miss - m'.val := by rw [← hmiss, ← hm']; exact s.miss_coord_at m'
  have hbs := s.base_miss_ge_d
  have hbt := t.base_miss_ge_d
  have hmd := m.isLt; have hm'd := m'.isLt
  have hm0 : m.val = 0 := by omega
  rw [← hm, show (m : Fin (d + 1)) = 0 from Fin.ext hm0]

open SpernerGrid in
/-- **Per-geometry uniqueness for `d ≥ 2`, with no canonicality hypothesis.**
Two `GridSimplex`es with the same vertex range are *equal* once `d ≥ 2`.  So
the `GridSimplex` encoding is already one-representative-per-geometry above
dimension 1: the orientation doubling that motivates `IsCanon` only occurs in
the inductive base cases `d ≤ 1`.  Proof: recover `miss` (`miss_intrinsic`) and
the base (`base_eq_of_miss`), then reuse the canonical reconstruction chain
`verts_eq` → `incDir_eq` → `eq_of_base_miss_incDir`. -/
theorem eq_of_range_eq (hd : 2 ≤ d) {s t : SpernerGrid.GridSimplex d N}
    (hset : Set.range s.verts = Set.range t.verts) :
    s = t := by
  have hmiss := miss_intrinsic hd hset
  have hbase := base_eq_of_miss hmiss hset
  have hverts := SpernerGrid.GridSimplex.verts_eq hbase hmiss hset
  have hinc := SpernerGrid.GridSimplex.incDir_eq hverts
  exact s.eq_of_base_miss_incDir t hbase hmiss hinc

-- ============================================================
-- SECTION: GridSimplex-direct carrier for `d ≥ 2`
-- ============================================================
-- The `CanonSimplex := {s // IsCanon s}` carrier (base = lex-min vertex) has
-- *uniqueness* (`canon_eq_of_vertices_range`) but **fails existence**:
-- `SpernerNDimOQ02Obstruction.sBad_no_canon_rep` exhibits a genuine Freudenthal
-- cell (`d = 2`, `N = 2`, vertices `(2,0,0), (1,1,0), (0,1,1)`) whose lex-minimum
-- `(0,1,1)` has every coordinate `< d`, so no grid simplex on that cell can
-- satisfy `IsCanon` (a base always carries a coordinate `≥ d` by
-- `base_miss_ge_d`).  Hence `CanonSimplex` *omits cells* and cannot be the
-- `Simplex` type unmodified.
--
-- The repair is to drop the subtype and use `GridSimplex d N` as the carrier
-- directly.  For `d ≥ 2` that is sound on *both* counts:
--
--   * **existence** is now definitional — every geometric cell *is* a
--     `GridSimplex`, with no constraint left to violate; and
--   * **uniqueness** is `eq_of_range_eq` — for `d ≥ 2` the `miss` direction and
--     base are forced by the vertex range, so distinct `GridSimplex`es have
--     distinct vertex sets.
--
-- This section packages the GridSimplex-direct vertex map and the sound
-- replacement for `canon_eq_of_vertices_range`: the Kuhn-vertex set of a grid
-- simplex determines it (`grid_eq_of_vertices_range`), equivalently the map
-- `s ↦ univ.image (gridVertices s)` is injective (`gridVertices_finset_injective`).
-- These are the carrier lemmas the door-counting `adj` discharge will cite once
-- the carrier is switched from `CanonSimplex` to `GridSimplex` for `d ≥ 2`.

/-- Vertex map of a grid simplex, pushed to Kuhn coordinates through the bridge
`toVertex`.  Same as `vertices` but on `GridSimplex` directly (no `IsCanon`
subtype), for the repaired `d ≥ 2` carrier. -/
def gridVertices (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    SpernerNDim.Vertex d N :=
  toVertex (s.verts k)

/-- The `d + 1` Kuhn vertices of a grid simplex are distinct (the
`vertices_injective` obligation for the GridSimplex-direct carrier).  Combines
per-cell vertex injectivity (`GridSimplex.verts_injective`) with injectivity of
the bridge. -/
theorem gridVertices_injective (s : SpernerGrid.GridSimplex d N) :
    Function.Injective (gridVertices s) := by
  intro i j h
  exact s.verts_injective (toVertex_injective h)

open SpernerGrid in
/-- **Sound carrier uniqueness for `d ≥ 2`.**  A grid simplex is determined by
its Kuhn vertex set: two grid simplices with the same `Set.range gridVertices`
are equal once `d ≥ 2`.  This is the GridSimplex-direct analogue of
`canon_eq_of_vertices_range`, but with **no `IsCanon` hypothesis**, so the
existence failure of the `CanonSimplex` carrier
(`SpernerNDimOQ02Obstruction.sBad_no_canon_rep`) does not arise.  Proof: strip
the injective bridge `toVertex` to recover equality of the barycentric ranges,
then apply `eq_of_range_eq`. -/
theorem grid_eq_of_vertices_range (hd : 2 ≤ d)
    {s t : SpernerGrid.GridSimplex d N}
    (h : Set.range (gridVertices s) = Set.range (gridVertices t)) :
    s = t := by
  have key : ∀ u : SpernerGrid.GridSimplex d N,
      Set.range (gridVertices u) = toVertex '' Set.range u.verts := by
    intro u
    have huc : gridVertices u = toVertex ∘ u.verts := rfl
    rw [huc, Set.range_comp]
  rw [key s, key t] at h
  have hbary : Set.range s.verts = Set.range t.verts :=
    Set.image_injective.mpr toVertex_injective h
  exact eq_of_range_eq hd hbary

open SpernerGrid in
/-- **The carrier embeds into vertex sets (for `d ≥ 2`).**  The map sending a
grid simplex to its Kuhn vertex `Finset` is injective.  This is the
`Finset`-level restatement of `grid_eq_of_vertices_range` that the door-counting
combinatorics use — cells are identified by their vertex sets, with no
orientation ambiguity and no omitted cells once `d ≥ 2`. -/
theorem gridVertices_finset_injective (hd : 2 ≤ d) :
    Function.Injective
      (fun s : SpernerGrid.GridSimplex d N =>
        Finset.univ.image (gridVertices s)) := by
  intro s t h
  apply grid_eq_of_vertices_range hd
  have h' : Finset.univ.image (gridVertices s) = Finset.univ.image (gridVertices t) := h
  have hcoe : (↑(Finset.univ.image (gridVertices s)) : Set (SpernerNDim.Vertex d N))
      = ↑(Finset.univ.image (gridVertices t)) := by rw [h']
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using hcoe

-- ============================================================
-- SECTION: GridSimplex-direct facet combinatorics (`d ≥ 2`)
-- ============================================================
-- The facet section above (`facet`, `facet_injective`,
-- `canon_eq_of_facet_and_vertex`, `facet_unique_neighbor`, …) is stated
-- over the `CanonSimplex` carrier, whose existence failure for `d ≥ 2`
-- (`SpernerNDimOQ02Obstruction.sBad_no_canon_rep`) makes it unsound as the
-- door-counting carrier.  This section re-points the same combinatorics at the
-- repaired `GridSimplex`-direct carrier, citing `gridVertices`,
-- `gridVertices_injective`, and `grid_eq_of_vertices_range hd` in place of
-- `vertices`, `vertices_injective`, and `canon_eq_of_vertices_range`.  The
-- proofs are otherwise identical to the `CanonSimplex` versions — the carrier
-- swap is the whole content.  The crux is `gridFacet_unique_neighbor` (the
-- `adj_unique_facet` obligation: a neighbour is glued across at most one facet),
-- now sound because no cell is omitted.  All 0-sorry; the `d ≥ 2` hypothesis
-- enters only through `grid_eq_of_vertices_range`.

/-- The `k`-th **facet** of a grid simplex on the `GridSimplex`-direct carrier:
delete vertex `k`, push the rest through the Kuhn bridge.  GridSimplex analogue
of `facet`. -/
def gridFacet (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    Finset (SpernerNDim.Vertex d N) :=
  (Finset.univ.erase k).image (gridVertices s)

/-- Membership in a grid facet: a Kuhn vertex lies on `gridFacet s k` exactly
when it is the image of some vertex `j ≠ k`. -/
theorem mem_gridFacet_iff (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1))
    (v : SpernerNDim.Vertex d N) :
    v ∈ gridFacet s k ↔ ∃ j : Fin (d + 1), j ≠ k ∧ gridVertices s j = v := by
  simp only [gridFacet, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]

/-- The deleted vertex is absent from its own grid facet. -/
theorem gridVertices_not_mem_gridFacet (s : SpernerGrid.GridSimplex d N)
    (k : Fin (d + 1)) : gridVertices s k ∉ gridFacet s k := by
  rw [mem_gridFacet_iff]
  rintro ⟨j, hjk, hj⟩
  exact hjk (gridVertices_injective s hj)

/-- Each grid facet carries exactly `d` vertices. -/
theorem gridFacet_card (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    (gridFacet s k).card = d := by
  rw [gridFacet, Finset.card_image_of_injective _ (gridVertices_injective s),
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  omega

/-- **The `d + 1` grid facets of a single cell are distinct.**  GridSimplex
analogue of `facet_injective`; the within-cell half of `adj_unique_facet`. -/
theorem gridFacet_injective (s : SpernerGrid.GridSimplex d N) :
    Function.Injective (gridFacet s) := by
  intro k₁ k₂ h
  by_contra hne
  have hmem : gridVertices s k₁ ∈ gridFacet s k₂ :=
    (mem_gridFacet_iff s k₂ _).mpr ⟨k₁, hne, rfl⟩
  rw [← h] at hmem
  exact gridVertices_not_mem_gridFacet s k₁ hmem

/-- The full vertex set of a grid cell is its `k`-th grid facet plus the deleted
vertex `gridVertices s k`.  GridSimplex analogue of
`image_univ_eq_insert_facet`. -/
theorem gridImage_univ_eq_insert_gridFacet (s : SpernerGrid.GridSimplex d N)
    (k : Fin (d + 1)) :
    Finset.univ.image (gridVertices s) = insert (gridVertices s k) (gridFacet s k) := by
  rw [gridFacet, ← Finset.image_insert, Finset.insert_erase (Finset.mem_univ k)]

/-- The grid cell's Finset vertex set coerces to the range of its vertex map.
GridSimplex analogue of `coe_image_univ_vertices`. -/
theorem gridCoe_image_univ_vertices (s : SpernerGrid.GridSimplex d N) :
    (↑(Finset.univ.image (gridVertices s)) : Set (SpernerNDim.Vertex d N))
      = Set.range (gridVertices s) := by
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- **A grid cell is determined by one facet and its opposite vertex (`d ≥ 2`).**
GridSimplex analogue of `canon_eq_of_facet_and_vertex`, sound because no cell is
omitted: both cells share the same full vertex set (facet ∪ {opposite vertex}),
and `grid_eq_of_vertices_range hd` collapses that to cell equality. -/
theorem grid_eq_of_facet_and_vertex (hd : 2 ≤ d) {s t : SpernerGrid.GridSimplex d N}
    {k l : Fin (d + 1)}
    (hface : gridFacet s k = gridFacet t l)
    (hvert : gridVertices s k = gridVertices t l) : s = t := by
  apply grid_eq_of_vertices_range hd
  rw [← gridCoe_image_univ_vertices s, ← gridCoe_image_univ_vertices t,
    gridImage_univ_eq_insert_gridFacet s k, gridImage_univ_eq_insert_gridFacet t l,
    hface, hvert]

/-- Two distinct grid facets of a cell union to all its vertices.  GridSimplex
analogue of `facet_union_facet`. -/
theorem gridFacet_union_gridFacet (s : SpernerGrid.GridSimplex d N)
    {k₁ k₂ : Fin (d + 1)} (h : k₁ ≠ k₂) :
    gridFacet s k₁ ∪ gridFacet s k₂ = Finset.univ.image (gridVertices s) := by
  rw [gridFacet, gridFacet, ← Finset.image_union]
  congr 1
  apply Finset.eq_univ_of_forall
  intro a
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_erase]
  by_cases ha : a = k₁
  · exact Or.inr ⟨ha ▸ h, Finset.mem_univ _⟩
  · exact Or.inl ⟨ha, Finset.mem_univ _⟩

/-- A grid cell has exactly `d + 1` distinct Kuhn vertices.  GridSimplex
analogue of `image_univ_card`. -/
theorem gridImage_univ_card (s : SpernerGrid.GridSimplex d N) :
    (Finset.univ.image (gridVertices s)).card = d + 1 := by
  rw [Finset.card_image_of_injective _ (gridVertices_injective s), Finset.card_univ,
    Fintype.card_fin]

/-- **At most one neighbour across a grid facet (`adj_unique_facet`, `d ≥ 2`).**
If a cell `s` shares two facets with the same other cell `t` (`s ≠ t`), then the
two facet indices coincide.  GridSimplex analogue of `facet_unique_neighbor`,
sound on the repaired carrier: the two distinct facets of `s` union to all of
`s`'s vertices while both lie in `t`'s vertex set; equal cardinalities force
equal vertex sets, and `grid_eq_of_vertices_range hd` gives `s = t`,
contradicting `s ≠ t`. -/
theorem gridFacet_unique_neighbor (hd : 2 ≤ d) {s t : SpernerGrid.GridSimplex d N}
    {k₁ k₂ l₁ l₂ : Fin (d + 1)} (hne : s ≠ t)
    (h₁ : gridFacet s k₁ = gridFacet t l₁) (h₂ : gridFacet s k₂ = gridFacet t l₂) :
    k₁ = k₂ := by
  by_contra hk
  have hs : Finset.univ.image (gridVertices s) = gridFacet s k₁ ∪ gridFacet s k₂ :=
    (gridFacet_union_gridFacet s hk).symm
  have hsub : Finset.univ.image (gridVertices s) ⊆ Finset.univ.image (gridVertices t) := by
    rw [hs, h₁, h₂]
    apply Finset.union_subset
    · rw [gridFacet]; exact Finset.image_subset_image (Finset.erase_subset _ _)
    · rw [gridFacet]; exact Finset.image_subset_image (Finset.erase_subset _ _)
  have hcard :
      (Finset.univ.image (gridVertices t)).card ≤ (Finset.univ.image (gridVertices s)).card := by
    rw [gridImage_univ_card, gridImage_univ_card]
  have heq : Finset.univ.image (gridVertices s) = Finset.univ.image (gridVertices t) :=
    Finset.eq_of_subset_of_card_le hsub hcard
  apply hne
  apply grid_eq_of_vertices_range hd
  rw [← gridCoe_image_univ_vertices s, ← gridCoe_image_univ_vertices t, heq]

/-- **Global facet/opposite-vertex coherence (`d ≥ 2`).**  The pair
`(gridFacet s k, gridVertices s k)` identifies both the cell `s` and the index
`k` across the entire `GridSimplex` carrier.  GridSimplex analogue of
`facet_vertex_injective`: the cross-cell direction (`grid_eq_of_facet_and_vertex`)
collapses the cell, then the within-cell direction (`gridFacet_injective`)
collapses the index.  The `(facet, opposite-vertex)` payload of an `adj` entry
names at most one `(cell, facet)` slot. -/
theorem gridFacet_vertex_injective (hd : 2 ≤ d) :
    Function.Injective
      (fun p : SpernerGrid.GridSimplex d N × Fin (d + 1) =>
        (gridFacet p.1 p.2, gridVertices p.1 p.2)) := by
  rintro ⟨s, k⟩ ⟨t, l⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨hface, hvert⟩ := h
  obtain rfl : s = t := grid_eq_of_facet_and_vertex hd hface hvert
  obtain rfl : k = l := gridFacet_injective s hface
  rfl

-- ============================================================
-- SECTION: The interior neighbour (face-gluing) relation (`d ≥ 2`)
-- ============================================================
-- The pivot machinery (`pivotSimplex`, `pivot_facet_eq`, `pivot_ne`,
-- `pivot_involutive`) and the sound Kuhn-carrier facet combinatorics
-- (`gridFacet`, `gridFacet_unique_neighbor`) are now both available.  This
-- section ties them together into the constructive neighbour relation the
-- door-counting `adj` records at chain-interior facets: `GridGlued s t` holds
-- when `t` is the Freudenthal pivot of `s` across the facet opposite a vertex
-- `a.succ` (for a consecutive Kuhn step pair `a.succ = b.castSucc`).  Each fact
-- below is proved on the sound `GridSimplex`/`gridFacet` carrier and feeds a
-- distinct `adj` obligation:
--   * `pivot_gridFacet_eq` / `GridGlued.shares_facet` — glued cells share a Kuhn
--     facet (the `adj` common-face datum);
--   * `GridGlued.ne` — a glued neighbour is a *different* cell (no self-loops);
--   * `GridGlued_symm` — the relation is symmetric (`adj_symm`), each facet-flip
--     its own reverse, via the pivot involution `pivot_involutive`;
--   * `exists_gridFacet_neighbor` — every chain-interior facet HAS such a
--     neighbour (existence; uniqueness is the separate
--     `gridFacet_unique_neighbor`, the only place `d ≥ 2` is needed).
-- All 0-sorry, 0-axiom.  `d ≤ 1` orientation doubling is handled separately.

/-- **The interior pivot preserves the shared Kuhn facet.**  Transports
`pivot_facet_eq` — stated on the raw barycentric vertices — to the sound Kuhn
carrier: `s` and its pivot across the facet opposite `a.succ` have the *same*
`gridFacet · a.succ`.  Both Kuhn facets are the `toVertex`-image of one and the
same barycentric facet `(univ.erase a.succ).image ·.verts`, equal by
`pivot_facet_eq`.  This is the bridge that lets the door-counting `adj` cite the
pivot neighbour directly on the `gridFacet` carrier it actually uses. -/
theorem pivot_gridFacet_eq (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) :
    gridFacet (pivotSimplex s a b hb) a.succ = gridFacet s a.succ := by
  have key : ∀ u : SpernerGrid.GridSimplex d N,
      gridFacet u a.succ
        = ((Finset.univ.erase a.succ).image u.verts).image toVertex := by
    intro u
    have hgv : gridVertices u = toVertex ∘ u.verts := rfl
    rw [gridFacet, hgv, ← Finset.image_image]
  rw [key, key, pivot_facet_eq]

/-- The constructive **interior face-gluing relation**: `t` is the Freudenthal
pivot of `s` across the chain-interior facet opposite vertex `a.succ`, for a
consecutive Kuhn step pair `a.succ = b.castSucc`.  This is the neighbour the
door-counting `adj` records at every interior facet (the `d ≤ 1` orientation
doubling is handled separately). -/
def GridGlued (s t : SpernerGrid.GridSimplex d N) : Prop :=
  ∃ (a b : Fin d) (hb : a.succ = b.castSucc), t = pivotSimplex s a b hb

/-- **Every chain-interior facet has a glued neighbour.**  Given consecutive Kuhn
steps `a.succ = b.castSucc`, the pivot is a cell distinct from `s` that shares the
facet `gridFacet s a.succ`.  This is the existence half the `adj` discharge needs
at interior facets — `pivotSimplex` supplies it; uniqueness is the separate
`gridFacet_unique_neighbor`. -/
theorem exists_gridFacet_neighbor (s : SpernerGrid.GridSimplex d N) (a b : Fin d)
    (hb : a.succ = b.castSucc) :
    ∃ t : SpernerGrid.GridSimplex d N,
      GridGlued s t ∧ t ≠ s ∧ gridFacet t a.succ = gridFacet s a.succ :=
  ⟨pivotSimplex s a b hb, ⟨a, b, hb, rfl⟩, pivot_ne s a b hb,
    pivot_gridFacet_eq s a b hb⟩

/-- A glued neighbour is a **different cell** (no self-loops in `adj`). -/
theorem GridGlued.ne {s t : SpernerGrid.GridSimplex d N} (h : GridGlued s t) :
    s ≠ t := by
  obtain ⟨a, b, hb, rfl⟩ := h
  exact (pivot_ne s a b hb).symm

/-- **Glued cells share a Kuhn facet** (the `adj` common-face datum): if
`GridGlued s t` then some facet of `t` equals some facet of `s`. -/
theorem GridGlued.shares_facet {s t : SpernerGrid.GridSimplex d N}
    (h : GridGlued s t) :
    ∃ k : Fin (d + 1), gridFacet t k = gridFacet s k := by
  obtain ⟨a, b, hb, rfl⟩ := h
  exact ⟨a.succ, pivot_gridFacet_eq s a b hb⟩

/-- **The interior face-gluing relation is symmetric** (`adj_symm`).  Each
facet-flip is its own reverse: if `t` is the pivot of `s` across the facet
opposite `a.succ`, then `s` is the pivot of `t` across the *same* facet, by the
pivot involution `pivot_involutive`. -/
theorem GridGlued_symm {s t : SpernerGrid.GridSimplex d N} (h : GridGlued s t) :
    GridGlued t s := by
  obtain ⟨a, b, hb, rfl⟩ := h
  exact ⟨a, b, hb, (pivot_involutive s a b hb).symm⟩

/-
## Interior / boundary facet predicate

The door-counting `adj` must split the `d+1` Kuhn facets of each cell into the
chain-*interior* facets — those across which the Freudenthal pivot is defined and
which therefore carry a glued neighbour — and the two geometric *boundary* facets
(`k = 0` and `k = Fin.last d`), which have no interior partner.  The interior
facets are exactly those opposite a vertex `a.succ` for a consecutive Kuhn step
pair `a.succ = b.castSucc`; numerically these are the indices `0 < k < d`.
All 0-sorry, 0-axiom.
-/

/-- A Kuhn facet index `k : Fin (d+1)` is **chain-interior** when it is the facet
opposite an interior vertex `a.succ` for a consecutive Kuhn step pair
`a.succ = b.castSucc`.  These are precisely the facets across which the
Freudenthal pivot (`pivotSimplex`) is defined. -/
def IsInteriorFacet (k : Fin (d + 1)) : Prop :=
  ∃ a b : Fin d, a.succ = b.castSucc ∧ k = a.succ

/-- **Numeric characterization of interior facets**: facet `k` is chain-interior
iff `0 < k < d`, i.e. `k` is neither the bottom facet `0` nor the top facet
`Fin.last d`.  (For `d ≤ 1` there are no interior facets, matching the fact that
the orientation doubling there is handled separately.) -/
theorem isInteriorFacet_iff (k : Fin (d + 1)) :
    IsInteriorFacet k ↔ 0 < (k : ℕ) ∧ (k : ℕ) < d := by
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    have hb' : (a : ℕ) + 1 = (b : ℕ) := by
      have h := congrArg Fin.val hb
      rwa [Fin.val_succ, Fin.coe_castSucc] at h
    have hbd : (b : ℕ) < d := b.isLt
    rw [Fin.val_succ]; omega
  · rintro ⟨hk0, hkd⟩
    refine ⟨⟨(k : ℕ) - 1, by omega⟩, ⟨(k : ℕ), hkd⟩, ?_, ?_⟩
    · apply Fin.ext; show (k : ℕ) - 1 + 1 = (k : ℕ); omega
    · apply Fin.ext; show (k : ℕ) = (k : ℕ) - 1 + 1; omega

/-- The bottom Kuhn facet (`k = 0`) is a geometric boundary facet, not interior. -/
theorem not_isInteriorFacet_zero : ¬ IsInteriorFacet (0 : Fin (d + 1)) := by
  rw [isInteriorFacet_iff, Fin.val_zero]; omega

/-- The top Kuhn facet (`k = Fin.last d`) is a geometric boundary facet, not
interior. -/
theorem not_isInteriorFacet_last : ¬ IsInteriorFacet (Fin.last d) := by
  rw [isInteriorFacet_iff, Fin.val_last]; omega

/-- **Every interior facet carries a glued neighbour.**  Combining the predicate
with `exists_gridFacet_neighbor`: if facet `k` is chain-interior, the Freudenthal
pivot across it is a distinct cell sharing exactly that facet.  This is the total
existence datum the door-counting `adj` records at every interior facet. -/
theorem exists_neighbor_of_isInteriorFacet (s : SpernerGrid.GridSimplex d N)
    {k : Fin (d + 1)} (hk : IsInteriorFacet k) :
    ∃ t : SpernerGrid.GridSimplex d N,
      GridGlued s t ∧ t ≠ s ∧ gridFacet t k = gridFacet s k := by
  obtain ⟨a, b, hb, rfl⟩ := hk
  exact exists_gridFacet_neighbor s a b hb

/-- Chain-interiority of a facet is decidable (it reduces to the numeric test
`0 < k < d` via `isInteriorFacet_iff`), so the door-counting `adj` can branch on
it computably. -/
instance : DecidablePred (IsInteriorFacet : Fin (d + 1) → Prop) := fun k =>
  decidable_of_iff _ (isInteriorFacet_iff k).symm

/-- A Kuhn facet is a **geometric boundary facet** when it is the bottom facet
`0` or the top facet `Fin.last d` — the two facets of a chain with no interior
Freudenthal pivot partner. -/
def IsBoundaryFacet (k : Fin (d + 1)) : Prop := k = 0 ∨ k = Fin.last d

/-- **Boundary = exactly not-interior.**  A Kuhn facet carries no glued (pivot)
neighbour precisely when it is one of the two geometric boundary facets `0` or
`Fin.last d`.  This pins down exactly which facets the door-counting `adj` must
send to `none`, and is the index-level half of the eventual `boundary_face`
obligation: the `none` facets are exactly `{0, Fin.last d}`. -/
theorem not_isInteriorFacet_iff (k : Fin (d + 1)) :
    ¬ IsInteriorFacet k ↔ IsBoundaryFacet k := by
  rw [isInteriorFacet_iff, IsBoundaryFacet]
  have hk : (k : ℕ) ≤ d := by have := k.isLt; omega
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos (k : ℕ) with h0 | h0
    · exact Or.inl (Fin.ext (by rw [Fin.val_zero]; exact h0))
    · exact Or.inr (Fin.ext (by rw [Fin.val_last]; omega))
  · rintro (rfl | rfl)
    · rw [Fin.val_zero]; omega
    · rw [Fin.val_last]; omega

/-- **Every Kuhn facet is interior or boundary** (the two cases are exhaustive).
Together with `not_isInteriorFacet_iff` this is the clean dichotomy the door
count rests on: each cell has chain-interior facets (each carrying a pivot
neighbour) and the two boundary facets `0`, `Fin.last d`. -/
theorem isInteriorFacet_or_boundary (k : Fin (d + 1)) :
    IsInteriorFacet k ∨ IsBoundaryFacet k :=
  (em (IsInteriorFacet k)).imp id (not_isInteriorFacet_iff k).mp

/-- The two cases are **mutually exclusive**: a boundary facet is never interior. -/
theorem not_isInteriorFacet_of_boundary {k : Fin (d + 1)} (h : IsBoundaryFacet k) :
    ¬ IsInteriorFacet k := (not_isInteriorFacet_iff k).mpr h

/-!
## Boundary-face reduction to barycentric coordinates

The abstract `SpernerTriangulation.boundary_face` obligation, specialised to the
`gridVertices` carrier, asks that whenever the door-graph `adj` sends facet `k`
to `none`, every *other* vertex of the cell lies on the geometric face `k`
(`SpernerNDim.onFace _ k`).  Through the coordinate bridge `onFace_toVertex` this
is a purely barycentric statement: it says the `k`-th barycentric coordinate of
every vertex `j ≠ k` vanishes.

This section records that reduction once and for all, as the exact goal a total
`adj` must discharge at each facet it sends to `none`.  It does **not** decide
*which* facets are `none`: pinning that down is the remaining cross-chain gluing
frontier (a chain-boundary facet `k ∈ {0, Fin.last d}` that is interior to `Δ_N`
is glued to a cell in a *different* Kuhn chain, which `pivotSimplex` does not
produce — see the module header and `IsBoundaryFacet`).  Once that gluing (or a
proof that such a facet lies on `∂Δ_N`) is in place, `boundary_face` follows from
`boundary_face_iff_coords_zero` below.
-/

/-- **Carrier face condition = barycentric coordinate zero.**  A Kuhn vertex
`gridVertices s j` lies on the geometric face `k` exactly when the `k`-th
barycentric coordinate of the underlying grid vertex `s.verts j` is `0`.  This is
just the bridge `onFace_toVertex` transported along the defeq
`gridVertices s j = toVertex (s.verts j)`. -/
@[simp] theorem gridVertices_onFace_iff
    (s : SpernerGrid.GridSimplex d N) (j k : Fin (d + 1)) :
    SpernerNDim.onFace (gridVertices s j) k ↔ (s.verts j).coords k = 0 := by
  have h := onFace_toVertex (s.verts j) k
  simpa [gridVertices, SpernerGrid.BaryPoint.onFace] using h

/-- **Boundary-face obligation, reduced.**  For the `gridVertices` carrier, the
`boundary_face` requirement at facet `k` — that every vertex `j ≠ k` lies on
geometric face `k` — is equivalent to the barycentric statement that the `k`-th
coordinate of every such `s.verts j` vanishes.  A total door-graph `adj` discharges
`boundary_face` at each `none` facet `k` precisely by establishing the right-hand
side here. -/
theorem boundary_face_iff_coords_zero
    (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    (∀ j : Fin (d + 1), j ≠ k → SpernerNDim.onFace (gridVertices s j) k) ↔
    (∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0) := by
  constructor
  · intro h j hj; exact (gridVertices_onFace_iff s j k).mp (h j hj)
  · intro h j hj; exact (gridVertices_onFace_iff s j k).mpr (h j hj)

/-- The facet indexed by the cell's `miss` direction is **never** a geometric
boundary face (for `d ≥ 2`): its `boundary_face` coordinate condition fails.
Indeed the `miss` coordinate decreases by exactly `1` per step
(`GridSimplex.miss_coord_at`) from a base value `≥ d` (`GridSimplex.base_miss_ge_d`),
so among the two distinct vertices `0` and `⟨1, …⟩` — at least one of which differs
from the index `miss` — the one chosen still has `miss`-coordinate `≥ d - 1 ≥ 1 > 0`.
This is one concrete witness that the geometric `none` facets are **not** simply
read off the facet index, confirming the cross-chain frontier: the `miss` facet
carries an interior (pivot) partner, never an `adj = none`.  (The `d ≤ 1`
orientation-doubling case is handled separately.) -/
theorem miss_not_boundary_face (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    ¬ (∀ j : Fin (d + 1), j ≠ s.miss → (s.verts j).coords s.miss = 0) := by
  intro h
  have hbase : d ≤ (s.verts 0).coords s.miss := s.base_miss_ge_d
  have hlt : (1 : ℕ) < d + 1 := by omega
  set v1 : Fin (d + 1) := ⟨1, hlt⟩ with hv1
  have hv1val : v1.val = 1 := rfl
  by_cases hm : s.miss = (0 : Fin (d + 1))
  · -- miss = 0; use vertex v1 (≠ 0), whose miss-coord = base - 1 ≥ d - 1 ≥ 1
    have hne : v1 ≠ s.miss := by
      rw [hm]; exact Fin.ne_of_val_ne (by simp [hv1val])
    have hmca : (s.verts v1).coords s.miss = (s.verts 0).coords s.miss - v1.val :=
      s.miss_coord_at v1
    have := h v1 hne
    rw [hmca, hv1val] at this
    omega
  · -- miss ≠ 0; use vertex 0, whose miss-coord = base ≥ d ≥ 2 > 0
    have hne : (0 : Fin (d + 1)) ≠ s.miss := fun hc => hm hc.symm
    have := h 0 hne
    omega

/-!
## Per-vertex evaluation of the reduced boundary-coordinate condition

The previous section reduced `boundary_face` at a `none` facet `k` to the
barycentric statement `∀ j ≠ k, (s.verts j).coords k = 0`
(`boundary_face_iff_coords_zero`) but did **not** evaluate that coordinate
condition.  This section does, vertex by vertex, exploiting the fact that
`incDir : Fin d → Fin (d+1)` is a bijection onto the complement of `miss`
(`incDir_surj_complement`): every barycentric coordinate is *either* the `miss`
direction or exactly one increase direction `incDir k`.  So each
`(s.verts m).coords c = 0` test resolves into one of two closed forms:

  * **increase direction** `c = incDir k`: zero iff it starts at zero and step
    `k` has not yet occurred (`m.val ≤ k.val`) — `coord_incDir_eq_zero_iff`;
  * **miss direction** `c = miss`: zero iff `m` has reached the base value
    `(s.verts 0).coords miss` — `miss_coord_eq_zero_iff` — which, since that base
    value is `≥ d`, forces `m = Fin.last d` (`onFace_miss_imp_last`).

These are the evaluation lemmas a total `adj` will feed into
`boundary_face_iff_coords_zero`; they sharpen `miss_not_boundary_face` from a mere
existence witness into a full localization of *which* vertices fail.  All
0-sorry, 0-axiom.
-/

/-- **Vanishing of a non-miss coordinate, per vertex.**  The increase-direction
coordinate `incDir k` is zero at chain vertex `m` exactly when it starts at zero
(`(verts 0).coords (incDir k) = 0`) and step `k` has not yet been taken
(`m.val ≤ k.val`).  Direct consequence of the per-vertex formula
`coord_incDir_at`, which makes this coordinate `base + (1 if k < m else 0)`.
Complements `boundary_face_iff_coords_zero`: it evaluates the reduced coordinate
condition at every increase-direction facet. -/
theorem coord_incDir_eq_zero_iff (s : SpernerGrid.GridSimplex d N) (k : Fin d)
    (m : Fin (d + 1)) :
    (s.verts m).coords (s.incDir k) = 0 ↔
      (s.verts 0).coords (s.incDir k) = 0 ∧ m.val ≤ k.val := by
  rw [s.coord_incDir_at k m]
  by_cases h : k.val < m.val
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

/-- **Vanishing of the miss coordinate, per vertex.**  The `miss` coordinate is
zero at chain vertex `m` exactly when `m` has reached the base value:
`(verts 0).coords miss ≤ m.val`.  Direct consequence of `miss_coord_at`
(`miss` coordinate `= base - m`, truncated subtraction). -/
theorem miss_coord_eq_zero_iff (s : SpernerGrid.GridSimplex d N)
    (m : Fin (d + 1)) :
    (s.verts m).coords s.miss = 0 ↔ (s.verts 0).coords s.miss ≤ m.val := by
  rw [s.miss_coord_at m]; omega

/-- **The miss coordinate is positive away from the last vertex.**  Because the
base `miss` value is at least `d` and the coordinate only drops by one per step,
every chain vertex `m ≠ Fin.last d` still has a strictly positive `miss`
coordinate.  Sharpens `miss_not_boundary_face`: not merely *some* vertex but
*every* non-last vertex violates the `miss`-facet boundary condition. -/
theorem miss_coord_pos_of_ne_last (s : SpernerGrid.GridSimplex d N)
    (m : Fin (d + 1)) (hm : m ≠ Fin.last d) :
    0 < (s.verts m).coords s.miss := by
  have hge := s.miss_coord_ge m
  have hmd : m.val < d := by
    have hle : m.val ≤ d := Nat.lt_succ_iff.mp m.isLt
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (Fin.ext (h.trans (Fin.val_last d).symm)) hm
  omega

/-- **The miss-face is reached only by the last vertex.**  If grid vertex `m` lies
on the geometric `miss`-face (`(s.verts m).coords miss = 0`) then `m = Fin.last d`.
The pointwise localization behind `miss_not_boundary_face`: the geometric
`miss`-boundary touches a Freudenthal cell only at the extreme end of its chain
(and only in the extremal cell whose base `miss = d`). -/
theorem onFace_miss_imp_last (s : SpernerGrid.GridSimplex d N) (m : Fin (d + 1))
    (h : (s.verts m).coords s.miss = 0) : m = Fin.last d := by
  by_contra hm
  exact absurd h (Nat.pos_iff_ne_zero.mp (miss_coord_pos_of_ne_last s m hm))

/-!
## The total door-graph neighbour map

The interior/boundary dichotomy (`isInteriorFacet_or_boundary`,
`not_isInteriorFacet_iff`) and the interior-facet existence datum
(`exists_neighbor_of_isInteriorFacet`) are assembled here into a single
`Option`-valued neighbour function on Freudenthal cells: an interior Kuhn facet `k`
is sent to its glued pivot partner, and the two geometric boundary facets
`0`, `Fin.last d` are sent to `none`.

This is the concrete `adj`-shaped datum the abstract door-counting argument
consumes.  Its `= none` fibre is *exactly* `{0, Fin.last d}`
(`gridNeighbor_eq_none_iff`), so the index-level `boundary_face` bookkeeping reads
off the facet index directly; on every interior facet it returns a genuine glued,
distinct, facet-sharing neighbour (`gridNeighbor_spec`).  (The remaining content
of `adj` — that a chain-boundary facet interior to `Δ_N` is glued *across* Kuhn
chains — is the cross-chain frontier flagged in the module header and is not
produced by `pivotSimplex`; this map records the within-chain pivot structure.)
All 0-sorry; only the standard `Classical.choice` is used (to select the partner).
-/

/-- **Total neighbour map of the Freudenthal door graph.**  An interior facet `k`
is sent to its glued pivot partner (chosen via `exists_neighbor_of_isInteriorFacet`);
a boundary facet (`0` or `Fin.last d`) is sent to `none`. -/
noncomputable def gridNeighbor (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    Option (SpernerGrid.GridSimplex d N) :=
  if hk : IsInteriorFacet k then
    some (Classical.choose (exists_neighbor_of_isInteriorFacet s hk))
  else none

/-- **The `none` fibre is exactly the geometric boundary.**  `gridNeighbor s k`
returns `none` precisely at the two boundary facets `k ∈ {0, Fin.last d}`. -/
theorem gridNeighbor_eq_none_iff (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    gridNeighbor s k = none ↔ IsBoundaryFacet k := by
  unfold gridNeighbor
  by_cases hk : IsInteriorFacet k
  · simp only [dif_pos hk]
    constructor
    · intro h; exact absurd h (by simp)
    · intro h; exact absurd hk (not_isInteriorFacet_of_boundary h)
  · simp only [dif_neg hk]
    exact iff_of_true trivial ((not_isInteriorFacet_iff k).mp hk)

/-- **Interior facets get a genuine glued partner.**  On an interior facet `k` the
neighbour map returns `some t` where `t` is a distinct cell glued to `s` and
sharing the facet `k`. -/
theorem gridNeighbor_spec (s : SpernerGrid.GridSimplex d N) {k : Fin (d + 1)}
    (hk : IsInteriorFacet k) :
    ∃ t : SpernerGrid.GridSimplex d N, gridNeighbor s k = some t ∧
      GridGlued s t ∧ t ≠ s ∧ gridFacet t k = gridFacet s k := by
  refine ⟨Classical.choose (exists_neighbor_of_isInteriorFacet s hk), ?_,
    Classical.choose_spec (exists_neighbor_of_isInteriorFacet s hk)⟩
  unfold gridNeighbor; rw [dif_pos hk]

/-- A boundary facet is sent to `none` (the convenient direction of
`gridNeighbor_eq_none_iff`). -/
theorem gridNeighbor_boundary (s : SpernerGrid.GridSimplex d N) {k : Fin (d + 1)}
    (hk : IsBoundaryFacet k) : gridNeighbor s k = none :=
  (gridNeighbor_eq_none_iff s k).mpr hk

/-- The neighbour map is defined (returns `some`) at exactly the interior facets. -/
theorem gridNeighbor_isSome_iff (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    (gridNeighbor s k).isSome ↔ IsInteriorFacet k := by
  rw [Option.isSome_iff_ne_none, ne_eq, gridNeighbor_eq_none_iff]
  constructor
  · intro h; exact (isInteriorFacet_or_boundary k).resolve_right h
  · intro h hb; exact not_isInteriorFacet_of_boundary hb h

/-- **The door-graph neighbour map is an involution across each facet
(`adj_symm`, `d ≥ 2`).**  If facet `k` of `s` is glued to `t`
(`gridNeighbor s k = some t`), then facet `k` of `t` is glued back to `s`.

The proof pins the gluing direction down twice.  On the `s` side,
`gridNeighbor s k = some t` exposes `t` as the interior Freudenthal pivot of `s`
across some step pair `(a, b)`; but the shared facet forces that pivot index to be
`k` itself — a cell shares a given facet with at most one partner
(`gridFacet_unique_neighbor`), so the facet the pivot preserves (`a.succ`,
via `pivot_gridFacet_eq`) and the facet `k` that is actually glued must coincide.
The same argument on the `t` side forces `t`'s neighbour across `k` to be the pivot
in the *same* direction `(a, b)`, and `pivot_involutive` returns `s`.  This is the
constructive `adj_symm` obligation of the abstract door-counting graph.  (`d ≤ 1`
orientation doubling is handled separately.) -/
theorem gridNeighbor_involutive (hd : 2 ≤ d) (s : SpernerGrid.GridSimplex d N)
    {k : Fin (d + 1)} {t : SpernerGrid.GridSimplex d N}
    (h : gridNeighbor s k = some t) : gridNeighbor t k = some s := by
  -- `k` is interior because the neighbour map returned `some`.
  have hk : IsInteriorFacet k :=
    (gridNeighbor_isSome_iff s k).mp (by rw [h]; rfl)
  -- Identify `t` as the neighbour selected by `gridNeighbor s k`.
  obtain ⟨t', ht', hglst, _, hfacet⟩ := gridNeighbor_spec s hk
  rw [h] at ht'
  obtain rfl := Option.some.inj ht'
  -- `t` is the interior pivot of `s`; read off the step pair `(a, b)`.
  obtain ⟨a, b, hb, rfl⟩ := hglst
  -- The shared facet forces the pivot index to be `k` (uniqueness of the partner).
  have hak : a.succ = k :=
    gridFacet_unique_neighbor hd (pivot_ne s a b hb)
      (pivot_gridFacet_eq s a b hb) hfacet
  subst hak
  -- Describe `t`'s neighbour across the same facet `a.succ`.
  obtain ⟨u, hu, hglu, _, hfaceu⟩ := gridNeighbor_spec (pivotSimplex s a b hb) hk
  rw [hu]
  -- `u` is the pivot of `t` at `a.succ`; its direction is forced to `(a, b)` again.
  obtain ⟨a', b', hb', rfl⟩ := hglu
  have hak' : a'.succ = a.succ :=
    gridFacet_unique_neighbor hd (pivot_ne (pivotSimplex s a b hb) a' b' hb')
      (pivot_gridFacet_eq (pivotSimplex s a b hb) a' b' hb') hfaceu
  -- Eliminate the fresh direction `(a', b')` in favour of `(a, b)`.
  have haa : a = a' := (Fin.succ_inj.mp hak').symm
  have hbb : b = b' := (Fin.castSucc_inj.mp (hb'.symm.trans (hak'.trans hb))).symm
  subst haa hbb
  -- Two pivots across the same facet cancel: `pivot_involutive` returns `s`.
  exact congrArg some (pivot_involutive s a b hb)

/-- **`gridNeighbor` is symmetric as a relation (`adj_symm`).**  Restatement of
`gridNeighbor_involutive` in the "`t` is among `s`'s neighbours ↔ `s` is among
`t`'s" shape the abstract door graph consumes: for `d ≥ 2`, facet `k` glues `s`
to `t` exactly when it glues `t` to `s`. -/
theorem gridNeighbor_symm (hd : 2 ≤ d) (s t : SpernerGrid.GridSimplex d N)
    (k : Fin (d + 1)) :
    gridNeighbor s k = some t ↔ gridNeighbor t k = some s :=
  ⟨gridNeighbor_involutive hd s, gridNeighbor_involutive hd t⟩

-- ============================================================
-- SECTION: Barycentric facet algebra
-- ============================================================
-- The Kuhn-side `facet`/`adj_vertices` data above is the shape the
-- *abstract* `SpernerTriangulation` field demands.  But the eventual
-- `adj` (the Freudenthal pivot) is naturally defined on the concrete
-- `GridSimplex` in *barycentric* coordinates: pivoting across the
-- `k`-th facet replaces vertex `k` by a neighbour obtained by swapping
-- two consecutive `incDir` increments, an operation phrased over
-- `BaryPoint`s, not their Kuhn images.  To discharge `adj_vertices`
-- (`facet s k = facet s' k'`) and the cross-cell half of
-- `adj_unique_facet` it is therefore convenient to compute facet
-- equalities on the barycentric side and transport them across the
-- injective bridge `toVertex`.
--
-- This section sets up that transport: the *barycentric facet*
-- `baryFacet s k := (univ.erase k).image s.verts`, its image under
-- `toVertex` is exactly the Kuhn `facet s k`, and (because `toVertex`
-- is injective) Kuhn-facet equality is *equivalent* to barycentric-facet
-- equality.  The membership/cardinality/injectivity lemmas mirror the
-- Kuhn side verbatim, and `canon_eq_of_baryFacet_and_vertex` restates
-- the cell-recovery coherence entirely in barycentric data — the form
-- the pivot discharge will cite.  All 0-sorry, 0-axiom.

/-- The barycentric `k`-th **facet** of a canonical cell: the `d`-vertex
set of `BaryPoint`s obtained by deleting vertex `k`, *before* pushing
through the Kuhn bridge.  The Freudenthal pivot acts on these. -/
def baryFacet (s : CanonSimplex d N) (k : Fin (d + 1)) :
    Finset (SpernerGrid.BaryPoint d N) :=
  (Finset.univ.erase k).image s.1.verts

/-- Membership in a barycentric facet: a `BaryPoint` lies on `baryFacet s k`
exactly when it is one of the cell's vertices other than vertex `k`. -/
theorem mem_baryFacet_iff (s : CanonSimplex d N) (k : Fin (d + 1))
    (b : SpernerGrid.BaryPoint d N) :
    b ∈ baryFacet s k ↔ ∃ j : Fin (d + 1), j ≠ k ∧ s.1.verts j = b := by
  simp only [baryFacet, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]

/-- **The Kuhn facet is the image of the barycentric facet.**  Pushing
`baryFacet s k` through the bridge `toVertex` yields exactly the Kuhn-side
`facet s k`, since `vertices = toVertex ∘ verts`. -/
theorem facet_eq_image_baryFacet (s : CanonSimplex d N) (k : Fin (d + 1)) :
    facet s k = (baryFacet s k).image toVertex := by
  rw [facet, baryFacet, Finset.image_image]
  rfl

/-- Each barycentric facet carries exactly `d` vertices.  (Mirrors
`facet_card`, using per-cell barycentric vertex injectivity.) -/
theorem baryFacet_card (s : CanonSimplex d N) (k : Fin (d + 1)) :
    (baryFacet s k).card = d := by
  rw [baryFacet, Finset.card_image_of_injective _ s.1.verts_injective,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
    Fintype.card_fin]
  omega

/-- The deleted vertex is absent from its own barycentric facet. -/
theorem verts_not_mem_baryFacet (s : CanonSimplex d N) (k : Fin (d + 1)) :
    s.1.verts k ∉ baryFacet s k := by
  rw [mem_baryFacet_iff]
  rintro ⟨j, hjk, hj⟩
  exact hjk (s.1.verts_injective hj)

/-- **The `d + 1` barycentric facets of a single cell are distinct.**
The within-cell uniqueness underlying `adj_unique_facet`, stated on the
barycentric side. -/
theorem baryFacet_injective (s : CanonSimplex d N) :
    Function.Injective (baryFacet s) := by
  intro k₁ k₂ h
  by_contra hne
  have hmem : s.1.verts k₁ ∈ baryFacet s k₂ :=
    (mem_baryFacet_iff s k₂ _).mpr ⟨k₁, hne, rfl⟩
  rw [← h] at hmem
  exact verts_not_mem_baryFacet s k₁ hmem

/-- **Kuhn-facet equality ⇔ barycentric-facet equality.**  Because the
bridge `toVertex` is injective, the Kuhn facets of two (possibly
different) cells coincide exactly when their barycentric facets do.  This
is what lets the pivot's barycentric facet-sharing computation discharge
the abstract `adj_vertices` obligation (`facet s k = facet s' k'`). -/
theorem facet_eq_iff_baryFacet_eq (s t : CanonSimplex d N) (k l : Fin (d + 1)) :
    facet s k = facet t l ↔ baryFacet s k = baryFacet t l := by
  rw [facet_eq_image_baryFacet, facet_eq_image_baryFacet]
  constructor
  · intro h
    exact Finset.image_injective toVertex_injective h
  · intro h
    rw [h]

/-- **A canonical cell is determined by one barycentric facet and its
opposite vertex.**  The barycentric restatement of
`canon_eq_of_facet_and_vertex`: if two canonical cells share a barycentric
facet (`baryFacet s k = baryFacet t l`) together with the matching deleted
barycentric vertex (`verts k = verts l`), they are equal.  This is the
coherence the Freudenthal pivot needs in its own (barycentric) language:
the (facet, opposite-vertex) pair pins the cell down with no orientation
ambiguity. -/
theorem canon_eq_of_baryFacet_and_vertex {s t : CanonSimplex d N}
    {k l : Fin (d + 1)}
    (hface : baryFacet s k = baryFacet t l)
    (hvert : s.1.verts k = t.1.verts l) : s = t := by
  apply canon_eq_of_facet_and_vertex
  · rw [facet_eq_image_baryFacet, facet_eq_image_baryFacet, hface]
  · simp only [vertices, hvert]

/-!
## Geometric boundary faces are localized to the top facet `Fin.last d`

The previous sections reduced the `boundary_face` obligation to the barycentric
condition `∀ j ≠ k, (s.verts j).coords k = 0` (`boundary_face_iff_coords_zero`)
and evaluated it per vertex (`coord_incDir_eq_zero_iff`, `miss_coord_eq_zero_iff`).
This section runs that evaluation to its conclusion: **for `d ≥ 2` the only facet
`k` of a Freudenthal cell that can satisfy the boundary-coordinate condition is the
top facet `k = Fin.last d`.**

This *sharpens* the within-chain neighbour map's `none` fibre.  The map
`gridNeighbor` sends *both* index-level boundary facets `{0, Fin.last d}` to `none`
(`gridNeighbor_eq_none_iff`), but that is a within-chain artifact of `pivotSimplex`,
not the geometric truth: facet `0` (coordinate direction `0`) is generically *not*
a geometric boundary face — some cell vertex has positive `0`-coordinate — so it
must carry a cross-chain pivot partner.  Only `Fin.last d` survives as a candidate
geometric boundary facet.  This is exactly the localization the cross-chain gluing
frontier needs: it pins down *which* facet the missing partner construction has to
address (`0` interior to `Δ_N`), and confirms the top facet is the sole within-cell
door to `∂Δ_N`.  All 0-sorry, 0-axiom (builds only on `coord_incDir_eq_zero_iff`,
`miss_not_boundary_face`, and `incDir_surj_complement`).
-/

/-- **Increase-direction boundary faces hit the top vertex.**  If the boundary
coordinate condition holds at an increase-direction facet `incDir c` — every cell
vertex other than `incDir c` lies on geometric face `incDir c` — then `incDir c`
is the top facet `Fin.last d`.  Reason: the last chain vertex `Fin.last d` (value
`d`), if it is *not* the omitted vertex, must satisfy `d = (Fin.last d).val ≤ c.val`
by `coord_incDir_eq_zero_iff`, impossible since `c.val < d`. -/
theorem incDir_boundary_face_imp_last (s : SpernerGrid.GridSimplex d N) (c : Fin d)
    (h : ∀ j : Fin (d + 1), j ≠ s.incDir c → (s.verts j).coords (s.incDir c) = 0) :
    s.incDir c = Fin.last d := by
  by_contra hlast
  have hne : (Fin.last d) ≠ s.incDir c := fun heq => hlast heq.symm
  have hz := (coord_incDir_eq_zero_iff s c (Fin.last d)).mp (h (Fin.last d) hne)
  have hle : (Fin.last d).val ≤ c.val := hz.2
  rw [Fin.val_last] at hle
  have hc : c.val < d := c.isLt
  omega

/-- **Geometric boundary faces are localized to `Fin.last d`.**  For `d ≥ 2`, if a
facet `k` satisfies the boundary-coordinate condition (`∀ j ≠ k, (s.verts j).coords
k = 0`), then `k = Fin.last d`.  Every facet is either the `miss` direction —
excluded outright by `miss_not_boundary_face` — or an increase direction `incDir c`
(`incDir_surj_complement`), for which `incDir_boundary_face_imp_last` forces the top
facet.  So the *geometric* `none`-fibre of a Freudenthal cell is at most the
singleton `{Fin.last d}`, strictly inside the index-level boundary set
`{0, Fin.last d}` (`IsBoundaryFacet`). -/
theorem boundary_face_imp_last (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d)
    (k : Fin (d + 1))
    (h : ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0) :
    k = Fin.last d := by
  by_cases hk : k = s.miss
  · subst hk
    exact absurd h (miss_not_boundary_face s hd)
  · obtain ⟨c, hc⟩ := s.incDir_surj_complement k hk
    subst hc
    exact incDir_boundary_face_imp_last s c h

/-- **Carrier form of the localization.**  Discharged directly against the abstract
`boundary_face` obligation: if every vertex of the `gridVertices` carrier other than
`k` lies on the geometric face `k` (`SpernerNDim.onFace`), then `k = Fin.last d`
(for `d ≥ 2`).  This is the form a total door-graph `adj` consumes — it certifies
that the *only* facet it may legitimately send to `none` on geometric grounds is the
top facet. -/
theorem gridVertices_boundary_face_imp_last (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) (k : Fin (d + 1))
    (h : ∀ j : Fin (d + 1), j ≠ k → SpernerNDim.onFace (gridVertices s j) k) :
    k = Fin.last d := by
  refine boundary_face_imp_last s hd k (fun j hj => ?_)
  exact (gridVertices_onFace_iff s j k).mp (h j hj)

/-- **Facet `0` is never a geometric boundary face** (for `d ≥ 2`).  Immediate from
`boundary_face_imp_last`: were the boundary-coordinate condition to hold at `k = 0`,
localization would force `0 = Fin.last d`, contradicting `d ≥ 2`.  Concretely: the
`none` value `gridNeighbor` assigns to facet `0` is a *within-chain* artifact, and
`0` must carry a cross-chain pivot partner — this isolates the exact obligation the
gluing frontier still owes. -/
theorem zero_not_boundary_face (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    ¬ (∀ j : Fin (d + 1), j ≠ (0 : Fin (d + 1)) → (s.verts j).coords (0 : Fin (d + 1)) = 0) := by
  intro h
  have hk : (0 : Fin (d + 1)) = Fin.last d := boundary_face_imp_last s hd 0 h
  have : (0 : ℕ) = d := by
    have := congrArg Fin.val hk
    simpa [Fin.val_last] using this
  omega

/-!
## Exact characterization of the top-facet geometric boundary door

`boundary_face_imp_last` and `zero_not_boundary_face` pin down *which* facet index
could carry a genuine `∂Δ_N` door — only the top facet `Fin.last d`, never the
bottom facet `0`.  This section resolves the remaining question for the top facet:
*when* does facet `Fin.last d` actually lie on `∂Δ_N`?

The answer is a clean combinatorial condition on the Kuhn chain: the top facet is a
geometric boundary door **iff** the last increment step of the chain increases the
top coordinate (`incDir` sends the final step to `Fin.last d`) and that coordinate
already starts at zero on the base vertex.  Intuitively these are precisely the
Freudenthal cells whose final vertex is the *only* one off the face `Fin.last d`.

This is the constructive converse of `boundary_face_imp_last`: it does not merely
say a boundary door must be the top facet, it says exactly which cells realise one.
Together with `zero_not_boundary_face` it fully localizes the *geometric* `none`
fibre of the door graph, and identifies the cells the last-face door count runs
over.  All 0-sorry, 0-axiom (builds only on `coord_incDir_at`, `miss_coord_at`,
`incDir_surj_complement`). -/

/-- **Sufficient condition for a top-facet door.**  If the final Kuhn step
(`c.val = d - 1`) increases the top coordinate (`s.incDir c = Fin.last d`) and that
coordinate is zero on the base vertex, then every vertex other than the last lies on
the geometric face `Fin.last d`, i.e. facet `Fin.last d` is a boundary door.

Every chain vertex `j ≠ Fin.last d` satisfies `j.val ≤ d - 1 = c.val`, so by
`coord_incDir_at` the top coordinate there is still its base value `0` — the increment
occurs only at the final step, reaching the deleted last vertex. -/
theorem last_boundary_face_of_incDir_last (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) (c : Fin d) (hc : c.val = d - 1)
    (hInc : s.incDir c = Fin.last d)
    (hbase : (s.verts 0).coords (Fin.last d) = 0) :
    ∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0 := by
  intro j hj
  have hjd : j.val < d := by
    rcases Nat.lt_or_ge j.val d with h | h
    · exact h
    · have hjval : j.val = d := by have := j.isLt; omega
      exact absurd (Fin.ext (show j.val = (Fin.last d).val by
        rw [Fin.val_last]; exact hjval)) hj
  have hform := s.coord_incDir_at c j
  rw [hInc] at hform
  have hcj : ¬ c.val < j.val := by omega
  rw [hform, hbase, if_neg hcj]

/-- **Necessary condition for a top-facet door.**  If facet `Fin.last d` is a
geometric boundary door, then the top coordinate is *not* the `miss` direction, the
final Kuhn step (`c.val = d - 1`) increases it, and it starts at zero on the base.

The `miss` direction is excluded because its coordinate is strictly positive away
from the last vertex (`miss_coord_pos_of_ne_last`); the base value is read off at
vertex `0`; and were the increment step earlier than the last (`c.val < d - 1`), the
vertex `c.succ ≠ Fin.last d` would already carry a positive top coordinate. -/
theorem last_boundary_face_imp_incDir_last (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d)
    (h : ∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0) :
    ∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1 ∧
      (s.verts 0).coords (Fin.last d) = 0 := by
  have h0ne : (0 : Fin (d + 1)) ≠ Fin.last d := by
    intro hcon
    have : (0 : ℕ) = d := by
      have := congrArg Fin.val hcon; simpa [Fin.val_last] using this
    omega
  -- The top coordinate is not the miss direction.
  have hmiss : s.miss ≠ Fin.last d := by
    intro hml
    have hpos : 0 < (s.verts 0).coords s.miss := miss_coord_pos_of_ne_last s 0 h0ne
    have hz := h 0 h0ne
    rw [hml, hz] at hpos
    exact Nat.lt_irrefl 0 hpos
  obtain ⟨c, hc⟩ := s.incDir_surj_complement (Fin.last d) (fun heq => hmiss heq.symm)
  have hbase : (s.verts 0).coords (Fin.last d) = 0 := h 0 h0ne
  refine ⟨c, hc, ?_, hbase⟩
  by_contra hcv
  -- The increment step must be the final one, else `c.succ` carries a positive coord.
  have hsucc_ne : c.succ ≠ Fin.last d := by
    intro hcon
    have hval : c.succ.val = d := by rw [hcon, Fin.val_last]
    rw [Fin.val_succ] at hval
    omega
  have hform := s.coord_incDir_at c c.succ
  rw [hc] at hform
  have hcc : c.val < c.succ.val := by rw [Fin.val_succ]; omega
  rw [if_pos hcc, hbase] at hform
  have hz := h c.succ hsucc_ne
  rw [hz] at hform
  omega

/-- **Top-facet boundary door, characterized.**  Facet `Fin.last d` of a Freudenthal
cell is a geometric `∂Δ_N` door — every other vertex lies on the geometric face
`Fin.last d` — exactly when the final Kuhn step increases the top coordinate and that
coordinate starts at zero on the base vertex.  The exact converse-refinement of
`boundary_face_imp_last`, identifying the cells whose top facet the last-face door
count actually visits. -/
theorem last_boundary_face_iff (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0) ↔
    (∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1) ∧
      (s.verts 0).coords (Fin.last d) = 0 := by
  constructor
  · intro h
    obtain ⟨c, hc, hcv, hbase⟩ := last_boundary_face_imp_incDir_last s hd h
    exact ⟨⟨c, hc, hcv⟩, hbase⟩
  · rintro ⟨⟨c, hc, hcv⟩, hbase⟩
    exact last_boundary_face_of_incDir_last s hd c hcv hc hbase

/-- **Carrier form: facet `0` is never a boundary door.**  The `SpernerNDim.onFace`
restatement of `zero_not_boundary_face`: on the `gridVertices` carrier, the vertices
of a cell never all lie (apart from vertex `0`) on the geometric face `0`.  This is
the exact shape the abstract `SpernerTriangulation.boundary_face` field consumes. -/
theorem gridVertices_zero_not_boundary_face (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) :
    ¬ (∀ j : Fin (d + 1), j ≠ (0 : Fin (d + 1)) →
        SpernerNDim.onFace (gridVertices s j) (0 : Fin (d + 1))) := by
  intro h
  exact zero_not_boundary_face s hd
    (fun j hj => (gridVertices_onFace_iff s j 0).mp (h j hj))

/-- **The within-chain door map cannot discharge `boundary_face` at facet `0`.**  The
neighbour map `gridNeighbor` sends the bottom facet `0` to `none` (a within-chain
bookkeeping artifact — facet `0` has no Freudenthal pivot partner), yet facet `0` is
never a geometric `∂Δ_N` door.  So `gridNeighbor` alone does *not* satisfy the
abstract `boundary_face` obligation: any total `adj` must instead glue facet `0`
across Kuhn chains.  This certifies, as a theorem, the exact remaining cross-chain
frontier flagged throughout this development. -/
theorem gridNeighbor_zero_none_not_boundary_face (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) :
    gridNeighbor s (0 : Fin (d + 1)) = none ∧
    ¬ (∀ j : Fin (d + 1), j ≠ (0 : Fin (d + 1)) →
        SpernerNDim.onFace (gridVertices s j) (0 : Fin (d + 1))) :=
  ⟨gridNeighbor_boundary s (Or.inl rfl), gridVertices_zero_not_boundary_face s hd⟩

/-!
## At most one geometric boundary door per cell

`boundary_face_imp_last` forces every geometric `∂Δ_N` boundary face of a Freudenthal
cell to be the single top facet `Fin.last d`.  The immediate consequence is that a cell
has **at most one** boundary door — the "`0`-or-`1` door per cell" fact that a Phase-2
door-parity (oddness) induction depends on: each cell contributes an even (`0`) or the
single boundary door to the global door count, never two competing boundary facets.
-/

/-- **At most one geometric boundary door per cell.**  Any two facets of a Freudenthal
cell that are geometric `∂Δ_N` boundary faces coincide — each is forced to the top
facet `Fin.last d` by `boundary_face_imp_last`.  So the boundary-door facet of a cell,
if it exists, is unique. -/
theorem boundary_face_subsingleton (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d)
    {k₁ k₂ : Fin (d + 1)}
    (h₁ : ∀ j : Fin (d + 1), j ≠ k₁ → (s.verts j).coords k₁ = 0)
    (h₂ : ∀ j : Fin (d + 1), j ≠ k₂ → (s.verts j).coords k₂ = 0) :
    k₁ = k₂ := by
  rw [boundary_face_imp_last s hd k₁ h₁, boundary_face_imp_last s hd k₂ h₂]

/-- **Carrier form of at-most-one-door.**  The `SpernerNDim.onFace` restatement of
`boundary_face_subsingleton`, in the shape the abstract triangulation layer consumes. -/
theorem gridVertices_boundary_face_subsingleton (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) {k₁ k₂ : Fin (d + 1)}
    (h₁ : ∀ j : Fin (d + 1), j ≠ k₁ → SpernerNDim.onFace (gridVertices s j) k₁)
    (h₂ : ∀ j : Fin (d + 1), j ≠ k₂ → SpernerNDim.onFace (gridVertices s j) k₂) :
    k₁ = k₂ :=
  boundary_face_subsingleton s hd
    (fun j hj => (gridVertices_onFace_iff s j k₁).mp (h₁ j hj))
    (fun j hj => (gridVertices_onFace_iff s j k₂).mp (h₂ j hj))

/-- **The boundary-door facets of a cell number at most one.**  The finset of facet
indices that are geometric `∂Δ_N` boundary doors has cardinality `≤ 1`: it is either
empty or the singleton `{Fin.last d}`.  This is the per-cell contribution bound the
door-parity argument relies on. -/
theorem boundary_faces_card_le_one (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro k₁ hk₁ k₂ hk₂
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
  exact boundary_face_subsingleton s hd hk₁ hk₂

/-!
## Exact per-cell boundary-door set and count

`boundary_faces_card_le_one` bounds each cell's contribution to the last-face door
count by one.  This section computes that contribution *exactly*.  Localization
(`boundary_face_imp_last`) confines the door-facet finset to `{Fin.last d}`, and the
top-facet characterization (`last_boundary_face_iff`) says precisely when that facet
is a door.  Together they collapse the per-cell door set to a single decidable
alternative: the singleton `{Fin.last d}` when the top facet is a door, otherwise
`∅`.  The corresponding cardinality is the `0/1` summand a Phase-2 door-parity
(oddness) induction accumulates over all cells — this is the exact per-cell term that
sum runs over.  All 0-sorry, 0-axiom (builds only on `boundary_face_imp_last`). -/

/-- **Boundary-door facets are contained in `{Fin.last d}`.**  Sharpens
`boundary_faces_card_le_one` from a cardinality bound to a concrete containment: the
only facet index that can be a geometric `∂Δ_N` door is the top facet.  Immediate from
`boundary_face_imp_last`. -/
theorem boundary_faces_subset_last (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)) ⊆ {Fin.last d} := by
  intro k hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  rw [Finset.mem_singleton]
  exact boundary_face_imp_last s hd k hk

/-- **Membership in the boundary-door set.**  A facet `k` is a geometric `∂Δ_N` door of
the cell iff it is the top facet `Fin.last d` *and* the top-facet boundary condition
holds there.  The `∈`-form combining `boundary_face_imp_last` (only `Fin.last d`
qualifies) with the defining filter predicate. -/
theorem mem_boundary_faces_iff (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d)
    (k : Fin (d + 1)) :
    (k ∈ Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)) ↔
    k = Fin.last d ∧
      (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0) := by
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hk : k = Fin.last d := boundary_face_imp_last s hd k h
    subst hk
    exact ⟨rfl, h⟩
  · rintro ⟨hk, h⟩
    subst hk
    exact h

/-- **Exact per-cell boundary-door set.**  The finset of geometric `∂Δ_N` boundary
doors of a Freudenthal cell equals the singleton `{Fin.last d}` when the top-facet
door condition holds, and `∅` otherwise.  Pins the per-cell contribution to a single
decidable boolean — exactly the summand a Phase-2 door-parity induction accumulates. -/
theorem boundary_faces_eq (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)) =
    if (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0)
      then {Fin.last d} else ∅ := by
  by_cases hcond :
      (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0)
  · rw [if_pos hcond]
    apply Finset.ext
    intro k
    rw [mem_boundary_faces_iff s hd, Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, hcond⟩⟩
  · rw [if_neg hcond, Finset.eq_empty_iff_forall_not_mem]
    intro k hk
    rw [mem_boundary_faces_iff s hd] at hk
    exact hcond hk.2

/-- **Exact per-cell boundary-door count.**  The number of geometric `∂Δ_N` boundary
doors of a Freudenthal cell is `1` when its top facet is a door and `0` otherwise.
This is the exact `0/1` per-cell term the last-face door-parity sum accumulates,
strengthening `boundary_faces_card_le_one` from `≤ 1` to a decidable equality. -/
theorem boundary_faces_card (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)).card =
    if (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0)
      then 1 else 0 := by
  rw [boundary_faces_eq s hd]
  by_cases hcond :
      (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0)
  · rw [if_pos hcond, if_pos hcond, Finset.card_singleton]
  · rw [if_neg hcond, if_neg hcond, Finset.card_empty]

/-!
## Per-cell door count in Kuhn-increment form

`boundary_faces_eq`/`boundary_faces_card` express each cell's contribution to the
last-face door count through the *geometric* top-facet condition
`∀ j ≠ Fin.last d, (verts j).coords (Fin.last d) = 0`.  A Phase-2 door-parity
induction, however, does not accumulate over that geometric predicate directly: it
runs along the **Kuhn chains**, whose data is the increment directions `s.incDir` and
the base vertex `s.verts 0`.  `last_boundary_face_iff` is exactly the translation
between the two — the top facet is a geometric `∂Δ_N` door iff the *final* Kuhn step
(`c.val = d - 1`) increments the top coordinate (`s.incDir c = Fin.last d`) and that
coordinate starts at zero on the base.  This section restates the exact per-cell door
set (`boundary_faces_eq_incDir`) and count (`boundary_faces_card_incDir`) through that
Kuhn-increment predicate, so the global door sum can be reorganized along Kuhn chains
without ever re-deriving the geometric condition.  All 0-sorry, 0-axiom (builds only
on `boundary_faces_eq`/`boundary_faces_card` + `last_boundary_face_iff`). -/

/-- **Per-cell boundary-door set, in Kuhn-increment form.**  The finset of geometric
`∂Δ_N` boundary doors of a Freudenthal cell equals the singleton `{Fin.last d}`
exactly when the final Kuhn step increments the top coordinate
(`∃ c, s.incDir c = Fin.last d ∧ c.val = d - 1`) and that coordinate starts at zero on
the base vertex, and `∅` otherwise.  The `boundary_faces_eq` set re-expressed through
the Kuhn-increment data a dimensional induction runs over (via
`last_boundary_face_iff`). -/
theorem boundary_faces_eq_incDir (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)) =
    if ((∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1) ∧
        (s.verts 0).coords (Fin.last d) = 0)
      then {Fin.last d} else ∅ := by
  rw [boundary_faces_eq s hd]
  by_cases hcond :
      (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0)
  · rw [if_pos hcond, if_pos ((last_boundary_face_iff s hd).mp hcond)]
  · rw [if_neg hcond, if_neg (fun hk => hcond ((last_boundary_face_iff s hd).mpr hk))]

/-- **Per-cell boundary-door count, in Kuhn-increment form.**  The number of geometric
`∂Δ_N` boundary doors of a Freudenthal cell is `1` when the final Kuhn step increments
the top coordinate and that coordinate starts at zero on the base, and `0` otherwise.
The `boundary_faces_card` term re-expressed through the Kuhn-increment data — the exact
`0/1` summand a Phase-2 door-parity induction over Kuhn chains accumulates. -/
theorem boundary_faces_card_incDir (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)).card =
    if ((∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1) ∧
        (s.verts 0).coords (Fin.last d) = 0)
      then 1 else 0 := by
  rw [boundary_faces_card s hd]
  by_cases hcond :
      (∀ j : Fin (d + 1), j ≠ Fin.last d → (s.verts j).coords (Fin.last d) = 0)
  · rw [if_pos hcond, if_pos ((last_boundary_face_iff s hd).mp hcond)]
  · rw [if_neg hcond, if_neg (fun hk => hcond ((last_boundary_face_iff s hd).mpr hk))]

/-!
## Per-cell door indicator collapses to the single final Kuhn step

`boundary_faces_card_incDir` phrases the per-cell door term through the existential
`∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1` — "*some* Kuhn step is the final
one (`c.val = d - 1`) and increments the top coordinate".  But `c.val = d - 1` pins `c`
down to a *single* element of `Fin d` (there is exactly one index of value `d - 1`), so
the quantifier is spurious: the whole condition is decided by the one direction
`s.incDir` assigns to the final chain step `⟨d - 1, _⟩`.  `exists_incDir_last_iff`
discharges the collapse and `boundary_faces_card_lastStep` restates the door count
through it.  This is the sharpest per-cell form: a Phase-2 door-parity induction that
peels the last Kuhn step reads the `0/1` summand off a *single* increment-direction
evaluation, with no residual quantifier to carry.  All 0-sorry, 0-axiom (builds only on
`boundary_faces_card_incDir` + `Fin.ext`). -/

/-- The final Kuhn step of a `d`-chain is the unique index of value `d - 1`, so the
existential "*some* step is final and increments the top coordinate" collapses to a
single evaluation: `s.incDir ⟨d - 1, _⟩ = Fin.last d`. -/
theorem exists_incDir_last_iff (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1) ↔
      s.incDir ⟨d - 1, by omega⟩ = Fin.last d := by
  constructor
  · rintro ⟨c, hc, hcv⟩
    have hce : c = ⟨d - 1, by omega⟩ := Fin.ext hcv
    rwa [hce] at hc
  · intro h
    exact ⟨⟨d - 1, by omega⟩, h, rfl⟩

/-- **Per-cell boundary-door count, at the single final Kuhn step.**  The number of
geometric `∂Δ_N` boundary doors of a Freudenthal cell is `1` exactly when the final
chain step increments the top coordinate (`s.incDir ⟨d - 1, _⟩ = Fin.last d`) and that
coordinate starts at zero on the base vertex, and `0` otherwise.  The quantifier-free
form of `boundary_faces_card_incDir`: the `0/1` summand read off one increment
direction, the precise local datum a last-step door-parity induction accumulates. -/
theorem boundary_faces_card_lastStep (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) :
    (Finset.univ.filter
      (fun k : Fin (d + 1) =>
        ∀ j : Fin (d + 1), j ≠ k → (s.verts j).coords k = 0)).card =
    if (s.incDir ⟨d - 1, by omega⟩ = Fin.last d ∧
        (s.verts 0).coords (Fin.last d) = 0)
      then 1 else 0 := by
  rw [boundary_faces_card_incDir s hd]
  by_cases hstep :
      (∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1) ∧
        (s.verts 0).coords (Fin.last d) = 0
  · rw [if_pos hstep,
      if_pos ⟨(exists_incDir_last_iff s hd).mp hstep.1, hstep.2⟩]
  · rw [if_neg hstep,
      if_neg (fun h => hstep ⟨(exists_incDir_last_iff s hd).mpr h.1, h.2⟩)]


-- ============================================================
-- SECTION: Geometric ∂Δ_N boundary faces over ALL coordinates
-- ============================================================
-- The `boundary_face k` predicate used above tests the SINGLE
-- coordinate whose index matches the dropped facet index `k`
-- (`(verts j).coords k = 0`), because that is the obligation a
-- `gridNeighbor`-`none` facet discharges.  But the genuine
-- *geometric* question — "does facet `k` lie on `∂Δ_N`?" — is
-- whether the `d` vertices of the facet share a common vanishing
-- coordinate `i`, for ANY `i : Fin (d+1)`, not necessarily `i = k`.
--
-- This section proves that the geometric boundary condition is no
-- weaker: a facet lies on `∂Δ_N` (any coordinate hyperplane) ONLY
-- for the top facet `k = Fin.last d`.  In particular facet `0` lies
-- on NO coordinate hyperplane — it is ALWAYS strictly interior to
-- `Δ_N`.  This settles the Phase-1 frontier dichotomy: the option
-- "route facet `0` to `∂Δ_N` so `adj = none` is sound" is
-- impossible, so the cross-`miss` partner construction for facet `0`
-- is unavoidable.  All 0-sorry, 0-axiom (builds only on
-- `coord_incDir_at`, `miss_coord_pos_of_ne_last`, and
-- `incDir_surj_complement`).

/-- **Geometric boundary faces are localized to the top facet.**
If some coordinate `i` vanishes at every vertex of facet `k`
(every `j ≠ k`), then `k = Fin.last d`.  Generalizes
`boundary_face_imp_last` from the index-matched coordinate `i = k`
to an ARBITRARY coordinate `i`: no matter which hyperplane the
facet is tested against, only the top facet can lie on it.

The `miss` coordinate is excluded because it is positive at every
non-top vertex (`miss_coord_pos_of_ne_last`), and a facet with
`2 ≤ d` contains at least one non-top vertex `≠ k`.  An
increase-direction coordinate `incDir c` is excluded unless the top
vertex is the dropped one, since at `Fin.last d` its value is
`base + 1 ≥ 1 > 0` (`coord_incDir_at`, as `c.val < d`). -/
theorem geom_boundary_face_imp_last (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) (k : Fin (d + 1))
    (h : ∃ i : Fin (d + 1), ∀ j : Fin (d + 1), j ≠ k →
      (s.verts j).coords i = 0) :
    k = Fin.last d := by
  obtain ⟨i, hi⟩ := h
  by_cases hmiss : i = s.miss
  · -- `i = miss`: impossible outright.  Pick a vertex `j ≠ k` with
    -- `j ≠ Fin.last d` (available since `d ≥ 2` gives `≥ 3` indices);
    -- its `miss` coordinate is positive, contradicting `hi j`.
    subst hmiss
    exfalso
    have hlast0 : (0 : Fin (d + 1)) ≠ Fin.last d := by
      rw [Ne, Fin.ext_iff]; simp only [Fin.val_zero, Fin.val_last]; omega
    have hlast1 : (⟨1, by omega⟩ : Fin (d + 1)) ≠ Fin.last d := by
      rw [Ne, Fin.ext_iff]; simp only [Fin.val_last]; omega
    by_cases hk0 : (0 : Fin (d + 1)) = k
    · -- `k = 0`, so use `j = 1`.
      have hne : (⟨1, by omega⟩ : Fin (d + 1)) ≠ k := by
        rw [← hk0, Ne, Fin.ext_iff]; simp
      have hz := hi ⟨1, by omega⟩ hne
      have hpos := miss_coord_pos_of_ne_last s ⟨1, by omega⟩ hlast1
      omega
    · -- `k ≠ 0`, so use `j = 0`.
      have hz := hi 0 hk0
      have hpos := miss_coord_pos_of_ne_last s 0 hlast0
      omega
  · -- `i = incDir c` for some `c` (surjectivity onto the miss
    -- complement).  If `k ≠ Fin.last d`, apply `hi` at the top
    -- vertex `Fin.last d`; `coord_incDir_at` makes that coordinate
    -- `base + 1`, contradicting `= 0`.
    obtain ⟨c, hc⟩ := s.incDir_surj_complement i hmiss
    subst hc
    by_contra hk
    have hne : (Fin.last d) ≠ k := fun h => hk h.symm
    have hz := hi (Fin.last d) hne
    rw [s.coord_incDir_at c (Fin.last d)] at hz
    have hcd : c.val < (Fin.last d).val := by
      simp only [Fin.val_last]; exact c.isLt
    simp only [hcd, if_true] at hz
    omega

/-- Carrier (`SpernerNDim.onFace`) form of
`geom_boundary_face_imp_last`. -/
theorem gridVertices_geom_boundary_face_imp_last
    (s : SpernerGrid.GridSimplex d N) (hd : 2 ≤ d) (k : Fin (d + 1))
    (h : ∃ i : Fin (d + 1), ∀ j : Fin (d + 1), j ≠ k →
      SpernerNDim.onFace (gridVertices s j) i) :
    k = Fin.last d := by
  apply geom_boundary_face_imp_last s hd k
  obtain ⟨i, hi⟩ := h
  exact ⟨i, fun j hj => (gridVertices_onFace_iff s j i).mp (hi j hj)⟩

/-- **Facet `0` is always strictly interior to `Δ_N`.**  No
coordinate hyperplane contains all of facet `0`'s vertices
`{verts 1, …, verts d}`.  Immediate from
`geom_boundary_face_imp_last` (facet `0` on `∂Δ_N` would force
`0 = Fin.last d`, false for `d ≥ 2`).  Consequence for Phase-1:
facet `0` has NO geometric escape to `∂Δ_N`, so a total triangulation
`adj` cannot legitimately send it to `none` — the cross-`miss`
partner cell for facet `0` must be constructed. -/
theorem zero_facet_not_on_boundary (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) :
    ¬ ∃ i : Fin (d + 1), ∀ j : Fin (d + 1), j ≠ 0 →
      (s.verts j).coords i = 0 := by
  intro h
  have hk := geom_boundary_face_imp_last s hd 0 h
  rw [Fin.ext_iff] at hk
  simp only [Fin.val_zero, Fin.val_last] at hk
  omega

/-- **Exact cross-chain gluing obligation.**  A facet `k` is one the within-chain
neighbour map `gridNeighbor` fails to pair (`gridNeighbor s k = none`) yet is *not* a
genuine geometric `∂Δ_N` door — precisely the facets a *total*
`SpernerTriangulation.adj` must glue across Kuhn chains — **exactly** when it is the
bottom facet `k = 0` (unconditionally, by `zero_facet_not_on_boundary`) or the top
facet `k = Fin.last d` in a cell whose top facet is *not* a door.

This consolidates the two endpoint analyses — the bottom-facet fact
(`gridNeighbor_zero_none_not_boundary_face` / `zero_facet_not_on_boundary`) and the
geometric localization to the top facet (`geom_boundary_face_imp_last`) — into the
complete dichotomy over *all* facets.  It pins the remaining cross-chain frontier
exactly: facet `0` is the unavoidable gluing site for every cell, while facet
`Fin.last d` needs gluing precisely for the cells whose last facet is geometrically
interior (i.e. not a last-face door, the `¬`-branch of `boundary_faces_eq`).  Every
interior facet `0 < k < Fin.last d` is excluded because `gridNeighbor` already pairs
it (`gridNeighbor_isSome_iff`), so no residual obligation there.

Only endpoint lemmas are used: `gridNeighbor_eq_none_iff` (the `none` fibre is
`{0, Fin.last d}`) and `zero_facet_not_on_boundary`; 0-sorry, 0-axiom. -/
theorem gridNeighbor_none_geom_interior_iff (s : SpernerGrid.GridSimplex d N)
    (hd : 2 ≤ d) (k : Fin (d + 1)) :
    (gridNeighbor s k = none ∧
        ¬ ∃ i : Fin (d + 1), ∀ j : Fin (d + 1), j ≠ k →
          (s.verts j).coords i = 0) ↔
      (k = 0 ∨
        (k = Fin.last d ∧
          ¬ ∃ i : Fin (d + 1), ∀ j : Fin (d + 1), j ≠ Fin.last d →
            (s.verts j).coords i = 0)) := by
  constructor
  · rintro ⟨hnone, hgeom⟩
    have hb : k = 0 ∨ k = Fin.last d := (gridNeighbor_eq_none_iff s k).mp hnone
    rcases hb with h0 | hlast
    · exact Or.inl h0
    · exact Or.inr ⟨hlast, by rw [← hlast]; exact hgeom⟩
  · rintro (h0 | ⟨hlast, hgeom⟩)
    · subst h0
      exact ⟨(gridNeighbor_eq_none_iff s 0).mpr (Or.inl rfl),
        zero_facet_not_on_boundary s hd⟩
    · subst hlast
      exact ⟨(gridNeighbor_eq_none_iff s (Fin.last d)).mpr (Or.inr rfl), hgeom⟩

/-!
## Toward the facet-`0` cross-chain partner cell

`gridNeighbor_none_geom_interior_iff` pins the remaining obstruction: facet `0`
is *always* an unpaired, geometrically-interior facet, so a total triangulation
`adj` must supply a partner cell across Kuhn chains.  The Freudenthal rule for
the facet-`0` pivot advances the *last* vertex one more step in the single
*omitted* increment direction `incDir 0` (taking the unit from `miss`), so the
new cell shares the facet `{verts 1, …, verts d}` and replaces the dropped base
`verts 0` by a genuinely new top vertex.

This section constructs that new top vertex (`zeroPivotTop`), computes its
coordinates, proves it is a *new* point (leaves `s`'s chain — the hallmark of a
distinct neighbouring cell), and isolates the exact arithmetic feasibility
regime of the construction (`zeroPivot_feasible_iff`).  All 0-sorry, 0-axiom;
they build only on the `GridSimplex` chain primitives of
`Proofs.SpernerGridBase`. -/

/-- Candidate new top vertex of the facet-`0` cross-chain partner cell.
It is the last vertex advanced one more step in the *omitted* increment
direction `incDir 0` (with the usual unit taken from the `miss`
coordinate): `verts (last) + e_{incDir 0} - e_miss`.  Feasible exactly
when the top vertex still has a positive `miss` coordinate. -/
def zeroPivotTop (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    BaryPoint d N where
  coords := fun j =>
    if j = s.incDir ⟨0, hd1⟩ then (s.verts (Fin.last d)).coords j + 1
    else if j = s.miss then (s.verts (Fin.last d)).coords j - 1
    else (s.verts (Fin.last d)).coords j
  sum_eq := by
    set p := s.incDir ⟨0, hd1⟩ with hp
    set q := s.miss with hq
    set V := s.verts (Fin.last d) with hV
    have hpq : p ≠ q := s.miss_ne_inc ⟨0, hd1⟩
    have key : ∀ j : Fin (d + 1),
        (if j = p then V.coords j + 1
          else if j = q then V.coords j - 1 else V.coords j)
        + (if j = q then 1 else 0)
        = V.coords j + (if j = p then 1 else 0) := by
      intro j
      by_cases h1 : j = p
      · subst h1
        rw [if_pos rfl, if_neg hpq, if_pos rfl]
      · by_cases h2 : j = q
        · subst h2
          rw [if_neg h1, if_pos rfl, if_pos rfl, if_neg h1]
          have : 1 ≤ V.coords q := hfeas
          omega
        · rw [if_neg h1, if_neg h2, if_neg h2, if_neg h1]
    have hone_p : (∑ j : Fin (d + 1), (if j = p then (1 : ℕ) else 0)) = 1 := by simp
    have hone_q : (∑ j : Fin (d + 1), (if j = q then (1 : ℕ) else 0)) = 1 := by simp
    have hsum :
        (∑ j : Fin (d + 1),
            (if j = p then V.coords j + 1
              else if j = q then V.coords j - 1 else V.coords j)) + 1
          = (∑ j : Fin (d + 1), V.coords j) + 1 := by
      calc
        (∑ j : Fin (d + 1),
            (if j = p then V.coords j + 1
              else if j = q then V.coords j - 1 else V.coords j)) + 1
            = (∑ j : Fin (d + 1),
                (if j = p then V.coords j + 1
                  else if j = q then V.coords j - 1 else V.coords j))
              + (∑ j : Fin (d + 1), (if j = q then (1 : ℕ) else 0)) := by rw [hone_q]
          _ = ∑ j : Fin (d + 1),
                ((if j = p then V.coords j + 1
                    else if j = q then V.coords j - 1 else V.coords j)
                  + (if j = q then (1 : ℕ) else 0)) := by rw [Finset.sum_add_distrib]
          _ = ∑ j : Fin (d + 1),
                (V.coords j + (if j = p then (1 : ℕ) else 0)) :=
                Finset.sum_congr rfl (fun j _ => key j)
          _ = (∑ j : Fin (d + 1), V.coords j)
                + (∑ j : Fin (d + 1), (if j = p then (1 : ℕ) else 0)) := by
                rw [Finset.sum_add_distrib]
          _ = (∑ j : Fin (d + 1), V.coords j) + 1 := by rw [hone_p]
    rw [V.sum_eq] at hsum
    omega

/-- Coordinate of `zeroPivotTop` at the omitted direction `incDir 0`. -/
theorem zeroPivotTop_coords_incDir0 (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (zeroPivotTop s hd1 hfeas).coords (s.incDir ⟨0, hd1⟩)
      = (s.verts (Fin.last d)).coords (s.incDir ⟨0, hd1⟩) + 1 := by
  show (if s.incDir ⟨0, hd1⟩ = s.incDir ⟨0, hd1⟩ then _ else _) = _
  rw [if_pos rfl]

/-- Coordinate of `zeroPivotTop` at the `miss` direction. -/
theorem zeroPivotTop_coords_miss (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (zeroPivotTop s hd1 hfeas).coords s.miss
      = (s.verts (Fin.last d)).coords s.miss - 1 := by
  have hpq : s.miss ≠ s.incDir ⟨0, hd1⟩ := fun h => s.miss_ne_inc ⟨0, hd1⟩ h.symm
  show (if s.miss = s.incDir ⟨0, hd1⟩ then _ else if s.miss = s.miss then _ else _) = _
  rw [if_neg hpq, if_pos rfl]

/-- Coordinate of `zeroPivotTop` at any other direction: unchanged from the
last vertex. -/
theorem zeroPivotTop_coords_other (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss)
    (j : Fin (d + 1)) (hjp : j ≠ s.incDir ⟨0, hd1⟩) (hjq : j ≠ s.miss) :
    (zeroPivotTop s hd1 hfeas).coords j
      = (s.verts (Fin.last d)).coords j := by
  show (if j = s.incDir ⟨0, hd1⟩ then _ else if j = s.miss then _ else _) = _
  rw [if_neg hjp, if_neg hjq]

/-- The `incDir 0` coordinate of the top vertex equals the base value plus one:
the omitted direction increases exactly once along `s`'s chain (at step 0) and
never again, so it is `base + 1` at every vertex from `verts 1` onward. -/
theorem top_incDir0_coord (s : GridSimplex d N) (hd1 : 0 < d) :
    (s.verts (Fin.last d)).coords (s.incDir ⟨0, hd1⟩)
      = (s.verts 0).coords (s.incDir ⟨0, hd1⟩) + 1 := by
  have hle : (⟨0, hd1⟩ : Fin d).succ ≤ Fin.last d := by
    simp [Fin.le_iff_val_le_val, Fin.succ, Fin.last]; omega
  have hca := s.incDir_const_after ⟨0, hd1⟩ (Fin.last d) hle
  have hstep := s.step_inc ⟨0, hd1⟩
  have hcs : (⟨0, hd1⟩ : Fin d).castSucc = (0 : Fin (d + 1)) := by
    apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
  rw [hca, hstep, hcs]

/-- The partner's top vertex has `incDir 0` coordinate `base + 2`, strictly
above the maximum value (`base + 1`) that coordinate attains anywhere on `s`'s
own chain — so the new vertex genuinely leaves the original cell. -/
theorem zeroPivotTop_incDir0_coord (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (zeroPivotTop s hd1 hfeas).coords (s.incDir ⟨0, hd1⟩)
      = (s.verts 0).coords (s.incDir ⟨0, hd1⟩) + 2 := by
  rw [zeroPivotTop_coords_incDir0, top_incDir0_coord]

/-- Along `s`'s chain the `incDir 0` coordinate never exceeds `base + 1`. -/
theorem chain_incDir0_le (s : GridSimplex d N) (hd1 : 0 < d) (j : Fin (d + 1)) :
    (s.verts j).coords (s.incDir ⟨0, hd1⟩)
      ≤ (s.verts 0).coords (s.incDir ⟨0, hd1⟩) + 1 := by
  rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
  · have : j = 0 := Fin.ext hj0
    rw [this]; omega
  · have hle : (⟨0, hd1⟩ : Fin d).succ ≤ j := by
      simp [Fin.le_iff_val_le_val, Fin.succ]; omega
    have hca := s.incDir_const_after ⟨0, hd1⟩ j hle
    have hstep := s.step_inc ⟨0, hd1⟩
    have hcs : (⟨0, hd1⟩ : Fin d).castSucc = (0 : Fin (d + 1)) := by
      apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
    rw [hca, hstep, hcs]

/-- **The partner's top vertex is genuinely new.**  `zeroPivotTop` coincides
with no vertex of `s`'s chain: its `incDir 0` coordinate (`base + 2`) exceeds the
chain maximum (`base + 1`).  So the facet-`0` partner cell is a *distinct* filling
of the shared facet `{verts 1, …, verts d}`, not `s` itself. -/
theorem zeroPivotTop_not_mem_chain (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) (j : Fin (d + 1)) :
    zeroPivotTop s hd1 hfeas ≠ s.verts j := by
  intro h
  have h1 := zeroPivotTop_incDir0_coord s hd1 hfeas
  have h2 := chain_incDir0_le s hd1 j
  rw [h] at h1
  omega

/-- **Feasibility dichotomy for the same-`miss` facet-`0` pivot.**  The partner's
top vertex is constructible (its `miss` coordinate stays nonnegative) exactly when
the base `miss` value is at least `d + 1`.  The complementary regime — base
`miss = d` (the extremal cell, whose top vertex already sits on the geometric
`miss`-face) — is precisely where the facet-`0` partner must instead cross to a
different `miss` fibre. -/
theorem zeroPivot_feasible_iff (s : GridSimplex d N) :
    1 ≤ (s.verts (Fin.last d)).coords s.miss
      ↔ d + 1 ≤ (s.verts 0).coords s.miss := by
  rw [s.miss_coord_at (Fin.last d)]
  simp only [Fin.val_last]
  have hge := s.base_miss_ge_d
  omega

-- ============================================================
-- SECTION: The facet-`0` cross-chain partner cell (feasible regime)
-- ============================================================
-- `zeroPivotTop` supplies the single new top vertex; this section
-- assembles the FULL neighbouring `GridSimplex`.  In the feasible
-- regime (`base miss ≥ d + 1`, equivalently top `miss ≥ 1`,
-- `zeroPivot_feasible_iff`) the facet-`0` partner keeps the same
-- `miss` direction and reuses `s`'s upper chain `verts 1, …, verts d`,
-- appending `zeroPivotTop` as its new last vertex.  Its increment
-- order is `s`'s cyclically rotated by one — `incDir 1, …,
-- incDir (d-1), incDir 0` — deferring the single omitted direction
-- `incDir 0` to the final step, exactly the Freudenthal facet-`0`
-- pivot.  This produces a bona-fide `GridSimplex` (`zeroPivotCell`)
-- that (i) reuses `s`'s upper chain as its own bottom `d` vertices —
-- so it shares the facet `{verts 1, …, verts d}` obtained by dropping
-- its last vertex — and (ii) is distinct from `s` (`zeroPivotCell_ne`).
-- All 0-sorry, 0-axiom; builds only on the `GridSimplex` chain
-- primitives and the `zeroPivotTop` coordinate lemmas above.

/-- Vertices of the facet-`0` partner cell: `s`'s upper chain
`verts 1, …, verts d` (at indices `0, …, d-1`) followed by the new top
vertex `zeroPivotTop` (at index `d`). -/
def zeroPivotVerts (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    Fin (d + 1) → BaryPoint d N :=
  fun k => if h : k.val < d then s.verts ⟨k.val + 1, by omega⟩
    else zeroPivotTop s hd1 hfeas

/-- Increment directions of the partner cell: `s`'s directions cyclically
rotated so the omitted direction `incDir 0` fires on the final step. -/
def zeroPivotInc (s : GridSimplex d N) (hd1 : 0 < d) :
    Fin d → Fin (d + 1) :=
  fun k => if h : k.val + 1 < d then s.incDir ⟨k.val + 1, h⟩
    else s.incDir ⟨0, hd1⟩

theorem zeroPivotVerts_of_lt (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss)
    (k : Fin (d + 1)) (h : k.val < d) :
    zeroPivotVerts s hd1 hfeas k = s.verts ⟨k.val + 1, by omega⟩ := by
  simp only [zeroPivotVerts, dif_pos h]

theorem zeroPivotVerts_last (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    zeroPivotVerts s hd1 hfeas (Fin.last d) = zeroPivotTop s hd1 hfeas := by
  have h : ¬ (Fin.last d).val < d := by simp [Fin.val_last]
  simp only [zeroPivotVerts, dif_neg h]

theorem zeroPivotInc_of_lt (s : GridSimplex d N) (hd1 : 0 < d)
    (k : Fin d) (h : k.val + 1 < d) :
    zeroPivotInc s hd1 k = s.incDir ⟨k.val + 1, h⟩ := by
  simp only [zeroPivotInc, dif_pos h]

theorem zeroPivotInc_last (s : GridSimplex d N) (hd1 : 0 < d)
    (k : Fin d) (h : ¬ k.val + 1 < d) :
    zeroPivotInc s hd1 k = s.incDir ⟨0, hd1⟩ := by
  simp only [zeroPivotInc, dif_neg h]

/-- Evaluation of the partner's vertices at `k.castSucc` (a lower-chain
vertex): it is `s.verts (k+1)`. -/
theorem zeroPivotVerts_castSucc (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) (k : Fin d) :
    zeroPivotVerts s hd1 hfeas k.castSucc = s.verts ⟨k.val + 1, by omega⟩ := by
  have h : (k.castSucc).val < d := by simp [Fin.coe_castSucc, k.isLt]
  rw [zeroPivotVerts_of_lt s hd1 hfeas _ h]
  apply congrArg; apply Fin.ext; simp [Fin.coe_castSucc]

/-- Evaluation of the partner's vertices at `k.succ` for an interior step
(`k+1 < d`): it is `s.verts (k+2)`. -/
theorem zeroPivotVerts_succ_of_lt (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) (k : Fin d)
    (hlt : k.val + 1 < d) :
    zeroPivotVerts s hd1 hfeas k.succ = s.verts ⟨k.val + 2, by omega⟩ := by
  have h : (k.succ).val < d := by simpa [Fin.val_succ] using hlt
  rw [zeroPivotVerts_of_lt s hd1 hfeas _ h]
  apply congrArg; apply Fin.ext; simp [Fin.val_succ]

/-- Evaluation of the partner's vertices at `k.succ` for the final step
(`k+1 = d`): it is the new top vertex `zeroPivotTop`. -/
theorem zeroPivotVerts_succ_last (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) (k : Fin d)
    (hlast : k.val + 1 = d) :
    zeroPivotVerts s hd1 hfeas k.succ = zeroPivotTop s hd1 hfeas := by
  have hk : k.succ = Fin.last d := by apply Fin.ext; simp [Fin.val_succ, hlast]
  rw [hk, zeroPivotVerts_last]

/-- **The facet-`0` cross-chain partner cell.**  A bona-fide `GridSimplex`
whose bottom `d` vertices are `s`'s upper chain `verts 1, …, verts d` and
whose top vertex is `zeroPivotTop`, with increment order `s`'s cyclic
rotation and the same `miss` direction.  Defined in the feasible regime
`top miss ≥ 1`. -/
def zeroPivotCell (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    GridSimplex d N where
  verts := zeroPivotVerts s hd1 hfeas
  incDir := zeroPivotInc s hd1
  miss := s.miss
  miss_ne_inc := by
    intro k
    by_cases hlt : k.val + 1 < d
    · rw [zeroPivotInc_of_lt s hd1 k hlt]; exact s.miss_ne_inc _
    · rw [zeroPivotInc_last s hd1 k hlt]; exact s.miss_ne_inc _
  step_inc := by
    intro k
    have hk := k.isLt
    by_cases hlt : k.val + 1 < d
    · set m : Fin d := ⟨k.val + 1, hlt⟩ with hm
      have ec : zeroPivotVerts s hd1 hfeas k.castSucc = s.verts m.castSucc := by
        rw [zeroPivotVerts_castSucc]; apply congrArg; apply Fin.ext
        simp [hm]
      have es : zeroPivotVerts s hd1 hfeas k.succ = s.verts m.succ := by
        rw [zeroPivotVerts_succ_of_lt s hd1 hfeas k hlt]; apply congrArg; apply Fin.ext
        simp [hm]
      have ei : zeroPivotInc s hd1 k = s.incDir m := zeroPivotInc_of_lt s hd1 k hlt
      rw [ec, es, ei]; exact s.step_inc m
    · have hlast : k.val + 1 = d := by omega
      have ec : zeroPivotVerts s hd1 hfeas k.castSucc = s.verts (Fin.last d) := by
        rw [zeroPivotVerts_castSucc]; apply congrArg; apply Fin.ext
        simp [Fin.val_last]; omega
      have es : zeroPivotVerts s hd1 hfeas k.succ = zeroPivotTop s hd1 hfeas :=
        zeroPivotVerts_succ_last s hd1 hfeas k hlast
      have ei : zeroPivotInc s hd1 k = s.incDir ⟨0, hd1⟩ :=
        zeroPivotInc_last s hd1 k (by omega)
      rw [ec, es, ei]; exact zeroPivotTop_coords_incDir0 s hd1 hfeas
  step_dec := by
    intro k
    have hk := k.isLt
    by_cases hlt : k.val + 1 < d
    · set m : Fin d := ⟨k.val + 1, hlt⟩ with hm
      have ec : zeroPivotVerts s hd1 hfeas k.castSucc = s.verts m.castSucc := by
        rw [zeroPivotVerts_castSucc]; apply congrArg; apply Fin.ext
        simp [hm]
      have es : zeroPivotVerts s hd1 hfeas k.succ = s.verts m.succ := by
        rw [zeroPivotVerts_succ_of_lt s hd1 hfeas k hlt]; apply congrArg; apply Fin.ext
        simp [hm]
      rw [ec, es]; exact s.step_dec m
    · have hlast : k.val + 1 = d := by omega
      have ec : zeroPivotVerts s hd1 hfeas k.castSucc = s.verts (Fin.last d) := by
        rw [zeroPivotVerts_castSucc]; apply congrArg; apply Fin.ext
        simp [Fin.val_last]; omega
      have es : zeroPivotVerts s hd1 hfeas k.succ = zeroPivotTop s hd1 hfeas :=
        zeroPivotVerts_succ_last s hd1 hfeas k hlast
      rw [ec, es, zeroPivotTop_coords_miss]; omega
  step_same := by
    intro k j hj1 hj2
    have hk := k.isLt
    by_cases hlt : k.val + 1 < d
    · set m : Fin d := ⟨k.val + 1, hlt⟩ with hm
      have ei : zeroPivotInc s hd1 k = s.incDir m := zeroPivotInc_of_lt s hd1 k hlt
      rw [ei] at hj1
      have ec : zeroPivotVerts s hd1 hfeas k.castSucc = s.verts m.castSucc := by
        rw [zeroPivotVerts_castSucc]; apply congrArg; apply Fin.ext
        simp [hm]
      have es : zeroPivotVerts s hd1 hfeas k.succ = s.verts m.succ := by
        rw [zeroPivotVerts_succ_of_lt s hd1 hfeas k hlt]; apply congrArg; apply Fin.ext
        simp [hm]
      rw [ec, es]; exact s.step_same m j hj1 hj2
    · have hlast : k.val + 1 = d := by omega
      have ei : zeroPivotInc s hd1 k = s.incDir ⟨0, hd1⟩ :=
        zeroPivotInc_last s hd1 k (by omega)
      rw [ei] at hj1
      have ec : zeroPivotVerts s hd1 hfeas k.castSucc = s.verts (Fin.last d) := by
        rw [zeroPivotVerts_castSucc]; apply congrArg; apply Fin.ext
        simp [Fin.val_last]; omega
      have es : zeroPivotVerts s hd1 hfeas k.succ = zeroPivotTop s hd1 hfeas :=
        zeroPivotVerts_succ_last s hd1 hfeas k hlast
      rw [ec, es]; exact zeroPivotTop_coords_other s hd1 hfeas j hj1 hj2
  inc_injective := by
    intro a b hab
    have ha0 := a.isLt
    have hb0 := b.isLt
    by_cases ha : a.val + 1 < d <;> by_cases hb : b.val + 1 < d
    · rw [zeroPivotInc_of_lt s hd1 a ha, zeroPivotInc_of_lt s hd1 b hb] at hab
      have h : a.val + 1 = b.val + 1 := congrArg Fin.val (s.inc_injective hab)
      exact Fin.ext (by omega)
    · rw [zeroPivotInc_of_lt s hd1 a ha, zeroPivotInc_last s hd1 b hb] at hab
      have h : a.val + 1 = 0 := congrArg Fin.val (s.inc_injective hab)
      omega
    · rw [zeroPivotInc_last s hd1 a ha, zeroPivotInc_of_lt s hd1 b hb] at hab
      have h : (0 : ℕ) = b.val + 1 := congrArg Fin.val (s.inc_injective hab)
      omega
    · exact Fin.ext (by omega)

@[simp] theorem zeroPivotCell_miss (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (zeroPivotCell s hd1 hfeas).miss = s.miss := rfl

/-- The partner cell reuses `s`'s upper chain: its vertex `k` (`k < d`) is
`s.verts (k+1)`.  So dropping its own last vertex recovers exactly the facet
`{verts 1, …, verts d}` = facet `0` of `s` — the shared cross-chain facet. -/
theorem zeroPivotCell_verts_of_lt (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss)
    (k : Fin (d + 1)) (h : k.val < d) :
    (zeroPivotCell s hd1 hfeas).verts k = s.verts ⟨k.val + 1, by omega⟩ :=
  zeroPivotVerts_of_lt s hd1 hfeas k h

/-- The partner cell's last vertex is the new top vertex `zeroPivotTop`. -/
theorem zeroPivotCell_verts_last (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (zeroPivotCell s hd1 hfeas).verts (Fin.last d) = zeroPivotTop s hd1 hfeas :=
  zeroPivotVerts_last s hd1 hfeas

/-- **The facet-`0` partner cell is distinct from `s`.**  Its last vertex is
`zeroPivotTop`, which lies on no vertex of `s`'s chain
(`zeroPivotTop_not_mem_chain`); equal cells would force equal vertex maps and
hence `zeroPivotTop = s.verts (last)`, a contradiction.  Together with
`zeroPivotCell_verts_of_lt` this exhibits `zeroPivotCell` as a genuine *second*
cell filling the shared facet — the cross-chain partner required at facet `0`. -/
theorem zeroPivotCell_ne (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    zeroPivotCell s hd1 hfeas ≠ s := by
  intro h
  have hv := congrArg (fun t => t.verts (Fin.last d)) h
  simp only [zeroPivotCell_verts_last] at hv
  exact zeroPivotTop_not_mem_chain s hd1 hfeas (Fin.last d) hv

/-- **The shared cross-chain facet.**  The top facet (`Fin.last d`) of the
partner cell `zeroPivotCell` equals facet `0` of `s`.  Dropping the partner's
last vertex (`zeroPivotTop`) leaves its lower `d` vertices, which are exactly
`s`'s upper chain `verts 1, …, verts d` (`zeroPivotCell_verts_of_lt`); that set
is precisely facet `0` of `s`.  This is the concrete facet-level gluing datum at
facet `0` that all prior sessions flagged as "must be constructed": the two
*distinct* cells `s` and `zeroPivotCell` (`zeroPivotCell_ne`) meet along one
common facet — `s` across its facet `0` and `zeroPivotCell` across its facet
`Fin.last d` — the boundary `gridNeighbor` leaves unpaired
(`gridNeighbor_zero_none_not_boundary_face`). -/
theorem zeroPivotCell_gridFacet_last (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    gridFacet (zeroPivotCell s hd1 hfeas) (Fin.last d) = gridFacet s 0 := by
  ext v
  rw [mem_gridFacet_iff, mem_gridFacet_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjd : j.val < d := by
      have := j.isLt
      rcases Nat.lt_or_ge j.val d with h | h
      · exact h
      · exact absurd (Fin.ext (by simp [Fin.val_last]; omega)) hj
    refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
    · simp only [ne_eq, Fin.ext_iff, Fin.val_zero]; omega
    · show gridVertices s ⟨j.val + 1, _⟩ = gridVertices (zeroPivotCell s hd1 hfeas) j
      unfold gridVertices
      rw [zeroPivotCell_verts_of_lt s hd1 hfeas j hjd]
  · rintro ⟨i, hi, rfl⟩
    have hile : i.val ≤ d := by have := i.isLt; omega
    have hi1 : 1 ≤ i.val :=
      Nat.pos_of_ne_zero (fun h => hi (Fin.ext (by simp [h])))
    have hlt : i.val - 1 < d + 1 := by omega
    have hval : (⟨i.val - 1, hlt⟩ : Fin (d + 1)).val = i.val - 1 := rfl
    refine ⟨⟨i.val - 1, hlt⟩, ?_, ?_⟩
    · simp only [ne_eq, Fin.ext_iff, Fin.val_last]; omega
    · have hstep : (zeroPivotCell s hd1 hfeas).verts ⟨i.val - 1, hlt⟩ = s.verts i := by
        rw [zeroPivotCell_verts_of_lt s hd1 hfeas ⟨i.val - 1, hlt⟩ (by rw [hval]; omega)]
        congr 1
        apply Fin.ext
        show (⟨i.val - 1, hlt⟩ : Fin (d + 1)).val + 1 = i.val
        rw [hval]
        omega
      show gridVertices (zeroPivotCell s hd1 hfeas) ⟨i.val - 1, hlt⟩ = gridVertices s i
      unfold gridVertices
      rw [hstep]

/-- **Facet-`0` cross-chain gluing witness.**  Packages
`zeroPivotCell_gridFacet_last` with `zeroPivotCell_ne`: in the feasible regime the
partner cell `zeroPivotCell` is a cell *distinct* from `s` that shares `s`'s facet
`0` (as its own facet `Fin.last d`).  This is exactly the adjacency datum a total
gluing map must record at the facet-`0` boundary that the within-chain
`gridNeighbor` leaves as `none`. -/
theorem zeroPivotCell_shares_facet_zero (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    zeroPivotCell s hd1 hfeas ≠ s ∧
      gridFacet (zeroPivotCell s hd1 hfeas) (Fin.last d) = gridFacet s 0 :=
  ⟨zeroPivotCell_ne s hd1 hfeas, zeroPivotCell_gridFacet_last s hd1 hfeas⟩

/-- **`s`'s facet-`0` apex is absent from the partner cell.**  The vertex
`gridVertices s 0` deleted from `s` to form the shared facet does not reappear
anywhere among the facet-`0` partner's Kuhn vertices.  The partner's chain is
`s.verts 1, …, verts d, zeroPivotTop`: chain injectivity rules out the reused
lower vertices `s.verts (j+1)` (they cannot equal `s.verts 0`), and
`zeroPivotTop_not_mem_chain` rules out the new apex.  So `s`'s apex lies strictly
on `s`'s side of the gluing. -/
theorem gridVertices_zero_not_mem_zeroPivotCell_image (s : GridSimplex d N)
    (hd1 : 0 < d) (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    gridVertices s 0
      ∉ Finset.univ.image (gridVertices (zeroPivotCell s hd1 hfeas)) := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨j, hj⟩
  -- `hj : gridVertices (zeroPivotCell ..) j = gridVertices s 0`
  have hj' : (zeroPivotCell s hd1 hfeas).verts j = s.verts 0 := toVertex_injective hj
  by_cases hlt : j.val < d
  · rw [zeroPivotCell_verts_of_lt s hd1 hfeas j hlt] at hj'
    have heq := s.verts_injective hj'
    have : j.val + 1 = 0 := congrArg Fin.val heq
    omega
  · have hjlast : j = Fin.last d :=
      Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)
    rw [hjlast, zeroPivotCell_verts_last] at hj'
    exact zeroPivotTop_not_mem_chain s hd1 hfeas 0 hj'

/-- **The partner's apex is genuinely new.**  The partner cell's top vertex
`gridVertices (zeroPivotCell) (Fin.last d)` (the Kuhn image of `zeroPivotTop`)
appears nowhere in `s`'s vertex set — `zeroPivotTop_not_mem_chain` shows it
coincides with no vertex of `s`'s chain.  So the partner's apex lies strictly on
the partner's side of the gluing. -/
theorem zeroPivotCell_apex_not_mem_s_image (s : GridSimplex d N)
    (hd1 : 0 < d) (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    gridVertices (zeroPivotCell s hd1 hfeas) (Fin.last d)
      ∉ Finset.univ.image (gridVertices s) := by
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rintro ⟨i, hi⟩
  -- `hi : gridVertices s i = gridVertices (zeroPivotCell ..) (Fin.last d)`
  have hi' : s.verts i = (zeroPivotCell s hd1 hfeas).verts (Fin.last d) :=
    toVertex_injective hi
  rw [zeroPivotCell_verts_last] at hi'
  exact zeroPivotTop_not_mem_chain s hd1 hfeas i hi'.symm

/-- **The cell and its facet-`0` partner meet in exactly the shared facet.**
`s` and its cross-chain partner `zeroPivotCell` share precisely the facet
`gridFacet s 0` (equivalently the partner's top facet `Fin.last d`,
`zeroPivotCell_gridFacet_last`) and nothing more: their full Kuhn vertex sets
intersect in exactly that facet.  Each cell contributes one apex *off* the shared
facet — `gridVertices s 0` for `s` and the image of `zeroPivotTop` for the
partner (`gridVertices_zero_not_mem_zeroPivotCell_image`,
`zeroPivotCell_apex_not_mem_s_image`) — so the two distinct cells
(`zeroPivotCell_ne`) glue precisely along the common facet.  This is the defining
local condition of a simplicial pseudomanifold — two cells meet along a common
facet — now established for the facet-`0` gluing site that the within-chain
`gridNeighbor` leaves unpaired (`gridNeighbor_zero_none_not_boundary_face`). -/
theorem zeroPivotCell_meet_eq_gridFacet_zero (s : GridSimplex d N)
    (hd1 : 0 < d) (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (Finset.univ.image (gridVertices s))
        ∩ (Finset.univ.image (gridVertices (zeroPivotCell s hd1 hfeas)))
      = gridFacet s 0 := by
  apply Finset.Subset.antisymm
  · -- intersection ⊆ facet `0`
    intro v hv
    rw [Finset.mem_inter] at hv
    obtain ⟨hvs, hvp⟩ := hv
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hvs
    obtain ⟨i, hi⟩ := hvs
    rw [mem_gridFacet_iff]
    refine ⟨i, ?_, hi⟩
    rintro rfl
    -- then `v = gridVertices s 0`, but `v` also lies in the partner's image
    rw [← hi] at hvp
    exact gridVertices_zero_not_mem_zeroPivotCell_image s hd1 hfeas hvp
  · -- facet `0` ⊆ intersection
    intro v hv
    rw [Finset.mem_inter]
    have hvs : v ∈ Finset.univ.image (gridVertices s) := by
      rw [mem_gridFacet_iff] at hv
      obtain ⟨j, _, hj⟩ := hv
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
    refine ⟨hvs, ?_⟩
    -- `gridFacet s 0 = gridFacet (zeroPivotCell) (Fin.last d) ⊆ partner image`
    rw [(zeroPivotCell_gridFacet_last s hd1 hfeas).symm, mem_gridFacet_iff] at hv
    obtain ⟨j, _, hj⟩ := hv
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩

-- ============================================================
-- SECTION: Miss-coordinate descent of the facet-`0` pivot chain
-- ============================================================
-- The facet-`0` partner reuses `s`'s upper chain, so its base vertex
-- is `s.verts 1` — one step down the chain in the shared `miss`
-- direction (`miss_coord_at`).  Hence the partner's base `miss`
-- coordinate is exactly `base_miss − 1`.  Iterating the pivot walks
-- `base_miss` strictly downward; since every cell has `base_miss ≥ d`
-- (`base_miss_ge_d`) and is feasible iff `base_miss ≥ d + 1`
-- (`zeroPivot_feasible_iff`), the descent halts precisely at the
-- extremal cell `base_miss = d` — the one whose top vertex already
-- lies on the geometric `miss`-face, where the pivot must cross to a
-- different `miss` fibre.  This exhibits the same-`miss` facet-`0`
-- pivot chain as a finite monotone descent terminating at the
-- boundary door, the discrete path structure underlying the Phase-2
-- door-parity induction.  All 0-sorry, 0-axiom.

/-- **Miss-coordinate descent of the facet-`0` pivot.**  The partner cell's base
vertex sits one step lower in the shared `miss` direction: its `miss` coordinate is
exactly `base_miss − 1`.  (The partner's base is `s.verts 1` — `zeroPivotVerts_of_lt`
— and the `miss` coordinate falls by one at each chain step — `miss_coord_at`.) -/
theorem zeroPivotCell_base_miss (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    ((zeroPivotCell s hd1 hfeas).verts 0).coords (zeroPivotCell s hd1 hfeas).miss
      = (s.verts 0).coords s.miss - 1 := by
  rw [zeroPivotCell_miss,
      show (zeroPivotCell s hd1 hfeas).verts 0 = zeroPivotVerts s hd1 hfeas 0 from rfl,
      zeroPivotVerts_of_lt s hd1 hfeas 0 hd1, s.miss_coord_at]
  simp

/-- The facet-`0` partner's base `miss` coordinate is strictly below `s`'s: the
pivot chain descends. -/
theorem zeroPivotCell_base_miss_lt (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    ((zeroPivotCell s hd1 hfeas).verts 0).coords (zeroPivotCell s hd1 hfeas).miss
      < (s.verts 0).coords s.miss := by
  rw [zeroPivotCell_base_miss]
  have hge := s.base_miss_ge_d
  omega

/-- **The facet-`0` pivot chain terminates exactly at the extremal cell.**  A cell
is *infeasible* for the same-`miss` facet-`0` pivot iff its base `miss` coordinate is
the minimal value `d` (`base_miss_ge_d` gives `≥ d`; `zeroPivot_feasible_iff` gives
feasibility `⟺ ≥ d + 1`).  That extremal cell is the one whose top vertex already
sits on the geometric `miss`-face, where the pivot must cross to a new `miss` fibre. -/
theorem zeroPivot_infeasible_iff_base_miss_eq_d (s : GridSimplex d N) :
    ¬ (1 ≤ (s.verts (Fin.last d)).coords s.miss)
      ↔ (s.verts 0).coords s.miss = d := by
  rw [zeroPivot_feasible_iff]
  have hge := s.base_miss_ge_d
  omega

/-- **One step of the descent, feasibility form.**  The facet-`0` partner is again
feasible for its *own* same-`miss` facet-`0` pivot exactly when `s`'s base `miss`
coordinate is at least `d + 2`.  Combined with `zeroPivotCell_base_miss` and
`zeroPivot_infeasible_iff_base_miss_eq_d`, this shows each pivot lowers `base_miss`
by one until it reaches `d`, at which point the same-`miss` pivot stops. -/
theorem zeroPivotCell_feasible_iff_base_miss_ge (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    1 ≤ ((zeroPivotCell s hd1 hfeas).verts (Fin.last d)).coords
          (zeroPivotCell s hd1 hfeas).miss
      ↔ d + 2 ≤ (s.verts 0).coords s.miss := by
  rw [zeroPivot_feasible_iff, zeroPivotCell_base_miss]
  have hge := s.base_miss_ge_d
  omega

/-- **Exact top-`miss` height of the facet-`0` partner.**  Sharpens the iff-form
`zeroPivotCell_feasible_iff_base_miss_ge` to an exact value: the partner cell's
top vertex sits exactly `d + 1` below `s`'s base vertex in the shared `miss`
direction.  Its top vertex is `zeroPivotTop`, one below the top of `s`'s chain
(`zeroPivotTop_coords_miss`), and that chain-top is `base_miss − d`
(`last_coord_miss`); so the new apex is pinned to a definite height.  Together
with `zeroPivotCell_base_miss` (partner base = `base_miss − 1`) this makes the
`base_miss` descent fully quantitative rather than merely monotone: the whole
partner cell is a `miss`-shifted copy of `s`'s upper chain capped one step lower. -/
theorem zeroPivotCell_top_miss (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    ((zeroPivotCell s hd1 hfeas).verts (Fin.last d)).coords
        (zeroPivotCell s hd1 hfeas).miss
      = (s.verts 0).coords s.miss - (d + 1) := by
  rw [zeroPivotCell_miss, zeroPivotCell_verts_last, zeroPivotTop_coords_miss,
      s.last_coord_miss]
  omega

/-- **The facet-`0` pivot chain reaches the boundary door in exactly one more
step from a `base_miss = d + 1` cell.**  The partner cell `zeroPivotCell s` is
itself the *extremal* cell of the descent — its own same-`miss` facet-`0` pivot is
infeasible (top vertex already on the geometric `miss`-face) — exactly when `s`'s
base `miss` coordinate is `d + 1`, one above the floor `d`.  Combined with
`zeroPivotCell_base_miss` (each pivot lowers `base_miss` by one) and
`base_miss_ge_d` (floor `d`), this pins the descent length: from a cell with base
`miss = m` the same-`miss` facet-`0` pivot fires exactly `m − d` times before
halting at the extremal cell whose top vertex sits on the `miss`-face — the
terminal door where the cross-`miss` partner must attach. -/
theorem zeroPivotCell_extremal_iff_base_miss_eq (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    ¬ (1 ≤ ((zeroPivotCell s hd1 hfeas).verts (Fin.last d)).coords
              (zeroPivotCell s hd1 hfeas).miss)
      ↔ (s.verts 0).coords s.miss = d + 1 := by
  rw [zeroPivotCell_top_miss]
  have hfe := (zeroPivot_feasible_iff s).mp hfeas
  omega

/-- **Reciprocity base identity: the partner recovers `s`'s deleted apex by one
downward step.**  The facet-`0` pivot builds the partner `t = zeroPivotCell s`
*upward* — it deletes `s`'s base vertex `s.verts 0` and adds a new apex
(`zeroPivotTop`) above `s`'s chain.  Dually, `s` is exactly the cell obtained from
`t` by extending its top facet `{verts 1, …, verts d}` (= `gridFacet t (Fin.last d)`
= `gridFacet s 0`, by `zeroPivotCell_gridFacet_last`) *downward*: `s`'s apex
`s.verts 0` is `t`'s base vertex `t.verts 0` (= `s.verts 1`, by
`zeroPivotCell_verts_of_lt`) moved one lattice step *back* along the omitted
direction `incDir 0` — decrement the `incDir 0` coordinate, increment the `miss`
coordinate (the exact inverse of `s`'s step-`0` chain move: `step_inc`/`step_dec`/
`step_same` at `k = 0`).  This single formula pins the reciprocal downward vertex
completely and is the coordinate core of the top-facet (`Fin.last d`) pivot that
must invert the facet-`0` pivot for `adj` to be a partial involution across the
boundary facets. -/
theorem zeroPivotCell_base_recover (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) (j : Fin (d + 1)) :
    (s.verts 0).coords j
      = if j = s.incDir ⟨0, hd1⟩ then
          ((zeroPivotCell s hd1 hfeas).verts 0).coords j - 1
        else if j = s.miss then
          ((zeroPivotCell s hd1 hfeas).verts 0).coords j + 1
        else ((zeroPivotCell s hd1 hfeas).verts 0).coords j := by
  have hcast : (⟨0, hd1⟩ : Fin d).castSucc = (0 : Fin (d + 1)) := by
    apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
  have ht : (zeroPivotCell s hd1 hfeas).verts 0 = s.verts (⟨0, hd1⟩ : Fin d).succ := by
    rw [zeroPivotCell_verts_of_lt s hd1 hfeas 0 hd1]
    congr 1
  rw [ht]
  by_cases hP : j = s.incDir ⟨0, hd1⟩
  · subst hP
    rw [if_pos rfl]
    have hstep := s.step_inc ⟨0, hd1⟩
    rw [hcast] at hstep
    omega
  · rw [if_neg hP]
    by_cases hQ : j = s.miss
    · subst hQ
      rw [if_pos rfl]
      have hstep := s.step_dec ⟨0, hd1⟩
      rw [hcast] at hstep
      omega
    · rw [if_neg hQ]
      have hstep := s.step_same ⟨0, hd1⟩ j hP hQ
      rw [hcast] at hstep
      omega

/-- **Downward-step coordinate of the recovered apex (`incDir 0` case).**  The
`incDir 0` coordinate of `s`'s deleted apex is one *below* the partner's base
vertex — the reciprocal of the pivot's single upward increment at step `0`.
Specialization of `zeroPivotCell_base_recover` at `j = incDir 0`. -/
theorem zeroPivotCell_base_incDir0 (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (s.verts 0).coords (s.incDir ⟨0, hd1⟩)
      = ((zeroPivotCell s hd1 hfeas).verts 0).coords (s.incDir ⟨0, hd1⟩) - 1 := by
  have h := zeroPivotCell_base_recover s hd1 hfeas (s.incDir ⟨0, hd1⟩)
  rwa [if_pos rfl] at h

/-- **Downward-step coordinate of the recovered apex (`miss` case).**  The `miss`
coordinate of `s`'s deleted apex is one *above* the partner's base vertex: moving
down along the omitted direction restores the unit of `miss` the pivot spent going
up.  Specialization of `zeroPivotCell_base_recover` at `j = miss`. -/
theorem zeroPivotCell_base_miss_recover (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    (s.verts 0).coords s.miss
      = ((zeroPivotCell s hd1 hfeas).verts 0).coords s.miss + 1 := by
  have h := zeroPivotCell_base_recover s hd1 hfeas s.miss
  rw [if_neg (fun hh => s.miss_ne_inc ⟨0, hd1⟩ hh.symm), if_pos rfl] at h
  exact h

-- ============================================================
-- SECTION: The top-facet (`Fin.last d`) pivot — reciprocal base vertex
-- ============================================================
-- Dual to `zeroPivotTop`/`zeroPivotCell`.  Where the facet-`0` pivot
-- deletes `u`'s base vertex and *appends* a new apex `zeroPivotTop`
-- above the chain (reversing the FIRST increment `incDir 0`), the
-- facet-`Fin.last d` pivot deletes `u`'s apex and *prepends* a new
-- base vertex below `u.verts 0`, reversing the LAST increment
-- `incDir (d-1)`: it decrements that direction and increments `miss`.
-- This is exactly the downward move `zeroPivotCell_base_recover`
-- pins at the coordinate level.  The section builds the new base
-- vertex as a bona-fide `BaryPoint` and proves the vertex-level
-- reciprocity `topPivotBottom (zeroPivotCell s) = s.verts 0` — the
-- top-facet pivot on the facet-`0` partner recovers `s`'s deleted
-- apex, the identity `adj` needs to be a partial involution across
-- the boundary facets.  All 0-sorry, 0-axiom; builds only on the
-- `GridSimplex` chain primitives and the `zeroPivotCell_base_recover`
-- lemma family above.

/-- The direction that increases at `u`'s final chain step `d-1` — the
increment the top-facet (`Fin.last d`) pivot reverses. -/
def lastIncDir (u : GridSimplex d N) (hd1 : 0 < d) : Fin (d + 1) :=
  u.incDir ⟨d - 1, by omega⟩

/-- **Reciprocal base vertex of the top-facet (`Fin.last d`) pivot.**  Dual to
`zeroPivotTop`: the facet-`Fin.last d` pivot deletes `u`'s apex and prepends a
new base *below* `u.verts 0`, obtained by reversing `u`'s final increment —
decrement the last-increment direction `lastIncDir`, increment the `miss`
direction (so the barycentric sum is preserved).  Feasible when that coordinate
of `u`'s base is at least `1`. -/
def topPivotBottom (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    BaryPoint d N where
  coords := fun j =>
    if j = lastIncDir u hd1 then (u.verts 0).coords j - 1
    else if j = u.miss then (u.verts 0).coords j + 1
    else (u.verts 0).coords j
  sum_eq := by
    set p := lastIncDir u hd1 with hp
    set q := u.miss with hq
    set V := u.verts 0 with hV
    have hpq : p ≠ q := u.miss_ne_inc ⟨d - 1, by omega⟩
    have key : ∀ j : Fin (d + 1),
        (if j = p then V.coords j - 1
          else if j = q then V.coords j + 1 else V.coords j)
        + (if j = p then 1 else 0)
        = V.coords j + (if j = q then 1 else 0) := by
      intro j
      by_cases h1 : j = p
      · subst h1
        rw [if_pos rfl, if_pos rfl, if_neg hpq]
        have : 1 ≤ V.coords p := hfeas
        omega
      · by_cases h2 : j = q
        · subst h2
          rw [if_neg h1, if_pos rfl, if_neg h1, if_pos rfl]
        · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
    have hone_p : (∑ j : Fin (d + 1), (if j = p then (1 : ℕ) else 0)) = 1 := by simp
    have hone_q : (∑ j : Fin (d + 1), (if j = q then (1 : ℕ) else 0)) = 1 := by simp
    have hsum :
        (∑ j : Fin (d + 1),
            (if j = p then V.coords j - 1
              else if j = q then V.coords j + 1 else V.coords j)) + 1
          = (∑ j : Fin (d + 1), V.coords j) + 1 := by
      calc
        (∑ j : Fin (d + 1),
            (if j = p then V.coords j - 1
              else if j = q then V.coords j + 1 else V.coords j)) + 1
            = (∑ j : Fin (d + 1),
                (if j = p then V.coords j - 1
                  else if j = q then V.coords j + 1 else V.coords j))
              + (∑ j : Fin (d + 1), (if j = p then (1 : ℕ) else 0)) := by rw [hone_p]
          _ = ∑ j : Fin (d + 1),
                ((if j = p then V.coords j - 1
                    else if j = q then V.coords j + 1 else V.coords j)
                  + (if j = p then (1 : ℕ) else 0)) := by rw [Finset.sum_add_distrib]
          _ = ∑ j : Fin (d + 1),
                (V.coords j + (if j = q then (1 : ℕ) else 0)) :=
                Finset.sum_congr rfl (fun j _ => key j)
          _ = (∑ j : Fin (d + 1), V.coords j)
                + (∑ j : Fin (d + 1), (if j = q then (1 : ℕ) else 0)) := by
                rw [Finset.sum_add_distrib]
          _ = (∑ j : Fin (d + 1), V.coords j) + 1 := by rw [hone_q]
    rw [V.sum_eq] at hsum
    omega

/-- Coordinate of `topPivotBottom` at the reversed direction `lastIncDir`. -/
theorem topPivotBottom_coords_lastIncDir (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    (topPivotBottom u hd1 hfeas).coords (lastIncDir u hd1)
      = (u.verts 0).coords (lastIncDir u hd1) - 1 := by
  show (if lastIncDir u hd1 = lastIncDir u hd1 then _ else _) = _
  rw [if_pos rfl]

/-- Coordinate of `topPivotBottom` at the `miss` direction. -/
theorem topPivotBottom_coords_miss (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    (topPivotBottom u hd1 hfeas).coords u.miss
      = (u.verts 0).coords u.miss + 1 := by
  have hpq : u.miss ≠ lastIncDir u hd1 :=
    fun h => u.miss_ne_inc ⟨d - 1, by omega⟩ h.symm
  show (if u.miss = lastIncDir u hd1 then _ else if u.miss = u.miss then _ else _) = _
  rw [if_neg hpq, if_pos rfl]

/-- Coordinate of `topPivotBottom` at any other direction: unchanged from the
base vertex `u.verts 0`. -/
theorem topPivotBottom_coords_other (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1))
    (j : Fin (d + 1)) (hjp : j ≠ lastIncDir u hd1) (hjq : j ≠ u.miss) :
    (topPivotBottom u hd1 hfeas).coords j = (u.verts 0).coords j := by
  show (if j = lastIncDir u hd1 then _ else if j = u.miss then _ else _) = _
  rw [if_neg hjp, if_neg hjq]

/-- The facet-`0` partner's last increment direction is `s`'s omitted
direction `incDir 0` (deferred to the final step by the cyclic rotation
`zeroPivotInc`). -/
theorem zeroPivotCell_lastIncDir (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    lastIncDir (zeroPivotCell s hd1 hfeas) hd1 = s.incDir ⟨0, hd1⟩ := by
  have hk : d - 1 < d := by omega
  have hnl : ¬ (⟨d - 1, hk⟩ : Fin d).val + 1 < d := by
    show ¬ (d - 1) + 1 < d
    omega
  show zeroPivotInc s hd1 ⟨d - 1, hk⟩ = s.incDir ⟨0, hd1⟩
  exact zeroPivotInc_last s hd1 ⟨d - 1, hk⟩ hnl

/-- The top-facet pivot is always feasible on the facet-`0` partner: its base
vertex `t.verts 0 = s.verts 1` has `incDir 0` coordinate `base + 1 ≥ 1`
(`step_inc` at step `0`). -/
theorem zeroPivotCell_lastIncDir_feasible (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    1 ≤ ((zeroPivotCell s hd1 hfeas).verts 0).coords
          (lastIncDir (zeroPivotCell s hd1 hfeas) hd1) := by
  have ht : (zeroPivotCell s hd1 hfeas).verts 0 = s.verts (⟨0, hd1⟩ : Fin d).succ := by
    rw [zeroPivotCell_verts_of_lt s hd1 hfeas 0 hd1]; congr 1
  rw [zeroPivotCell_lastIncDir, ht]
  have hstep := s.step_inc ⟨0, hd1⟩
  have hcs : (⟨0, hd1⟩ : Fin d).castSucc = (0 : Fin (d + 1)) := by
    apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.castLE]
  rw [hcs] at hstep
  rw [hstep]; omega

/-- **Vertex-level reciprocity: the top-facet pivot recovers `s`'s deleted
apex.**  The facet-`0` partner `t = zeroPivotCell s` reuses `s`'s upper chain
and appends a new apex, deleting `s`'s base vertex `s.verts 0`.  Applying the
dual top-facet (`Fin.last d`) pivot to `t` — deleting `t`'s apex and prepending
a new base by reversing `t`'s last increment (`= s.incDir 0`,
`zeroPivotCell_lastIncDir`) — reconstructs exactly `s.verts 0`: decrement
`incDir 0`, increment `miss` from `t.verts 0 = s.verts 1`, precisely the formula
of `zeroPivotCell_base_recover`.  This is the reciprocal (downward) vertex the
partial involution `adj` needs at the boundary facets: the two pivots invert one
another at the shared cross-chain facet `gridFacet s 0 = gridFacet t (Fin.last d)`
(`zeroPivotCell_gridFacet_last`). -/
theorem topPivotBottom_zeroPivotCell (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    topPivotBottom (zeroPivotCell s hd1 hfeas) hd1
        (zeroPivotCell_lastIncDir_feasible s hd1 hfeas) = s.verts 0 := by
  have hlast : lastIncDir (zeroPivotCell s hd1 hfeas) hd1 = s.incDir ⟨0, hd1⟩ :=
    zeroPivotCell_lastIncDir s hd1 hfeas
  have hmiss : (zeroPivotCell s hd1 hfeas).miss = s.miss :=
    zeroPivotCell_miss s hd1 hfeas
  ext j
  by_cases hP : j = lastIncDir (zeroPivotCell s hd1 hfeas) hd1
  · subst hP
    rw [topPivotBottom_coords_lastIncDir, hlast]
    exact (zeroPivotCell_base_incDir0 s hd1 hfeas).symm
  · by_cases hQ : j = (zeroPivotCell s hd1 hfeas).miss
    · subst hQ
      rw [topPivotBottom_coords_miss, hmiss]
      exact (zeroPivotCell_base_miss_recover s hd1 hfeas).symm
    · have hjp : j ≠ s.incDir ⟨0, hd1⟩ := by rw [← hlast]; exact hP
      have hjq : j ≠ s.miss := by rw [← hmiss]; exact hQ
      rw [topPivotBottom_coords_other (zeroPivotCell s hd1 hfeas) hd1
        (zeroPivotCell_lastIncDir_feasible s hd1 hfeas) j hP hQ]
      have h := zeroPivotCell_base_recover s hd1 hfeas j
      rw [if_neg hjp, if_neg hjq] at h
      exact h.symm

/-- **The dual base vertex is genuinely new.**  `topPivotBottom u`, the reciprocal
base vertex the top-facet (`Fin.last d`) pivot prepends below `u`'s chain,
coincides with no vertex of `u`'s own chain: its `lastIncDir` coordinate is
`base − 1`, strictly below the chain minimum.  That coordinate — direction
`incDir (d-1)` — never dips below its base value along the chain
(`coord_incDir_at`: it is `base` until step `d-1` and `base + 1` after), while the
dual base sits one unit lower still.  This is the mirror of
`zeroPivotTop_not_mem_chain` for the facet-`0` pivot: it shows the top-facet pivot
genuinely leaves the original cell, so the dual partner cell is a *distinct*
filling of the shared facet — the distinctness datum the full `topPivotCell`
assembly and the boundary partial involution `adj` require. -/
theorem topPivotBottom_not_mem_chain (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) (m : Fin (d + 1)) :
    topPivotBottom u hd1 hfeas ≠ u.verts m := by
  intro h
  have hk : d - 1 < d := by omega
  have hval : lastIncDir u hd1 = u.incDir ⟨d - 1, hk⟩ := rfl
  have hcoord : (topPivotBottom u hd1 hfeas).coords (lastIncDir u hd1)
      = (u.verts m).coords (lastIncDir u hd1) := by rw [h]
  rw [topPivotBottom_coords_lastIncDir] at hcoord
  have hmono := u.coord_incDir_at ⟨d - 1, hk⟩ m
  rw [← hval] at hmono
  have hge : (u.verts 0).coords (lastIncDir u hd1)
      ≤ (u.verts m).coords (lastIncDir u hd1) := by rw [hmono]; split <;> omega
  omega

-- ============================================================
-- The dual top-facet pivot cell `topPivotCell` and cell-level reciprocity
--
-- This section assembles the full `GridSimplex` produced by the top-facet
-- (`Fin.last d`) pivot: delete `u`'s apex `verts d`, prepend the reciprocal
-- base `topPivotBottom` (`= verts 0` shifted down by reversing the last
-- increment), and shift the surviving chain up one index.  It is the exact
-- dual of `zeroPivotCell` (which deletes the base and appends a new apex).
--
-- The capstone `topPivotCell_zeroPivotCell` lifts the vertex-level identity
-- `topPivotBottom_zeroPivotCell` (the new base recovers `s`'s deleted apex)
-- to the CELL level: the two pivots invert one another,
--   `topPivotCell (zeroPivotCell s) = s`,
-- which is precisely the partial-involution reciprocity the boundary `adj`
-- needs at the cross-chain facet `gridFacet s 0 = gridFacet (zeroPivotCell s)
-- (Fin.last d)`.  All 0-sorry, 0-axiom; builds only on the `GridSimplex`
-- chain primitives and the `zeroPivotCell`/`topPivotBottom` lemmas above.
-- ============================================================

/-- Vertices of the dual top-facet partner cell: the new base
`topPivotBottom` at index `0`, followed by `u`'s surviving chain
`verts 0, …, verts (d-1)` shifted up to indices `1, …, d`. -/
def topPivotVerts (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    Fin (d + 1) → BaryPoint d N :=
  fun k => if h : k.val = 0 then topPivotBottom u hd1 hfeas
    else u.verts ⟨k.val - 1, by have := k.isLt; omega⟩

/-- Increment directions of the dual cell: `u`'s directions cyclically rotated
so the reversed final increment `lastIncDir` fires on step `0`. -/
def topPivotInc (u : GridSimplex d N) (hd1 : 0 < d) :
    Fin d → Fin (d + 1) :=
  fun k => if h : k.val = 0 then lastIncDir u hd1
    else u.incDir ⟨k.val - 1, by have := k.isLt; omega⟩

theorem topPivotVerts_eq_bottom (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1))
    (k : Fin (d + 1)) (h : k.val = 0) :
    topPivotVerts u hd1 hfeas k = topPivotBottom u hd1 hfeas := by
  simp only [topPivotVerts, dif_pos h]

theorem topPivotVerts_of_pos (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1))
    (k : Fin (d + 1)) (h : k.val ≠ 0) :
    topPivotVerts u hd1 hfeas k = u.verts ⟨k.val - 1, by have := k.isLt; omega⟩ := by
  simp only [topPivotVerts, dif_neg h]

theorem topPivotInc_eq_lastIncDir (u : GridSimplex d N) (hd1 : 0 < d)
    (k : Fin d) (h : k.val = 0) :
    topPivotInc u hd1 k = lastIncDir u hd1 := by
  simp only [topPivotInc, dif_pos h]

theorem topPivotInc_of_pos (u : GridSimplex d N) (hd1 : 0 < d)
    (k : Fin d) (h : k.val ≠ 0) :
    topPivotInc u hd1 k = u.incDir ⟨k.val - 1, by have := k.isLt; omega⟩ := by
  simp only [topPivotInc, dif_neg h]

/-- Evaluation of the dual cell's vertices at `k.succ`: since `(k.succ).val =
k.val + 1 ≠ 0`, it drops back to `u`'s chain at `k.castSucc`. -/
theorem topPivotVerts_succ (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) (k : Fin d) :
    topPivotVerts u hd1 hfeas k.succ = u.verts k.castSucc := by
  rw [topPivotVerts_of_pos u hd1 hfeas k.succ (by simp [Fin.val_succ])]
  rfl

/-- Evaluation of the dual cell's vertices at `k.castSucc` for a positive step
(`k.val ≠ 0`): it is `u.verts (k-1)`. -/
theorem topPivotVerts_castSucc_of_pos (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) (k : Fin d)
    (h : k.val ≠ 0) :
    topPivotVerts u hd1 hfeas k.castSucc
      = u.verts ⟨k.val - 1, by have := k.isLt; omega⟩ := by
  rw [topPivotVerts_of_pos u hd1 hfeas k.castSucc (by simpa [Fin.coe_castSucc] using h)]
  rfl

/-- Evaluation of the dual cell's vertices at `k.castSucc` for the first step
(`k.val = 0`): it is the new base `topPivotBottom`. -/
theorem topPivotVerts_castSucc_zero (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) (k : Fin d)
    (h : k.val = 0) :
    topPivotVerts u hd1 hfeas k.castSucc = topPivotBottom u hd1 hfeas := by
  rw [topPivotVerts_eq_bottom u hd1 hfeas k.castSucc (by simpa [Fin.coe_castSucc] using h)]

/-- **The dual top-facet pivot cell.**  A bona-fide `GridSimplex` whose base
vertex is the reciprocal `topPivotBottom` and whose remaining `d` vertices are
`u`'s surviving chain `verts 0, …, verts (d-1)`; increments are `u`'s cyclic
rotation (reversed last increment `lastIncDir` first), same `miss`.  Defined in
the feasible regime `(verts 0)(lastIncDir) ≥ 1`. -/
def topPivotCell (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    GridSimplex d N where
  verts := topPivotVerts u hd1 hfeas
  incDir := topPivotInc u hd1
  miss := u.miss
  miss_ne_inc := by
    intro k
    by_cases hk0 : k.val = 0
    · rw [topPivotInc_eq_lastIncDir u hd1 k hk0]
      exact u.miss_ne_inc ⟨d - 1, by omega⟩
    · rw [topPivotInc_of_pos u hd1 k hk0]; exact u.miss_ne_inc _
  step_inc := by
    intro k
    by_cases hk0 : k.val = 0
    · rw [topPivotInc_eq_lastIncDir u hd1 k hk0, topPivotVerts_succ,
        topPivotVerts_castSucc_zero u hd1 hfeas k hk0]
      have hc : k.castSucc = (0 : Fin (d + 1)) := by
        apply Fin.ext; show k.val = 0; exact hk0
      rw [hc, topPivotBottom_coords_lastIncDir]
      omega
    · have hb : k.val - 1 < d := by have := k.isLt; omega
      have hks : k.castSucc = (⟨k.val - 1, hb⟩ : Fin d).succ := by
        apply Fin.ext; show k.val = k.val - 1 + 1; omega
      rw [topPivotInc_of_pos u hd1 k hk0, topPivotVerts_succ,
        topPivotVerts_castSucc_of_pos u hd1 hfeas k hk0, hks]
      exact u.step_inc ⟨k.val - 1, hb⟩
  step_dec := by
    intro k
    by_cases hk0 : k.val = 0
    · have hc : k.castSucc = (0 : Fin (d + 1)) := by
        apply Fin.ext; show k.val = 0; exact hk0
      rw [topPivotVerts_succ, topPivotVerts_castSucc_zero u hd1 hfeas k hk0, hc,
        topPivotBottom_coords_miss]
    · have hb : k.val - 1 < d := by have := k.isLt; omega
      have hks : k.castSucc = (⟨k.val - 1, hb⟩ : Fin d).succ := by
        apply Fin.ext; show k.val = k.val - 1 + 1; omega
      rw [topPivotVerts_succ, topPivotVerts_castSucc_of_pos u hd1 hfeas k hk0, hks]
      exact u.step_dec ⟨k.val - 1, hb⟩
  step_same := by
    intro k j hj1 hj2
    by_cases hk0 : k.val = 0
    · rw [topPivotInc_eq_lastIncDir u hd1 k hk0] at hj1
      have hc : k.castSucc = (0 : Fin (d + 1)) := by
        apply Fin.ext; show k.val = 0; exact hk0
      rw [topPivotVerts_succ, topPivotVerts_castSucc_zero u hd1 hfeas k hk0, hc,
        topPivotBottom_coords_other u hd1 hfeas j hj1 hj2]
    · have hb : k.val - 1 < d := by have := k.isLt; omega
      have hks : k.castSucc = (⟨k.val - 1, hb⟩ : Fin d).succ := by
        apply Fin.ext; show k.val = k.val - 1 + 1; omega
      rw [topPivotInc_of_pos u hd1 k hk0] at hj1
      rw [topPivotVerts_succ, topPivotVerts_castSucc_of_pos u hd1 hfeas k hk0, hks]
      exact u.step_same ⟨k.val - 1, hb⟩ j hj1 hj2
  inc_injective := by
    intro a b hab
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
    · exact Fin.ext (by omega)
    · exfalso
      rw [topPivotInc_eq_lastIncDir u hd1 a ha, topPivotInc_of_pos u hd1 b hb,
        lastIncDir] at hab
      have h := u.inc_injective hab
      have hval : (d - 1 : ℕ) = b.val - 1 := by simpa using congrArg Fin.val h
      have := b.isLt; omega
    · exfalso
      rw [topPivotInc_of_pos u hd1 a ha, topPivotInc_eq_lastIncDir u hd1 b hb,
        lastIncDir] at hab
      have h := u.inc_injective hab
      have hval : (a.val - 1 : ℕ) = d - 1 := by simpa using congrArg Fin.val h
      have := a.isLt; omega
    · rw [topPivotInc_of_pos u hd1 a ha, topPivotInc_of_pos u hd1 b hb] at hab
      have h := u.inc_injective hab
      have hval : (a.val - 1 : ℕ) = b.val - 1 := by simpa using congrArg Fin.val h
      exact Fin.ext (by omega)

@[simp] theorem topPivotCell_verts (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) (k : Fin (d + 1)) :
    (topPivotCell u hd1 hfeas).verts k = topPivotVerts u hd1 hfeas k := rfl

@[simp] theorem topPivotCell_incDir (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) (k : Fin d) :
    (topPivotCell u hd1 hfeas).incDir k = topPivotInc u hd1 k := rfl

@[simp] theorem topPivotCell_miss (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    (topPivotCell u hd1 hfeas).miss = u.miss := rfl

/-- **The dual pivot cell is distinct from `u`.**  Its base vertex is
`topPivotBottom`, which lies on no vertex of `u`'s chain
(`topPivotBottom_not_mem_chain`).  Equal cells would force equal vertex maps
and hence `topPivotBottom = u.verts 0`, a contradiction.  So `topPivotCell u`
is a genuine *second* cell — the reciprocal partner filling the top facet. -/
theorem topPivotCell_ne (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    topPivotCell u hd1 hfeas ≠ u := by
  intro h
  have hv := congrArg (fun t => t.verts 0) h
  simp only [topPivotCell_verts] at hv
  rw [topPivotVerts_eq_bottom u hd1 hfeas 0 rfl] at hv
  exact topPivotBottom_not_mem_chain u hd1 hfeas 0 hv

/-- **Cell-level reciprocity: the two pivots invert one another.**  Applying
the dual top-facet pivot `topPivotCell` to the facet-`0` cross-chain partner
`zeroPivotCell s` reconstructs `s` exactly.  Vertex `0` is recovered by
`topPivotBottom_zeroPivotCell` (the reciprocal base is `s`'s deleted apex
`s.verts 0`); each higher vertex `k ≥ 1` is `s.verts k` because the dual cell
re-shifts the partner's chain (`zeroPivotCell` uses `s.verts 1, …, verts d`,
`topPivotCell` prepends a new base and slides them back); `incDir` matches by
the two mutually-inverse cyclic rotations, and `miss` is preserved throughout.
This is the partial-involution reciprocity `adj` requires at the shared
cross-chain facet `gridFacet s 0 = gridFacet (zeroPivotCell s) (Fin.last d)`
(`zeroPivotCell_gridFacet_last`): the boundary facet `0` of `s` and the top
facet of its partner are glued by two cells that map to each other. -/
theorem topPivotCell_zeroPivotCell (s : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (s.verts (Fin.last d)).coords s.miss) :
    topPivotCell (zeroPivotCell s hd1 hfeas) hd1
        (zeroPivotCell_lastIncDir_feasible s hd1 hfeas) = s := by
  apply gridSimplex_ext
  · funext k
    by_cases hk0 : k.val = 0
    · have hk : k = (0 : Fin (d + 1)) := by apply Fin.ext; show k.val = 0; exact hk0
      rw [topPivotCell_verts, topPivotVerts_eq_bottom _ hd1 _ k hk0, hk]
      exact topPivotBottom_zeroPivotCell s hd1 hfeas
    · rw [topPivotCell_verts, topPivotVerts_of_pos _ hd1 _ k hk0]
      show (zeroPivotCell s hd1 hfeas).verts ⟨k.val - 1, by have := k.isLt; omega⟩
        = s.verts k
      rw [zeroPivotCell_verts_of_lt s hd1 hfeas ⟨k.val - 1, by have := k.isLt; omega⟩
        (by show k.val - 1 < d; have := k.isLt; omega)]
      congr 1; apply Fin.ext; show (k.val - 1) + 1 = k.val; omega
  · funext k
    by_cases hk0 : k.val = 0
    · rw [topPivotCell_incDir, topPivotInc_eq_lastIncDir _ hd1 k hk0,
        zeroPivotCell_lastIncDir s hd1 hfeas]
      congr 1; apply Fin.ext; show (0 : ℕ) = k.val; omega
    · rw [topPivotCell_incDir, topPivotInc_of_pos _ hd1 k hk0]
      show zeroPivotInc s hd1 ⟨k.val - 1, by have := k.isLt; omega⟩ = s.incDir k
      rw [zeroPivotInc_of_lt s hd1 ⟨k.val - 1, by have := k.isLt; omega⟩
        (by show k.val - 1 + 1 < d; have := k.isLt; omega)]
      congr 1; apply Fin.ext; show (k.val - 1) + 1 = k.val; omega
  · rw [topPivotCell_miss, zeroPivotCell_miss]

-- ============================================================
-- Reverse reciprocity: `zeroPivotCell (topPivotCell u) = u`
-- ============================================================
-- `topPivotCell_zeroPivotCell` proves ONE composition of the two
-- cross-facet pivots is the identity (`topPivotCell ∘ zeroPivotCell =
-- id`).  This section proves the OTHER composition
-- (`zeroPivotCell ∘ topPivotCell = id`), upgrading the partial-involution
-- reciprocity to a genuine two-sided involution: on the feasible regime the
-- facet-`0` cross-chain pivot and the dual top-facet pivot are mutually
-- inverse bijections.  This is exactly the well-definedness the boundary
-- `adj` needs — the gluing at a shared cross-chain facet is an involution,
-- so each of the two cells filling it maps to the other and back.
--
-- The feasibility bridge is automatic: `topPivotCell u`'s apex is `u.verts
-- (d-1)`, whose `miss` coordinate is `base_miss − (d−1) ≥ d − (d−1) = 1`
-- (`miss_coord_at` + `base_miss_ge_d`), so the facet-`0` pivot is always
-- applicable to it.  The crux is the dual apex-recovery
-- `zeroPivotTop (topPivotCell u) = u.verts (Fin.last d)` — the mirror of
-- `topPivotBottom_zeroPivotCell`: the new apex the facet-`0` pivot appends
-- above `topPivotCell u`'s chain reconstructs `u`'s deleted apex, coordinate
-- by coordinate via the last chain step `u.step_inc/step_dec/step_same` at
-- `⟨d-1⟩`.  All 0-sorry, 0-axiom.

/-- **Feasibility bridge.**  The facet-`0` cross-chain pivot is always
applicable to the dual cell `topPivotCell u`: its apex is `u.verts (d-1)`,
whose `miss` coordinate is `base_miss − (d−1) ≥ 1` (it descends by one at each
of the `d−1` steps and starts `≥ d`, `miss_coord_at` + `base_miss_ge_d`). -/
theorem topPivotCell_zeroFeasible (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    1 ≤ ((topPivotCell u hd1 hfeas).verts (Fin.last d)).coords
          (topPivotCell u hd1 hfeas).miss := by
  have hne : (Fin.last d).val ≠ 0 := by simp only [Fin.val_last]; omega
  rw [topPivotCell_verts, topPivotCell_miss,
    topPivotVerts_of_pos u hd1 hfeas (Fin.last d) hne, u.miss_coord_at]
  have hb := u.base_miss_ge_d
  simp only [Fin.val_last]
  omega

/-- **Dual apex recovery** (mirror of `topPivotBottom_zeroPivotCell`).  The new
apex that the facet-`0` pivot appends above `topPivotCell u`'s chain
reconstructs exactly `u`'s deleted apex `u.verts (Fin.last d)`.  Proved
coordinate-by-coordinate from the last chain step of `u` (`step_inc` at the
reversed `lastIncDir` direction, `step_dec` at `miss`, `step_same` elsewhere)
evaluated between `u.verts (d-1)` and `u.verts (Fin.last d)`. -/
theorem zeroPivotTop_topPivotCell (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    zeroPivotTop (topPivotCell u hd1 hfeas) hd1
        (topPivotCell_zeroFeasible u hd1 hfeas) = u.verts (Fin.last d) := by
  have hlt : d - 1 < d := by omega
  have hne : (Fin.last d).val ≠ 0 := by simp only [Fin.val_last]; omega
  have hsucc : (⟨d - 1, hlt⟩ : Fin d).succ = Fin.last d := by
    apply Fin.ext; show d - 1 + 1 = (Fin.last d).val; simp only [Fin.val_last]; omega
  have hinc : (topPivotCell u hd1 hfeas).incDir ⟨0, hd1⟩ = u.incDir ⟨d - 1, hlt⟩ :=
    topPivotInc_eq_lastIncDir u hd1 ⟨0, hd1⟩ rfl
  have hmiss : (topPivotCell u hd1 hfeas).miss = u.miss := topPivotCell_miss u hd1 hfeas
  have hapex : (topPivotCell u hd1 hfeas).verts (Fin.last d)
      = u.verts (⟨d - 1, hlt⟩ : Fin d).castSucc := by
    rw [topPivotCell_verts, topPivotVerts_of_pos u hd1 hfeas (Fin.last d) hne]
    congr 1
  ext j
  by_cases hP : j = (topPivotCell u hd1 hfeas).incDir ⟨0, hd1⟩
  · subst hP
    rw [zeroPivotTop_coords_incDir0, hapex, hinc]
    have hs := u.step_inc ⟨d - 1, hlt⟩
    rw [hsucc] at hs
    exact hs.symm
  · by_cases hQ : j = (topPivotCell u hd1 hfeas).miss
    · subst hQ
      rw [zeroPivotTop_coords_miss, hapex, hmiss]
      have hs := u.step_dec ⟨d - 1, hlt⟩
      rw [hsucc] at hs
      omega
    · rw [zeroPivotTop_coords_other _ _ _ j hP hQ, hapex]
      have hj1 : j ≠ u.incDir ⟨d - 1, hlt⟩ := by rw [← hinc]; exact hP
      have hj2 : j ≠ u.miss := by rw [← hmiss]; exact hQ
      have hs := u.step_same ⟨d - 1, hlt⟩ j hj1 hj2
      rw [hsucc] at hs
      exact hs.symm

/-- **Cell-level reverse reciprocity: the two pivots invert one another (other
direction).**  Applying the facet-`0` cross-chain pivot `zeroPivotCell` to the
dual top-facet partner `topPivotCell u` reconstructs `u` exactly.  Together with
`topPivotCell_zeroPivotCell` this establishes that, on the feasible regime,
`zeroPivotCell` and `topPivotCell` are mutually inverse bijections — a genuine
two-sided involution, the well-definedness the boundary `adj` requires.  Vertex
`Fin.last d` is recovered by `zeroPivotTop_topPivotCell`; each lower vertex
`k < d` is `u.verts k` because `topPivotCell` slid `u`'s chain up one index and
`zeroPivotCell` slides it back; `incDir` matches by the two mutually-inverse
cyclic rotations, and `miss` is preserved. -/
theorem zeroPivotCell_topPivotCell (u : GridSimplex d N) (hd1 : 0 < d)
    (hfeas : 1 ≤ (u.verts 0).coords (lastIncDir u hd1)) :
    zeroPivotCell (topPivotCell u hd1 hfeas) hd1
        (topPivotCell_zeroFeasible u hd1 hfeas) = u := by
  apply gridSimplex_ext
  · funext k
    by_cases hk : k.val < d
    · rw [zeroPivotCell_verts_of_lt _ hd1 _ k hk, topPivotCell_verts,
        topPivotVerts_of_pos u hd1 hfeas ⟨k.val + 1, by omega⟩ (by simp)]
      congr 1
    · have hklast : k = Fin.last d := by
        apply Fin.ext; simp only [Fin.val_last]; have := k.isLt; omega
      rw [hklast, zeroPivotCell_verts_last]
      exact zeroPivotTop_topPivotCell u hd1 hfeas
  · funext k
    show zeroPivotInc (topPivotCell u hd1 hfeas) hd1 k = u.incDir k
    by_cases hk : k.val + 1 < d
    · rw [zeroPivotInc_of_lt _ hd1 k hk, topPivotCell_incDir,
        topPivotInc_of_pos u hd1 ⟨k.val + 1, hk⟩ (by simp)]
      congr 1
    · rw [zeroPivotInc_last _ hd1 k hk, topPivotCell_incDir,
        topPivotInc_eq_lastIncDir u hd1 ⟨0, hd1⟩ rfl]
      show u.incDir ⟨d - 1, by omega⟩ = u.incDir k
      congr 1; apply Fin.ext; show d - 1 = k.val; have := k.isLt; omega
  · rw [zeroPivotCell_miss, topPivotCell_miss]

end SpernerNDimOQ02

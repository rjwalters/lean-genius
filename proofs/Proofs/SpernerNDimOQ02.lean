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

end SpernerNDimOQ02

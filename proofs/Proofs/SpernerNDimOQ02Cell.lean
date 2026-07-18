import Proofs.SpernerGridCell
import Proofs.SpernerNDimOQ02

/-
# sperner-ndim-oq-02: cell→Vertex bridge and the canonical-cell subtype

Phase 1 of "Option C" builds an *unoriented* `SpernerNDim.SpernerTriangulation d N`
instance whose `Simplex` type is **one canonical cell per geometric Freudenthal
simplex**. This file supplies the pieces that do **not** need the (orientation-free)
adjacency involution:

* `cellVertices` / `cellVertices_injective` — the `vertices` field of the eventual
  instance, obtained by pushing a cell's chain vertices through the verified
  coordinate bridge `SpernerNDimOQ02.toVertex` (`BaryPoint d N → Vertex d N`).
  Injectivity is `toVertex_injective ∘ GridSimplex.verts_injective`.
* `onFace_cellVertices` — the face correspondence at the level of cells, an
  immediate consequence of `SpernerNDimOQ02.onFace_toVertex`. This is what the
  `boundary_face` field will consume once `adj` is defined.
* `CanonCell` — the canonical-cell subtype that picks a single encoding per
  geometry (a `GridSimplex` is an *oriented chain*; the same vertex set admits
  several `(verts, incDir, miss)` encodings, which is exactly what makes the parent
  file's oriented `gridAdj` double-count). It is built directly on the canonical
  foundation `SpernerGrid.IsCanon`/`SpernerGrid.BaryPoint.lexLE` from
  `SpernerGridBase` (which says the chain base `s.verts 0` is lexicographically least
  among the cell's vertices), rather than on a private lex-order copy. Decidability
  and the (noncomputable) `Fintype` for the subtype reuse Base's `IsCanon` instances.
* `canonCell_eq_of_vertices_range` — **per-geometry uniqueness at the Kuhn level**:
  two canonical cells with the same Kuhn vertex set are equal. Lifts Base's proved
  `SpernerGrid.IsCanon.geometry_unique` across the injective bridge `toVertex`.

This converges the earlier private canonicality scaffold onto Base's `IsCanon`
development (#8998 item 3 / #38578): there is now a single lex order and a single
`IsCanon` predicate across the Sperner grid files.

Still open (next session): the facet-sharing dual-graph `adj` and its five
involution fields. Those complete the `SpernerTriangulation` instance; `sperner_ndim`
then finishes the proof, transported across `SpernerNDimOQ02.isSperner_iff`.

No new axioms or sorries: every declaration below depends only on the standard
`propext`/`Classical.choice`/`Quot.sound`.
-/

open Finset

namespace SpernerNDimOQ02

variable {d N : ℕ}

-- ============================================================
-- The `vertices` field: a cell's chain through the bridge
-- ============================================================

/-- The `d+1` Kuhn vertices of a Freudenthal cell, obtained by dropping the last
    barycentric coordinate of each chain vertex (`toVertex`). This is the
    `vertices` field of the Option-C `SpernerTriangulation` instance. -/
def cellVertices (s : SpernerGrid.GridSimplex d N) : Fin (d + 1) → SpernerNDim.Vertex d N :=
  fun k => toVertex (s.verts k)

@[simp]
theorem cellVertices_apply (s : SpernerGrid.GridSimplex d N) (k : Fin (d + 1)) :
    cellVertices s k = toVertex (s.verts k) := rfl

/-- The `vertices` field's injectivity obligation: a cell's `d+1` Kuhn vertices are
    pairwise distinct. The chain vertices are distinct (`GridSimplex.verts_injective`)
    and `toVertex` is injective (the forward map of the bridge `Equiv`). -/
theorem cellVertices_injective (s : SpernerGrid.GridSimplex d N) :
    Function.Injective (cellVertices s) :=
  toVertex_injective.comp s.verts_injective

/-- Face correspondence at the cell level: a chain vertex's image lies on Kuhn face
    `k` exactly when the chain vertex lies on barycentric face `k`. Feeds the
    `boundary_face` field once `adj` is in place. -/
theorem onFace_cellVertices (s : SpernerGrid.GridSimplex d N)
    (i : Fin (d + 1)) (k : Fin (d + 1)) :
    SpernerNDim.onFace (cellVertices s i) k ↔ (s.verts i).onFace k :=
  onFace_toVertex (s.verts i) k

-- ============================================================
-- Canonicality: one chain encoding per geometric cell
-- ============================================================

/-- The `Simplex` type of the Option-C instance: one canonical chain encoding per
    geometric Freudenthal cell. Built on Base's `SpernerGrid.IsCanon` (a cell is
    *canonical* when its chain base `verts 0` is lexicographically least — under
    `SpernerGrid.BaryPoint.lexLE` — among its `d+1` vertices). Since the chain
    direction of a Freudenthal cell is geometrically forced once the base is fixed
    (the `miss` coordinate strictly decreases along the chain), pinning the base to
    the lex-least vertex selects a single encoding per geometry — the device that
    eliminates the oriented `gridAdj` double-count. -/
def CanonCell (d N : ℕ) : Type := { s : SpernerGrid.GridSimplex d N // SpernerGrid.IsCanon s }

instance : DecidableEq (CanonCell d N) := Subtype.instDecidableEq

noncomputable instance : Fintype (CanonCell d N) := Subtype.fintype _

/-- The `vertices` map on the canonical subtype (the actual field of the
    forthcoming `SpernerTriangulation`). -/
def canonVertices (s : CanonCell d N) : Fin (d + 1) → SpernerNDim.Vertex d N :=
  cellVertices s.val

theorem canonVertices_injective (s : CanonCell d N) :
    Function.Injective (canonVertices s) :=
  cellVertices_injective s.val

/-- **Per-geometry uniqueness (Kuhn side).** Two canonical cells with the same Kuhn
    vertex *set* are equal. This lifts Base's proved
    `SpernerGrid.IsCanon.geometry_unique` (stated over barycentric points) across the
    injective bridge `toVertex`: equal image-sets under an injection have equal
    preimage sets, so the underlying grid simplices share a vertex set, geometry
    uniqueness makes them equal, and `Subtype.ext` finishes. It closes the
    canonicality scaffold's remaining obligation — there is exactly one canonical
    cell per geometric Freudenthal simplex — the well-definedness the facet-sharing
    `adj` will rely on. -/
theorem canonCell_eq_of_vertices_range {s t : CanonCell d N}
    (h : Set.range (canonVertices s) = Set.range (canonVertices t)) : s = t := by
  have key : ∀ u : CanonCell d N,
      Set.range (canonVertices u) = toVertex '' Set.range u.val.verts := by
    intro u
    have hcomp : canonVertices u = toVertex ∘ u.val.verts := rfl
    rw [hcomp, Set.range_comp]
  rw [key s, key t] at h
  have hbary : Set.range s.val.verts = Set.range t.val.verts :=
    Set.image_injective.mpr toVertex_injective h
  exact Subtype.ext (SpernerGrid.IsCanon.geometry_unique s.2 t.2 hbary)

end SpernerNDimOQ02

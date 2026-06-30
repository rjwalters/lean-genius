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
* `BaryPoint.lexLe` / `IsCanon` / `CanonCell` — the canonicality scaffolding that
  picks a single encoding per geometry (a `GridSimplex` is an *oriented chain*; the
  same vertex set admits several `(verts, incDir, miss)` encodings, which is exactly
  what makes the parent file's oriented `gridAdj` double-count). `IsCanon s` says the
  chain base `s.verts 0` is lexicographically least among the cell's vertices.
  Decidability and the (noncomputable) `Fintype` for the subtype are established here.

Still open (next session): the facet-sharing dual-graph `adj` and its five
involution fields, plus the per-geometry uniqueness of `IsCanon`. Those complete the
`SpernerTriangulation` instance; `sperner_ndim` then finishes the proof, transported
across `SpernerNDimOQ02.isSperner_iff`.

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

/-- Lexicographic `≤` on barycentric points: `a ≤ b` iff `a = b` or, at the first
    coordinate where they differ, `a` is smaller. Decidable because both the
    equality test and the bounded existential range over the finite `Fin (d+1)`. -/
def _root_.SpernerGrid.BaryPoint.lexLe (a b : SpernerGrid.BaryPoint d N) : Prop :=
  a = b ∨ ∃ i : Fin (d + 1),
    (∀ j : Fin (d + 1), j < i → a.coords j = b.coords j) ∧ a.coords i < b.coords i

instance (a b : SpernerGrid.BaryPoint d N) : Decidable (a.lexLe b) := by
  unfold SpernerGrid.BaryPoint.lexLe; infer_instance

/-- A cell is *canonical* when its chain base `verts 0` is lexicographically least
    among its `d+1` vertices. Since the chain direction of a Freudenthal cell is
    geometrically forced once the base is fixed (the `miss` coordinate strictly
    decreases along the chain, `GridSimplex.miss_coord_at`), pinning the base to the
    lex-least vertex selects a single encoding per geometry — the device that
    eliminates the oriented `gridAdj` double-count. -/
def IsCanon (s : SpernerGrid.GridSimplex d N) : Prop :=
  ∀ k : Fin (d + 1), (s.verts 0).lexLe (s.verts k)

instance : DecidablePred (IsCanon : SpernerGrid.GridSimplex d N → Prop) :=
  fun _ => by unfold IsCanon; infer_instance

/-- The `Simplex` type of the Option-C instance: one canonical chain encoding per
    geometric Freudenthal cell. -/
def CanonCell (d N : ℕ) : Type := { s : SpernerGrid.GridSimplex d N // IsCanon s }

instance : DecidableEq (CanonCell d N) := Subtype.instDecidableEq

noncomputable instance : Fintype (CanonCell d N) := Subtype.fintype _

/-- The `vertices` map on the canonical subtype (the actual field of the
    forthcoming `SpernerTriangulation`). -/
def canonVertices (s : CanonCell d N) : Fin (d + 1) → SpernerNDim.Vertex d N :=
  cellVertices s.val

theorem canonVertices_injective (s : CanonCell d N) :
    Function.Injective (canonVertices s) :=
  cellVertices_injective s.val

end SpernerNDimOQ02

import Mathlib
import Proofs.SpernerGridBase

/-
# The lex-min-base canonicality predicate omits genuine Freudenthal cells

`SpernerNDimOQ02.CanonSimplex d N := {s : GridSimplex d N // IsCanon s}` is the
intended orientation-free carrier for the Freudenthal triangulation, with
`IsCanon s := ∀ k, (s.verts 0).lexLE (s.verts k)` — the recorded chain base
`verts 0` is required to be the lex-minimal vertex of the cell.  The companion
file proves *at most one* canonical cell per geometry (`IsCanon.geometry_unique`),
so the design is sound **iff** every cell also has *at least one* canonical
representative.  This file proves the matching **existence direction is FALSE**:
there is a genuine Freudenthal cell whose geometry admits **no** canonical
representative.  Hence `CanonSimplex` is missing cells and, as the predicate
currently stands, cannot be the triangulation `Simplex` type.

## The structural obstruction

`GridSimplex.base_miss_ge_d` forces the base `verts 0` of *any* grid simplex to
carry a coordinate `≥ d`: its `miss` coordinate strictly decreases once per step,
`d` times in all, so at the base it is at least `d`.  But the *lex-minimal*
vertex of a cell can have **every** coordinate `< d`.  When that happens no grid
simplex realising that vertex set can place its base at the lex-minimum, i.e.
`IsCanon` is unsatisfiable for that geometry.

## The witness  (`d = 2`, `N = 2`)

The Freudenthal cell with vertices `(2,0,0)`, `(1,1,0)`, `(0,1,1)` — base
`(2,0,0)`, `miss = 0`, increment order `1, 2`.  All three barycentric points sum
to `2`, and the chain decrements coordinate `0` and increments coordinates `1`
then `2`.  Its lex-minimum is `(0,1,1)`, whose coordinates are all `≤ 1 < 2 = d`.
The `miss = 0` coordinate of the geometry is forced (it is the unique coordinate
with range `2`), so the only grid simplex on this vertex set is the one below,
which is not canonical, and no canonical one exists.
-/

namespace SpernerNDimOQ02Obstruction

open SpernerGrid

/-- **General obstruction.**  The chain base `verts 0` of *any* grid simplex
carries a coordinate `≥ d` — namely its `miss` coordinate (`base_miss_ge_d`).
A `CanonSimplex` additionally requires `verts 0` to be the lex-minimal vertex,
so the lex-minimum of every cell that *does* have a canonical representative must
have a coordinate `≥ d`.  Cells whose lex-minimum is "small" in every coordinate
are therefore unreachable. -/
theorem canon_base_has_large_coord {d N : ℕ} (t : GridSimplex d N) :
    ∃ j : Fin (d + 1), d ≤ (t.verts 0).coords j :=
  ⟨t.miss, t.base_miss_ge_d⟩

/-- **General small-lex-minimum obstruction.**  The formal content of the prose
"cells whose lex-minimum is small in every coordinate are unreachable": if a grid
simplex `t` has a vertex `v` that is the lex-minimum of its vertex set (`v` is
`lexLE` every vertex and lies in the range) and *every* coordinate of `v` is
`< d`, then `t` is not canonical.  Indeed `IsCanon t` would force the base
`t.verts 0` to be `lexLE v`; with `v` `lexLE` the base, antisymmetry
(`lexLE_antisymm`) pins `t.verts 0 = v`, so the base inherits `v`'s small
coordinates — contradicting `base_miss_ge_d`, which forces the base's `miss`
coordinate to be `≥ d`.  This is the single principle behind the concrete witness
below (`sBad_no_canon_rep`): its lex-minimum `(0,1,1)` has all coordinates `≤ 1 < 2`. -/
theorem not_canon_of_lexMin_small {d N : ℕ} (t : GridSimplex d N) (v : BaryPoint d N)
    (hmem : v ∈ Set.range t.verts) (hmin : ∀ k, v.lexLE (t.verts k))
    (hsmall : ∀ j, (v.coords j) < d) :
    ¬ IsCanon t := by
  intro hcanon
  -- Canonicality against the vertex realising `v` gives `base ≤ v`.
  have h1 : (t.verts 0).lexLE v := by
    obtain ⟨k, hk⟩ := hmem; have := hcanon k; rwa [hk] at this
  -- `v` is the lex-minimum, so `v ≤ base`.
  have h2 : v.lexLE (t.verts 0) := hmin 0
  -- Antisymmetry pins the base to `v`, which is small in every coordinate.
  have hbase : t.verts 0 = v := BaryPoint.lexLE_antisymm h1 h2
  have hge : d ≤ (t.verts 0).coords t.miss := t.base_miss_ge_d
  rw [hbase] at hge
  exact absurd hge (by have := hsmall t.miss; omega)

/-- The three barycentric points of the witness cell. -/
def p2 : BaryPoint 2 2 := ⟨![2, 0, 0], by decide⟩
def p1 : BaryPoint 2 2 := ⟨![1, 1, 0], by decide⟩
def p0 : BaryPoint 2 2 := ⟨![0, 1, 1], by decide⟩

/-- The witness Freudenthal cell: base `(2,0,0)`, `miss = 0`, increments `1, 2`. -/
def sBad : GridSimplex 2 2 where
  verts := ![p2, p1, p0]
  incDir := ![1, 2]
  miss := 0
  miss_ne_inc := by decide
  step_inc := by decide
  step_dec := by decide
  step_same := by decide
  inc_injective := by decide

/-- The witness cell is **not** canonical: its base `(2,0,0)` is the
lex-*maximum*, not the lex-minimum (`(0,1,1)` is). -/
theorem sBad_not_canon : ¬ IsCanon sBad := by
  intro h
  -- `IsCanon` would force `verts 0 = (2,0,0)` to be `lexLE` `verts 2 = (0,1,1)`.
  have hbad : (sBad.verts 0).lexLE (sBad.verts 2) := h 2
  revert hbad
  decide

/-- **The Phase-1 existence direction fails.**  No canonical grid simplex shares
the vertex set of `sBad`.  Any such `t` would have to place its base `t.verts 0`
at the lex-minimum `(0,1,1)` of the common vertex set; but `base_miss_ge_d`
forces some coordinate of `t.verts 0` to be `≥ 2`, while every coordinate of
`(0,1,1)` is `≤ 1`.  Contradiction.  Therefore `CanonSimplex 2 2` contains **no**
representative of this genuine Freudenthal cell — the `IsCanon` carrier omits
cells and cannot serve as the triangulation `Simplex` type unmodified. -/
theorem sBad_no_canon_rep :
    ¬ ∃ t : GridSimplex 2 2, IsCanon t ∧ Set.range t.verts = Set.range sBad.verts := by
  rintro ⟨t, hcanon, hrange⟩
  -- `(0,1,1) = sBad.verts 2` lies in `range sBad.verts = range t.verts`.
  have hp0_mem : p0 ∈ Set.range t.verts := by
    rw [hrange]; exact ⟨2, rfl⟩
  obtain ⟨k0, hk0⟩ := hp0_mem
  -- The base `t.verts 0` is one of the three witness vertices.
  have hbase_mem : t.verts 0 ∈ Set.range sBad.verts := by
    rw [← hrange]; exact ⟨0, rfl⟩
  obtain ⟨i, hi⟩ := hbase_mem
  -- Canonicality at `k0`: the base is `lexLE` `(0,1,1)`.
  have h1 : (t.verts 0).lexLE p0 := by
    have := hcanon k0; rwa [hk0] at this
  -- `(0,1,1)` is the lex-minimum of the witness set, so it is `lexLE` the base.
  have h2 : p0.lexLE (t.verts 0) := by
    rw [← hi]; fin_cases i <;> decide
  -- Antisymmetry pins the base to `(0,1,1)`.
  have hbase : t.verts 0 = p0 := BaryPoint.lexLE_antisymm h1 h2
  -- But `base_miss_ge_d` forces a base coordinate `≥ 2`, impossible for `(0,1,1)`.
  have hge : 2 ≤ (t.verts 0).coords t.miss := t.base_miss_ge_d
  rw [hbase] at hge
  have hle : ∀ j : Fin 3, p0.coords j ≤ 1 := by decide
  exact absurd hge (by have := hle t.miss; omega)

end SpernerNDimOQ02Obstruction

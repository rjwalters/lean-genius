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

/-- **General no-canonical-representative theorem.**  The abstract principle behind
the concrete `sBad_no_canon_rep`: if a grid simplex `t` has a vertex `v` that is the
lex-minimum of its vertex set (`v` is `lexLE` every vertex *in the range*) and every
coordinate of `v` is `< d`, then **no** grid simplex `t'` sharing `t`'s vertex set is
canonical.  Any such `t'` would have the same lex-minimum `v` — forcing its base to
`v` by canonicality and antisymmetry — but `base_miss_ge_d` demands a base coordinate
`≥ d`, which `v`'s small coordinates cannot supply (`not_canon_of_lexMin_small`).  This
lifts the single-witness obstruction to *every* cell with a small lex-minimum: the
`IsCanon` carrier omits the entire family of such cells, not just `sBad`. -/
theorem no_canon_rep_of_lexMin_small {d N : ℕ} (t : GridSimplex d N) (v : BaryPoint d N)
    (hmem : v ∈ Set.range t.verts)
    (hmin : ∀ w ∈ Set.range t.verts, v.lexLE w)
    (hsmall : ∀ j, (v.coords j) < d) :
    ¬ ∃ t' : GridSimplex d N, IsCanon t' ∧ Set.range t'.verts = Set.range t.verts := by
  rintro ⟨t', hcanon, hrange⟩
  have hvmem : v ∈ Set.range t'.verts := by rw [hrange]; exact hmem
  have hmin' : ∀ k, v.lexLE (t'.verts k) := fun k =>
    hmin (t'.verts k) (by rw [← hrange]; exact ⟨k, rfl⟩)
  exact not_canon_of_lexMin_small t' v hvmem hmin' hsmall hcanon

/-- **The chain base is never small in every coordinate.**  The hypothesis-free core of
the obstruction: for *any* grid simplex `t`, a barycentric point `v` all of whose
coordinates are `< d` can never be the base `t.verts 0`.  Indeed `base_miss_ge_d` forces
the base's `miss` coordinate to be `≥ d`, which `v`'s small coordinates cannot match.  No
canonicality or lex-minimality assumption is needed — it is a property of the base alone,
and is exactly what makes a small lex-minimum unreachable in `not_canon_of_lexMin_small`. -/
theorem base_ne_of_small {d N : ℕ} (t : GridSimplex d N) (v : BaryPoint d N)
    (hsmall : ∀ j, (v.coords j) < d) : v ≠ t.verts 0 := by
  intro h
  have hge : d ≤ (t.verts 0).coords t.miss := t.base_miss_ge_d
  rw [← h] at hge
  exact absurd hge (by have := hsmall t.miss; omega)

/-- **Range form of canonicality.**  Unfolds `IsCanon t` (the base is `lexLE` every indexed
vertex) to the set form: the base `t.verts 0` is `lexLE` every vertex `w` in the cell's
vertex *set* `Set.range t.verts`.  This is the shape the general obstruction consumes
(`no_canon_rep_of_lexMin_small` compares against `Set.range`), so it bridges the indexed
predicate to the geometry-level statement "the base is a lex-minimum of the cell". -/
theorem isCanon_base_lexLE_of_mem {d N : ℕ} (t : GridSimplex d N) (h : IsCanon t)
    {w : BaryPoint d N} (hw : w ∈ Set.range t.verts) : (t.verts 0).lexLE w := by
  obtain ⟨k, rfl⟩ := hw
  exact h k

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

/-! ## A second witness at `N = 3`, via the general theorem

The `sBad` obstruction (`d = 2, N = 2`) is not an artefact of the minimal grid size.
Here is a companion witness at `d = 2, N = 3` whose lex-minimum `(1,1,1)` again has every
coordinate `< d = 2`.  Unlike `sBad_no_canon_rep` — which was proved from first principles —
this one is discharged by simply *feeding the witness to the general theorem*
`no_canon_rep_of_lexMin_small`, confirming that the abstract obstruction (not just the single
`d = 2, N = 2` computation) is what does the work.  It also shows the obstructed family is
infinite along `N`: every `N ≥ 2` admits a cell whose lex-minimum is small in every
coordinate. -/

/-- The three barycentric points of the `N = 3` witness cell (each summing to `3`). -/
def q3 : BaryPoint 2 3 := ⟨![3, 0, 0], by decide⟩
def q2 : BaryPoint 2 3 := ⟨![2, 1, 0], by decide⟩
def q1 : BaryPoint 2 3 := ⟨![1, 1, 1], by decide⟩

/-- The `N = 3` witness Freudenthal cell: base `(3,0,0)`, `miss = 0`, increments `1, 2`.
Its lex-minimum is `(1,1,1)`, all of whose coordinates are `1 < 2 = d`. -/
def sBad3 : GridSimplex 2 3 where
  verts := ![q3, q2, q1]
  incDir := ![1, 2]
  miss := 0
  miss_ne_inc := by decide
  step_inc := by decide
  step_dec := by decide
  step_same := by decide
  inc_injective := by decide

/-- The witness cell `sBad3` is not canonical: its base `(3,0,0)` is the lex-maximum. -/
theorem sBad3_not_canon : ¬ IsCanon sBad3 := by
  intro h
  have hbad : (sBad3.verts 0).lexLE (sBad3.verts 2) := h 2
  revert hbad
  decide

/-- **The existence direction fails at `N = 3` too.**  No canonical grid simplex shares the
vertex set of `sBad3`.  Proved by applying the general `no_canon_rep_of_lexMin_small` to the
lex-minimum `(1,1,1)`: it is a vertex of the cell, is `lexLE` every vertex of the cell, and has
every coordinate `< 2`.  The single-witness obstruction of `sBad_no_canon_rep` is thus an
instance of a phenomenon that recurs across grid sizes. -/
theorem sBad3_no_canon_rep :
    ¬ ∃ t : GridSimplex 2 3, IsCanon t ∧ Set.range t.verts = Set.range sBad3.verts := by
  refine no_canon_rep_of_lexMin_small sBad3 q1 ⟨2, rfl⟩ ?_ ?_
  · rintro w ⟨k, rfl⟩; fin_cases k <;> decide
  · intro j; fin_cases j <;> decide

/-! ## A third witness in dimension `d = 3` — the obstruction is not a `d = 2` artefact

The witnesses `sBad` and `sBad3` both live in dimension `d = 2`.  The natural *infinite*
family of obstructed cells, however, runs along the **dimension** `d`, not the grid size `N`:
for each `d ≥ 2` the barycentric point `(1, 1, …, 1)` (all `d + 1` coordinates equal to `1`)
has every coordinate `1 < d`, and it sums to `d + 1`, so it lives in `BaryPoint d (d+1)` and is
the lex-minimum of the Freudenthal cell based at `(d+1, 0, …, 0)`.  (For *fixed* `d = 2`, by
contrast, only `N = 2, 3` admit an all-`< 2` vertex, since three coordinates each `≤ 1` sum to
at most `3`.)  Here is the next member of that dimensional family, `d = 3` at `N = 4`, with
lex-minimum `(1,1,1,1)`.  As with `sBad3`, it is discharged by feeding the witness to the
general `no_canon_rep_of_lexMin_small`, confirming the obstruction genuinely recurs in higher
dimension. -/

/-- The four barycentric points of the `d = 3` witness cell (each summing to `4`). -/
def r4 : BaryPoint 3 4 := ⟨![4, 0, 0, 0], by decide⟩
def r3 : BaryPoint 3 4 := ⟨![3, 1, 0, 0], by decide⟩
def r2 : BaryPoint 3 4 := ⟨![2, 1, 1, 0], by decide⟩
def r1 : BaryPoint 3 4 := ⟨![1, 1, 1, 1], by decide⟩

/-- The `d = 3` witness Freudenthal cell: base `(4,0,0,0)`, `miss = 0`, increments `1, 2, 3`.
Its lex-minimum is `(1,1,1,1)`, all of whose coordinates are `1 < 3 = d`. -/
def sBadD3 : GridSimplex 3 4 where
  verts := ![r4, r3, r2, r1]
  incDir := ![1, 2, 3]
  miss := 0
  miss_ne_inc := by decide
  step_inc := by decide
  step_dec := by decide
  step_same := by decide
  inc_injective := by decide

/-- The witness cell `sBadD3` is not canonical: its base `(4,0,0,0)` is the lex-maximum. -/
theorem sBadD3_not_canon : ¬ IsCanon sBadD3 := by
  intro h
  have hbad : (sBadD3.verts 0).lexLE (sBadD3.verts 3) := h 3
  revert hbad
  decide

/-- **The existence direction fails in dimension `d = 3` too.**  No canonical grid simplex
shares the vertex set of `sBadD3`.  Proved by applying the general
`no_canon_rep_of_lexMin_small` to the lex-minimum `(1,1,1,1)`: it is a vertex of the cell, is
`lexLE` every vertex of the cell, and has every coordinate `< 3`.  So the `IsCanon` carrier omits
cells in dimension `3` exactly as it does in dimension `2` — the obstruction is dimensional, and
recurs for every `d ≥ 2` via the all-ones lex-minimum at `N = d + 1`. -/
theorem sBadD3_no_canon_rep :
    ¬ ∃ t : GridSimplex 3 4, IsCanon t ∧ Set.range t.verts = Set.range sBadD3.verts := by
  refine no_canon_rep_of_lexMin_small sBadD3 r1 ⟨3, rfl⟩ ?_ ?_
  · rintro w ⟨k, rfl⟩; fin_cases k <;> decide
  · intro j; fin_cases j <;> decide

end SpernerNDimOQ02Obstruction

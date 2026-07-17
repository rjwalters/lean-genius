/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerGridBase

/-
# The d = 1, N = 1 faithfulness counterexample, machine-checked (issue #8998)

`SpernerGrid.GridSimplex` encodes grid simplices as *oriented chains*
`(verts, incDir, miss)`.  Issue #8998 records (in prose) that this
encoding is unfaithful — one geometric simplex can have several
distinct encodings — and that as a consequence the per-encoded-pair
boundary-door count of `SpernerGrid.lean`'s `boundary_doors_odd` is
**even** at `d = 1, N = 1` (namely 2), while the classical geometric
count is 1 (odd).  That legacy file no longer compiles on the pinned
toolchain, so the counterexample has never been machine-checked.

This file pins it on the *clean, compiling* foundation
`Proofs.SpernerGridBase` (same `GridSimplex` structure, plus the
`IsCanon` canonical-form layer with `IsCanon.geometry_unique`).
Everything below is fully verified: **0 sorries, 0 axioms**.

## Part 1 — the unfaithfulness witness and exact classification

* `S₁`, `S₂` : the two distinct `GridSimplex 1 1` encodings of the
  unique geometric edge of Δ₁ at N = 1 (`S₁_ne_S₂`,
  `S₁_S₂_same_range`).
* `gridSimplex_d1N1_cases` : they are the *only* cells, so all counts
  below are exact.
* `isCanon_iff_d1N1` : exactly one of them (`S₂`) is canonical — the
  concrete instance of `IsCanon.geometry_unique`'s
  one-representative-per-geometry promise.

## Part 2 — the parity bug, quantitatively

With `IsGridDoor` (the door predicate of the abstract Sperner theorem,
with `vertex := verts` inlined) and `OnSimplexBoundary` (the geometric
boundary of Δ), for **every** Sperner coloring:

* `oriented_boundary_door_count_d1N1` : the count over encoded
  `(cell, facet)` pairs is **2** — even, breaking the parity argument.
  (At `d = 1, N = 1` this matches the legacy `gridAdj` exactly: it
  returns `none` at precisely the facets on `OnSimplexBoundary`, so
  this is the machine-checked arithmetic of the `boundary_doors_odd`
  counterexample recorded on #8998.)
* `oriented_boundary_door_count_not_odd` : hence any
  `boundary_doors_odd`-style oddness claim over encoded pairs is
  false at `d = 1, N = 1`.

## Part 3 — the redesign target holds on canonical cells

* `canon_boundary_door_count_d1N1` : restricting to canonical cells
  (`IsCanon`), the boundary-door count is exactly **1** — odd, as the
  classical Sperner argument requires.  This is the acceptance
  criterion of #8998 at `d = 1, N = 1`.
* `canonFacetIncidence_*` : each geometric facet is incident to
  exactly **1** canonical cell (all facets are boundary at N = 1),
  while the oriented incidence is 2 — the oriented encoding is a
  double cover here, which is precisely what flipped the parity.

## What remains (next increments, tracked in #8998)

* The facet-sharing adjacency involution on canonical cells for
  general `d, N` (1 = boundary / 2 = interior incidence), on top of
  `IsCanon.geometry_unique`.
* The general `boundary_doors_odd` over canonical cells (dimensional
  induction), unlocking a sound `sperner_grid`.
-/

open Finset

namespace SpernerGrid

-- ============================================================
-- Part 0: helpers
-- ============================================================

private lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  revert i; decide

/-- Local copy of the (noncomputable) `Fintype` instance for
`GridSimplex`; `SpernerGridBase` does not carry one. -/
private noncomputable instance gridSimplexFintypeLocal (d N : ℕ) :
    Fintype (GridSimplex d N) :=
  Fintype.ofInjective
    (fun s : GridSimplex d N => (s.verts, s.incDir, s.miss))
    (fun a b h => by
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3; rfl)

/-- The door predicate of the abstract Sperner theorem
(`CellComplex.IsDoor`), specialised to grid cells with
`vertex := GridSimplex.verts` inlined: facet `k` of `s` sees every
color `0, …, d-1` among the vertices other than `k`. -/
def IsGridDoor {d N : ℕ} (c : BaryPoint d N → Fin (d + 1))
    (s : GridSimplex d N) (k : Fin (d + 1)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin (d + 1),
    i ≠ k ∧ c (s.verts i) = Fin.castSucc j

instance {d N : ℕ} (c : BaryPoint d N → Fin (d + 1))
    (s : GridSimplex d N) (k : Fin (d + 1)) :
    Decidable (IsGridDoor c s k) := by
  unfold IsGridDoor; exact inferInstance

/-- The geometric `(d-1)`-face carried by an encoded `(cell, facet)`
pair: the vertex set of the cell with the facet-opposite vertex
removed.  Two encoded pairs represent the same geometric face iff
their `geomFacet`s agree — the quotient a faithful count must use. -/
def geomFacet {d N : ℕ} (s : GridSimplex d N) (k : Fin (d + 1)) :
    Finset (BaryPoint d N) :=
  (univ.erase k).image s.verts

/-- A vertex set lies on the geometric boundary of the standard
simplex: some barycentric coordinate vanishes on all of it. -/
def OnSimplexBoundary {d N : ℕ} (F : Finset (BaryPoint d N)) : Prop :=
  ∃ j : Fin (d + 1), ∀ v ∈ F, v.coords j = 0

instance {d N : ℕ} (F : Finset (BaryPoint d N)) :
    Decidable (OnSimplexBoundary F) := by
  unfold OnSimplexBoundary; exact inferInstance

/-- Number of *canonical* cells incident to a given geometric facet.
The redesign target: 1 on the boundary, 2 in the interior. -/
noncomputable def canonFacetIncidence {d N : ℕ}
    (F : Finset (BaryPoint d N)) : ℕ :=
  (univ.filter (fun p : GridSimplex d N × Fin (d + 1) =>
    IsCanon p.1 ∧ geomFacet p.1 p.2 = F)).card

/-- Number of *oriented* (encoded) cells incident to a given geometric
facet — the unfaithful count the legacy `gridAdj` effectively uses. -/
noncomputable def orientedFacetIncidence {d N : ℕ}
    (F : Finset (BaryPoint d N)) : ℕ :=
  (univ.filter (fun p : GridSimplex d N × Fin (d + 1) =>
    geomFacet p.1 p.2 = F)).card

-- ============================================================
-- Part 1: the two encodings of the unique edge at d = 1, N = 1
-- ============================================================

/-- The lattice point `(1, 0)` of Δ₁ at N = 1 (on face 1). -/
def v10 : BaryPoint 1 1 := ⟨![1, 0], by decide⟩

/-- The lattice point `(0, 1)` of Δ₁ at N = 1 (on face 0). -/
def v01 : BaryPoint 1 1 := ⟨![0, 1], by decide⟩

theorem v10_ne_v01 : v10 ≠ v01 := by decide

/-- Every lattice point of Δ₁ at N = 1 is `(1,0)` or `(0,1)`. -/
theorem baryPoint_d1N1_cases (v : BaryPoint 1 1) : v = v10 ∨ v = v01 := by
  have hsum : v.coords 0 + v.coords 1 = 1 := by
    have h := v.sum_eq
    rwa [Fin.sum_univ_two] at h
  rcases Nat.eq_zero_or_pos (v.coords 0) with h0 | h0
  · right
    ext j
    rcases fin2_cases j with hj | hj <;> subst hj
    · show v.coords 0 = 0; omega
    · show v.coords 1 = 1; omega
  · left
    ext j
    rcases fin2_cases j with hj | hj <;> subst hj
    · show v.coords 0 = 1; omega
    · show v.coords 1 = 0; omega

/-- First encoding of the unique geometric edge: the chain
`(1,0) → (0,1)`, mass moves from coordinate 0 into coordinate 1. -/
def S₁ : GridSimplex 1 1 where
  verts := ![v10, v01]
  incDir := ![1]
  miss := 0
  miss_ne_inc := by decide
  step_inc := by decide
  step_dec := by decide
  step_same := by decide
  inc_injective := by decide

/-- Second encoding of the *same* geometric edge: the reversed chain
`(0,1) → (1,0)`, mass moves from coordinate 1 into coordinate 0. -/
def S₂ : GridSimplex 1 1 where
  verts := ![v01, v10]
  incDir := ![0]
  miss := 1
  miss_ne_inc := by decide
  step_inc := by decide
  step_dec := by decide
  step_same := by decide
  inc_injective := by decide

theorem S₁_ne_S₂ : S₁ ≠ S₂ := fun h =>
  absurd (congrArg GridSimplex.miss h) (by decide)

/-- **Unfaithfulness witness**: distinct cells, same geometric vertex
set — one geometric simplex, two encodings. -/
theorem S₁_S₂_same_range : Set.range S₁.verts = Set.range S₂.verts := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    rcases fin2_cases i with hi | hi <;> subst hi
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- **Exact classification**: `S₁` and `S₂` are the only cells at
`d = 1, N = 1`, so all counts below are exact. -/
theorem gridSimplex_d1N1_cases (s : GridSimplex 1 1) : s = S₁ ∨ s = S₂ := by
  have hdec : (s.verts 0).coords s.miss = (s.verts 1).coords s.miss + 1 :=
    s.step_dec 0
  have hsum0 : (s.verts 0).coords 0 + (s.verts 0).coords 1 = 1 := by
    have h := (s.verts 0).sum_eq
    rwa [Fin.sum_univ_two] at h
  have hne := s.miss_ne_inc 0
  rcases fin2_cases s.miss with hm | hm
  · -- miss = 0, incDir 0 = 1: this is S₁
    left
    have hi : s.incDir 0 = 1 := by
      rcases fin2_cases (s.incDir 0) with h | h
      · exact absurd (h.trans hm.symm) hne
      · exact h
    refine s.eq_of_base_miss_incDir S₁ ?_ ?_ ?_
    · rw [hm] at hdec
      ext j
      rcases fin2_cases j with hj | hj <;> subst hj
      · show (s.verts 0).coords 0 = 1; omega
      · show (s.verts 0).coords 1 = 0; omega
    · exact hm
    · funext k
      rw [Subsingleton.elim k 0]
      exact hi
  · -- miss = 1, incDir 0 = 0: this is S₂
    right
    have hi : s.incDir 0 = 0 := by
      rcases fin2_cases (s.incDir 0) with h | h
      · exact h
      · exact absurd (h.trans hm.symm) hne
    refine s.eq_of_base_miss_incDir S₂ ?_ ?_ ?_
    · rw [hm] at hdec
      ext j
      rcases fin2_cases j with hj | hj <;> subst hj
      · show (s.verts 0).coords 0 = 0; omega
      · show (s.verts 0).coords 1 = 1; omega
    · exact hm
    · funext k
      rw [Subsingleton.elim k 0]
      exact hi

/-- Exactly one of the two encodings is canonical: `S₂`, whose base
`(0,1)` is the lex-minimum of the edge's vertex set. -/
theorem isCanon_S₂ : IsCanon S₂ := by decide

theorem not_isCanon_S₁ : ¬ IsCanon S₁ := by decide

/-- **One canonical representative per geometry**, concretely: the
canonical cells at `d = 1, N = 1` are exactly `{S₂}`.  (The abstract
statement is `IsCanon.geometry_unique` in `SpernerGridBase`.) -/
theorem isCanon_iff_d1N1 (s : GridSimplex 1 1) : IsCanon s ↔ s = S₂ := by
  constructor
  · intro hs
    rcases gridSimplex_d1N1_cases s with h | h
    · exact absurd (h ▸ hs) not_isCanon_S₁
    · exact h
  · rintro rfl
    exact isCanon_S₂

-- ============================================================
-- Part 2: Sperner colorings and doors at d = 1, N = 1
-- ============================================================

/-- Any Sperner coloring is forced: `c (1,0) = 0` and `c (0,1) = 1`. -/
theorem sperner_forced {c : BaryPoint 1 1 → Fin 2} (hc : IsSperner c) :
    c v10 = 0 ∧ c v01 = 1 := by
  constructor
  · have h := hc v10 1 (by decide)
    rcases fin2_cases (c v10) with h0 | h1
    · exact h0
    · exact absurd h1 h
  · have h := hc v01 0 (by decide)
    rcases fin2_cases (c v01) with h0 | h1
    · exact absurd h0 h
    · exact h1

/-- The (unique) Sperner coloring at `d = 1, N = 1`, explicitly. -/
def c₀ : BaryPoint 1 1 → Fin 2 := fun v => if v.coords 0 = 0 then 1 else 0

theorem c₀_isSperner : IsSperner c₀ := by
  intro v k hface
  have hsum : v.coords 0 + v.coords 1 = 1 := by
    have h := v.sum_eq
    rwa [Fin.sum_univ_two] at h
  unfold BaryPoint.onFace at hface
  rcases fin2_cases k with hk | hk <;> subst hk
  · -- on face 0: coords 0 = 0, so c₀ v = 1 ≠ 0
    simp only [c₀, hface, if_true]
    decide
  · -- on face 1: coords 1 = 0, so coords 0 = 1 and c₀ v = 0 ≠ 1
    have h0 : v.coords 0 ≠ 0 := by omega
    simp only [c₀, h0, if_false]
    decide

theorem isGridDoor_S₁_one {c : BaryPoint 1 1 → Fin 2}
    (hc : IsSperner c) : IsGridDoor c S₁ 1 := by
  intro j
  refine ⟨0, by decide, ?_⟩
  have hj : Fin.castSucc j = (0 : Fin 2) := by
    rw [Subsingleton.elim j 0]; decide
  rw [hj]
  show c v10 = 0
  exact (sperner_forced hc).1

theorem isGridDoor_S₂_zero {c : BaryPoint 1 1 → Fin 2}
    (hc : IsSperner c) : IsGridDoor c S₂ 0 := by
  intro j
  refine ⟨1, by decide, ?_⟩
  have hj : Fin.castSucc j = (0 : Fin 2) := by
    rw [Subsingleton.elim j 0]; decide
  rw [hj]
  show c v10 = 0
  exact (sperner_forced hc).1

theorem not_isGridDoor_S₁_zero {c : BaryPoint 1 1 → Fin 2}
    (hc : IsSperner c) : ¬ IsGridDoor c S₁ 0 := by
  intro h
  obtain ⟨i, hi, hcol⟩ := h 0
  have hi1 : i = 1 := by
    rcases fin2_cases i with h' | h'
    · exact absurd h' hi
    · exact h'
  subst hi1
  have hv : c v01 = Fin.castSucc (0 : Fin 1) := hcol
  rw [(sperner_forced hc).2] at hv
  exact absurd hv (by decide)

theorem not_isGridDoor_S₂_one {c : BaryPoint 1 1 → Fin 2}
    (hc : IsSperner c) : ¬ IsGridDoor c S₂ 1 := by
  intro h
  obtain ⟨i, hi, hcol⟩ := h 0
  have hi0 : i = 0 := by
    rcases fin2_cases i with h' | h'
    · exact h'
    · exact absurd h' hi
  subst hi0
  have hv : c v01 = Fin.castSucc (0 : Fin 1) := hcol
  rw [(sperner_forced hc).2] at hv
  exact absurd hv (by decide)

-- ------------------------------------------------------------
-- Geometric facets at d = 1, N = 1
-- ------------------------------------------------------------

theorem geomFacet_S₁_one : geomFacet S₁ 1 = {v10} := by decide

theorem geomFacet_S₂_zero : geomFacet S₂ 0 = {v10} := by decide

theorem geomFacet_S₁_zero : geomFacet S₁ 0 = {v01} := by decide

theorem geomFacet_S₂_one : geomFacet S₂ 1 = {v01} := by decide

theorem onBoundary_v10 : OnSimplexBoundary ({v10} : Finset (BaryPoint 1 1)) :=
  ⟨1, by decide⟩

theorem onBoundary_v01 : OnSimplexBoundary ({v01} : Finset (BaryPoint 1 1)) :=
  ⟨0, by decide⟩

-- ============================================================
-- Part 3: the counts — 2 (even, bug) vs 1 (odd, target)
-- ============================================================

/-- The encoded boundary-door set is exactly `{(S₁,1), (S₂,0)}`: the
single geometric boundary door `{(1,0)}`, once per encoding. -/
theorem oriented_boundary_doors_d1N1_eq (c : BaryPoint 1 1 → Fin 2)
    (hc : IsSperner c) :
    (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsGridDoor c p.1 p.2 ∧ OnSimplexBoundary (geomFacet p.1 p.2))) =
    {(S₁, 1), (S₂, 0)} := by
  ext p
  obtain ⟨s, k⟩ := p
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hdoor, -⟩
    rcases gridSimplex_d1N1_cases s with hs | hs <;> subst hs <;>
      rcases fin2_cases k with hk | hk <;> subst hk
    · exact absurd hdoor (not_isGridDoor_S₁_zero hc)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact absurd hdoor (not_isGridDoor_S₂_one hc)
  · rintro (⟨hs, hk⟩ | ⟨hs, hk⟩) <;> subst hs <;> subst hk
    · exact ⟨isGridDoor_S₁_one hc, geomFacet_S₁_one ▸ onBoundary_v10⟩
    · exact ⟨isGridDoor_S₂_zero hc, geomFacet_S₂_zero ▸ onBoundary_v10⟩

/-- **The parity bug, quantitatively**: counting boundary doors over
encoded `(cell, facet)` pairs gives **2** for every Sperner coloring —
even.  The classical geometric count is 1.  (At `d = 1, N = 1` the
legacy `gridAdj` returns `none` exactly at the `OnSimplexBoundary`
facets, so this is the arithmetic of the `boundary_doors_odd`
counterexample recorded on issue #8998.) -/
theorem oriented_boundary_door_count_d1N1 (c : BaryPoint 1 1 → Fin 2)
    (hc : IsSperner c) :
    (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsGridDoor c p.1 p.2 ∧
      OnSimplexBoundary (geomFacet p.1 p.2))).card = 2 := by
  rw [oriented_boundary_doors_d1N1_eq c hc]
  refine Finset.card_pair ?_
  intro h
  exact S₁_ne_S₂ (congrArg Prod.fst h)

/-- Hence a `boundary_doors_odd`-style oddness claim over encoded
pairs is **false** at `d = 1, N = 1` (witnessed by `c₀`): the
oriented-chain encoding double-counts the boundary and flips the
parity that the abstract Sperner theorem needs. -/
theorem oriented_boundary_door_count_not_odd :
    ¬ Odd (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsGridDoor c₀ p.1 p.2 ∧
      OnSimplexBoundary (geomFacet p.1 p.2))).card := by
  rw [oriented_boundary_door_count_d1N1 c₀ c₀_isSperner, Nat.odd_iff]
  omega

/-- On **canonical** cells the boundary-door set collapses to the
single pair `{(S₂, 0)}`. -/
theorem canon_boundary_doors_d1N1_eq (c : BaryPoint 1 1 → Fin 2)
    (hc : IsSperner c) :
    (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsCanon p.1 ∧ IsGridDoor c p.1 p.2 ∧
      OnSimplexBoundary (geomFacet p.1 p.2))) =
    {(S₂, 0)} := by
  ext p
  obtain ⟨s, k⟩ := p
  simp only [mem_filter, mem_univ, true_and, mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hcanon, hdoor, -⟩
    have hs : s = S₂ := (isCanon_iff_d1N1 s).mp hcanon
    subst hs
    rcases fin2_cases k with hk | hk <;> subst hk
    · exact ⟨rfl, rfl⟩
    · exact absurd hdoor (not_isGridDoor_S₂_one hc)
  · rintro ⟨hs, hk⟩
    subst hs; subst hk
    exact ⟨isCanon_S₂, isGridDoor_S₂_zero hc,
      geomFacet_S₂_zero ▸ onBoundary_v10⟩

/-- **The redesign target holds at the counterexample**: over
canonical cells the boundary-door count is exactly **1** for every
Sperner coloring — the acceptance criterion of issue #8998 at
`d = 1, N = 1`. -/
theorem canon_boundary_door_count_d1N1 (c : BaryPoint 1 1 → Fin 2)
    (hc : IsSperner c) :
    (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsCanon p.1 ∧ IsGridDoor c p.1 p.2 ∧
      OnSimplexBoundary (geomFacet p.1 p.2))).card = 1 := by
  rw [canon_boundary_doors_d1N1_eq c hc]
  exact Finset.card_singleton _

/-- The canonical boundary-door count is **odd**, restoring the parity
the classical Sperner argument requires. -/
theorem canon_boundary_doors_odd_d1N1 (c : BaryPoint 1 1 → Fin 2)
    (hc : IsSperner c) :
    Odd (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsCanon p.1 ∧ IsGridDoor c p.1 p.2 ∧
      OnSimplexBoundary (geomFacet p.1 p.2))).card := by
  rw [canon_boundary_door_count_d1N1 c hc]
  exact ⟨0, rfl⟩

-- ============================================================
-- Part 4: facet incidence — double cover collapses to 1
-- ============================================================

/-- The facet `{(1,0)}` is incident to exactly **one** canonical cell
(it is a boundary facet). -/
theorem canonFacetIncidence_v10 :
    canonFacetIncidence ({v10} : Finset (BaryPoint 1 1)) = 1 := by
  unfold canonFacetIncidence
  have heq : (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsCanon p.1 ∧ geomFacet p.1 p.2 = {v10})) = {(S₂, 0)} := by
    ext p
    obtain ⟨s, k⟩ := p
    simp only [mem_filter, mem_univ, true_and, mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hcanon, hfacet⟩
      have hs : s = S₂ := (isCanon_iff_d1N1 s).mp hcanon
      subst hs
      rcases fin2_cases k with hk | hk <;> subst hk
      · exact ⟨rfl, rfl⟩
      · rw [geomFacet_S₂_one] at hfacet
        exact absurd hfacet (by decide)
    · rintro ⟨hs, hk⟩
      subst hs; subst hk
      exact ⟨isCanon_S₂, geomFacet_S₂_zero⟩
  rw [heq]
  exact Finset.card_singleton _

/-- The facet `{(0,1)}` is incident to exactly **one** canonical cell
(it is a boundary facet). -/
theorem canonFacetIncidence_v01 :
    canonFacetIncidence ({v01} : Finset (BaryPoint 1 1)) = 1 := by
  unfold canonFacetIncidence
  have heq : (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      IsCanon p.1 ∧ geomFacet p.1 p.2 = {v01})) = {(S₂, 1)} := by
    ext p
    obtain ⟨s, k⟩ := p
    simp only [mem_filter, mem_univ, true_and, mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨hcanon, hfacet⟩
      have hs : s = S₂ := (isCanon_iff_d1N1 s).mp hcanon
      subst hs
      rcases fin2_cases k with hk | hk <;> subst hk
      · rw [geomFacet_S₂_zero] at hfacet
        exact absurd hfacet (by decide)
      · exact ⟨rfl, rfl⟩
    · rintro ⟨hs, hk⟩
      subst hs; subst hk
      exact ⟨isCanon_S₂, geomFacet_S₂_one⟩
  rw [heq]
  exact Finset.card_singleton _

/-- In contrast, the *oriented* incidence of `{(1,0)}` is **2**: the
oriented encoding is a double cover of the geometry at `d = 1`, which
is exactly what flipped the boundary-door parity. -/
theorem orientedFacetIncidence_v10 :
    orientedFacetIncidence ({v10} : Finset (BaryPoint 1 1)) = 2 := by
  unfold orientedFacetIncidence
  have heq : (univ.filter (fun p : GridSimplex 1 1 × Fin 2 =>
      geomFacet p.1 p.2 = {v10})) = {(S₁, 1), (S₂, 0)} := by
    ext p
    obtain ⟨s, k⟩ := p
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton,
      Prod.mk.injEq]
    constructor
    · intro hfacet
      rcases gridSimplex_d1N1_cases s with hs | hs <;> subst hs <;>
        rcases fin2_cases k with hk | hk <;> subst hk
      · rw [geomFacet_S₁_zero] at hfacet
        exact absurd hfacet (by decide)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, rfl⟩
      · rw [geomFacet_S₂_one] at hfacet
        exact absurd hfacet (by decide)
    · rintro (⟨hs, hk⟩ | ⟨hs, hk⟩) <;> subst hs <;> subst hk
      · exact geomFacet_S₁_one
      · exact geomFacet_S₂_zero
  rw [heq]
  refine Finset.card_pair ?_
  intro h
  exact S₁_ne_S₂ (congrArg Prod.fst h)

end SpernerGrid

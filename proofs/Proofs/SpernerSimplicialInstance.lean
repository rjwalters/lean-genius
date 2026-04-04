/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerMathlib4

/-
# SimplicialComplex to CellComplex Bridge for Sperner's Lemma

This file bridges the gap between simplicial complexes and our
abstract `CellComplex` structure from `SpernerMathlib4.lean`.

## The Architecture

Part 1 (done in SpernerMathlib4.lean): Abstract `CellComplex`
  with adjacency axioms, and the Sperner parity theorem proved
  for any `CellComplex`.

Part 2 (this file): Show that a triangulation of the standard
  simplex satisfying a pseudomanifold condition gives rise to a
  `CellComplex` instance.

## Strategy

We define a `Triangulation` structure that axiomatizes exactly
what we need: a finite pure simplicial complex with the
pseudomanifold property. The structure has the same fields as
`CellComplex` plus vertex injectivity, so the bridge is
immediate.

We also define `AbstractSimplicialData` for constructing a
`Triangulation` from unordered simplices (as in Mathlib's
`Geometry.SimplicialComplex`), and provide a concrete 1-d
interval example with fully proved axioms.

## Main definitions

* `Triangulation V n`: A triangulation with ordered vertices.
* `Triangulation.toCellComplex`: The `CellComplex` instance.
* `AbstractSimplicialData V n`: Unordered simplicial data.
* `intervalTriangulation m`: Concrete 1-d example.

## Main results

* `Triangulation.sperner`: Sperner's lemma for triangulations.
* Interval triangulation: all axioms fully proved (0 sorries).

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]
* Yael Dillies, mathlib4#25231, mathlib4#34310

## Tags

Sperner, simplicial complex, triangulation, cell complex, bridge
-/

set_option maxHeartbeats 1600000

open Finset

/-! ## Triangulation Structure

We axiomatize a finite pure simplicial complex with the
pseudomanifold property. This is the minimal interface needed
to construct a `CellComplex`.

The key insight: `Triangulation` has exactly the same fields as
`CellComplex` plus `vertex_injective`, so the bridge construction
`toCellComplex` is trivial (just forget the extra field). -/

/-- A `Triangulation V n` is a finite collection of
top-dimensional simplices (each an ordered `(n+1)`-tuple of
vertices from `V`) satisfying the pseudomanifold condition:
each codimension-1 face belongs to at most 2 top simplices.

This is the minimal abstraction needed to instantiate
`CellComplex` and apply the abstract Sperner theorem. -/
structure Triangulation (V : Type*) [DecidableEq V]
    (n : ℕ) where
  /-- The type of top-dimensional cells (n-simplices). -/
  Cell : Type
  /-- Decidable equality on cells. -/
  cellDecEq : DecidableEq Cell
  /-- Finiteness of cells. -/
  cellFintype : Fintype Cell
  /-- The ordered vertices of each cell: vertex k is the k-th
  vertex of cell s. Each cell has n+1 distinct vertices. -/
  vertex : Cell → Fin (n + 1) → V
  /-- Vertices within a single cell are distinct. -/
  vertex_injective : ∀ s, Function.Injective (vertex s)
  /-- Pseudomanifold adjacency: for each cell s and face
  position k, either there is a unique neighboring cell s'
  sharing the codim-1 face, or the face is on the boundary. -/
  adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1))
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ s k s' k',
    adj s k = some (s', k') → adj s' k' = some (s, k)
  /-- Adjacent cells share the codimension-1 face. -/
  adj_vertex : ∀ s k s' k',
    adj s k = some (s', k') →
    (univ.erase k).image (vertex s) =
    (univ.erase k').image (vertex s')
  /-- Adjacent cells are distinct. -/
  adj_ne : ∀ s k s' k',
    adj s k = some (s', k') → s ≠ s'

attribute [instance] Triangulation.cellDecEq
attribute [instance] Triangulation.cellFintype

namespace Triangulation

variable {V : Type*} [DecidableEq V] {n : ℕ}

/-! ## CellComplex Instance

The bridge is immediate: `Triangulation` extends `CellComplex`
with `vertex_injective`, so we just forget it. -/

/-- Every `Triangulation` gives rise to a `CellComplex`. -/
def toCellComplex (T : Triangulation V n) : CellComplex V n where
  Cell := T.Cell
  cellDecEq := T.cellDecEq
  cellFintype := T.cellFintype
  vertex := T.vertex
  adj := T.adj
  adj_symm := T.adj_symm
  adj_vertex := T.adj_vertex
  adj_ne := T.adj_ne

/-! ## Sperner Coloring and Main Theorem -/

/-- A Sperner coloring: if vertex v is on face k (determined by
the predicate `onFace`), then `c v` is not `k`. -/
def IsSpernerColoring
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop) : Prop :=
  ∀ v k, onFace v k → c v ≠ k

/-- **Sperner's Lemma for Triangulations**: Given a triangulation
whose boundary doors are odd, a panchromatic cell exists.

This is a direct application of the abstract `CellComplex.sperner`
theorem via the `toCellComplex` bridge. -/
theorem sperner (T : Triangulation V n)
    (c : V → Fin (n + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none)).card) :
    ∃ s : T.Cell,
      CellComplex.IsPanchromatic c (T.toCellComplex) s :=
  CellComplex.sperner c T.toCellComplex hbdry

/-! ## Boundary Door Parity

The key geometric fact for the standard simplex: with a Sperner
coloring, boundary doors are odd. This decomposes by face and
uses induction on dimension.

We state this with explicit hypotheses that can be discharged
for any concrete triangulation. -/

/-- **Boundary door parity for triangulations**: Given
decomposition hypotheses about boundary doors on each geometric
face, the total boundary door count is odd.

The hypotheses separate doors by which geometric face they lie
on. Doors on faces 0 through n-1 pair up (even), and doors on
face n are odd (by induction). -/
theorem boundary_doors_odd (T : Triangulation V n)
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (_hSperner : IsSpernerColoring c onFace)
    (_hBoundaryOnFace : ∀ s k, T.adj s k = none →
      ∃ faceIdx : Fin (n + 1), ∀ j : Fin (n + 1),
        j ≠ k → onFace (T.vertex s j) faceIdx)
    (_hLowerDim : ∀ faceIdx : Fin (n + 1),
      faceIdx.val < n →
      Even (Finset.univ.filter (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (T.vertex p.1 j) faceIdx))).card)
    (_hLastFace : Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (T.vertex p.1 j)
            ⟨n, by omega⟩))).card) :
    Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none)).card := by
  sorry

/-! ## Construction from Unordered Simplices

When starting from unordered simplices (Mathlib's
`Geometry.SimplicialComplex` uses `Finset V`), we need a
`LinearOrder V` to produce ordered vertices via `Finset.sort`.

`AbstractSimplicialData` packages this construction. -/

/-- Unordered simplicial data: a finite set of top simplices
with the pseudomanifold property. -/
structure AbstractSimplicialData (V : Type*) [DecidableEq V]
    [LinearOrder V] (n : ℕ) where
  /-- The top-dimensional simplices. -/
  topSimplices : Finset (Finset V)
  /-- Each top simplex has exactly n+1 vertices. -/
  card_eq : ∀ s ∈ topSimplices, s.card = n + 1
  /-- Pseudomanifold: each codim-1 face is in at most 2 top
  simplices. -/
  pseudomanifold : ∀ (face : Finset V),
    face.card = n →
    (topSimplices.filter (fun s => face ⊆ s)).card ≤ 2

/-
## Face Helper Library

Named helpers for working with codimension-1 faces of top
simplices. These factor out the key operations needed to
construct adjacency for `toTriangulation`. -/

section FaceHelpers

variable {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
variable (D : AbstractSimplicialData V n)

/-- The ordered vertex enumeration of a top simplex. -/
noncomputable def AbstractSimplicialData.vertexEnum
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  (s.sort (· ≤ ·)).get (k.cast (by rw [Finset.length_sort]; exact (D.card_eq s hs).symm))

/-- The k-th vertex is a member of the simplex. -/
lemma AbstractSimplicialData.vertexEnum_mem
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    D.vertexEnum s hs k ∈ s := by
  unfold vertexEnum
  have hmem := List.get_mem (s.sort (· ≤ ·))
    (k.cast (by rw [Finset.length_sort]; exact (D.card_eq s hs).symm))
  exact (s.mem_sort (· ≤ ·)).mp hmem

/-- The codimension-1 face obtained by deleting the k-th vertex. -/
noncomputable def AbstractSimplicialData.faceOf
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : Finset V :=
  s.erase (D.vertexEnum s hs k)

/-- A face has cardinality n. -/
lemma AbstractSimplicialData.faceOf_card
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    (D.faceOf s hs k).card = n := by
  simp only [faceOf]
  rw [Finset.card_erase_of_mem (D.vertexEnum_mem s hs k)]
  have := D.card_eq s hs
  omega

/-- A face is a subset of the simplex. -/
lemma AbstractSimplicialData.faceOf_subset
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    D.faceOf s hs k ⊆ s :=
  Finset.erase_subset _ _

/-- Top simplices containing a given face. -/
noncomputable def AbstractSimplicialData.containersOf
    (f : Finset V) : Finset (Finset V) :=
  D.topSimplices.filter (fun t => f ⊆ t)

/-- The original simplex contains its own face. -/
lemma AbstractSimplicialData.self_mem_containersOf
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    s ∈ D.containersOf (D.faceOf s hs k) := by
  simp only [containersOf, Finset.mem_filter]
  exact ⟨hs, D.faceOf_subset s hs k⟩

/-- Container count is at most 2 (pseudomanifold). -/
lemma AbstractSimplicialData.containersOf_card_le_two
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    (D.containersOf (D.faceOf s hs k)).card ≤ 2 :=
  D.pseudomanifold _ (D.faceOf_card s hs k)

/-- Container count is 1 or 2. -/
lemma AbstractSimplicialData.containersOf_card_one_or_two
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    (D.containersOf (D.faceOf s hs k)).card = 1 ∨
    (D.containersOf (D.faceOf s hs k)).card = 2 := by
  have h1 : 0 < (D.containersOf (D.faceOf s hs k)).card :=
    Finset.card_pos.mpr ⟨s, D.self_mem_containersOf s hs k⟩
  have h2 := D.containersOf_card_le_two s hs k
  omega

/-- The difference `t \ f` is nonempty when `t` has `n+1` elements
and `f` has `n` elements with `f ⊆ t`. -/
lemma AbstractSimplicialData.sdiff_nonempty
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (_hf : f ⊆ t) (hfc : f.card = n) :
    (t \ f).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hsub := Finset.sdiff_eq_empty_iff_subset.mp h
  have := D.card_eq t ht
  have := Finset.card_le_card hsub
  omega

/-- Given a top simplex `t` containing face `f`, find the index
in `t`'s sorted vertex list of the unique vertex in `t \ f`.
Returns the position of the "opposite" vertex. -/
noncomputable def AbstractSimplicialData.findOppositeIdx
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (_hf : f ⊆ t) (hfc : f.card = n) :
    Fin (n + 1) :=
  -- There exists k such that vertexEnum t ht k is not in f.
  -- Since t has n+1 vertices and f has n with f ⊆ t, at least one
  -- vertex of t is not in f.
  have hex : ∃ k : Fin (n + 1), D.vertexEnum t ht k ∉ f := by
    by_contra hall
    push_neg at hall
    -- Every vertex of t is in f, so t ⊆ f
    have hsub : t ⊆ f := by
      intro v hv
      -- v is in t, so v appears somewhere in t.sort
      have hv_sort : v ∈ t.sort (· ≤ ·) := (t.mem_sort (· ≤ ·)).mpr hv
      rw [List.mem_iff_getElem] at hv_sort
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
      have hidx_lt' : idx < n + 1 := by
        rwa [Finset.length_sort, D.card_eq t ht] at hidx_lt
      have hmem := hall ⟨idx, hidx_lt'⟩
      -- vertexEnum t ht ⟨idx, hidx_lt'⟩ = (t.sort (· ≤ ·)).get (cast ⟨idx, ...⟩)
      -- which equals (t.sort (· ≤ ·))[idx] = v
      -- Use the fact that vertexEnum_mem gives us membership
      -- and that vertexEnum at index idx equals (t.sort ...)[idx]
      have heq : D.vertexEnum t ht ⟨idx, hidx_lt'⟩ = v := by
        simp only [vertexEnum, List.get_eq_getElem]
        exact hidx_eq
      rwa [heq] at hmem
    have := Finset.card_le_card hsub
    rw [D.card_eq t ht, hfc] at this
    omega
  hex.choose

/-- The opposite vertex is not in the face. -/
lemma AbstractSimplicialData.vertexEnum_findOppositeIdx_not_mem
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (hf : f ⊆ t) (hfc : f.card = n) :
    D.vertexEnum t ht (D.findOppositeIdx t ht f hf hfc) ∉ f := by
  unfold findOppositeIdx
  generalize_proofs hex
  exact hex.choose_spec

/-- Erasing the opposite vertex from t gives back f. -/
lemma AbstractSimplicialData.erase_opposite_eq
    (t : Finset V) (ht : t ∈ D.topSimplices)
    (f : Finset V) (hf : f ⊆ t) (hfc : f.card = n) :
    t.erase (D.vertexEnum t ht (D.findOppositeIdx t ht f hf hfc)) = f := by
  set v := D.vertexEnum t ht (D.findOppositeIdx t ht f hf hfc) with hv_def
  have hv_not_f : v ∉ f := D.vertexEnum_findOppositeIdx_not_mem t ht f hf hfc
  have hv_mem_t : v ∈ t := D.vertexEnum_mem t ht (D.findOppositeIdx t ht f hf hfc)
  have h_sub : f ⊆ t.erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hv_not_f (h ▸ hx), hf hx⟩
  have h_card : (t.erase v).card ≤ f.card := by
    rw [Finset.card_erase_of_mem hv_mem_t, D.card_eq t ht, hfc]
    omega
  exact (Finset.eq_of_subset_of_card_le h_sub h_card).symm

/-- The faceOf operation is the same as erasing a vertex. -/
lemma AbstractSimplicialData.faceOf_eq
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    D.faceOf s hs k = s.erase (D.vertexEnum s hs k) :=
  rfl

/-- If vertexEnum s hs j ∈ s.erase (vertexEnum s hs k), then j ≠ k. -/
lemma AbstractSimplicialData.vertexEnum_not_mem_faceOf_iff
    (s : Finset V) (hs : s ∈ D.topSimplices) (j k : Fin (n + 1)) :
    D.vertexEnum s hs j ∉ D.faceOf s hs k ↔ j = k := by
  constructor
  · intro h
    -- faceOf s hs k = s.erase (vertexEnum s hs k)
    simp only [faceOf, Finset.mem_erase, not_and_or, not_not] at h
    rcases h with h | h
    · -- vertexEnum s hs j = vertexEnum s hs k
      have hinj := D.card_eq s hs
      have hnd : (s.sort (· ≤ ·)).Nodup := s.sort_nodup (· ≤ ·)
      simp only [vertexEnum, List.get_eq_getElem] at h
      rw [List.nodup_iff_injective_get] at hnd
      have hcast_eq := hnd (show (s.sort (· ≤ ·)).get
        (j.cast (by rw [Finset.length_sort]; exact hinj.symm)) =
        (s.sort (· ≤ ·)).get
        (k.cast (by rw [Finset.length_sort]; exact hinj.symm)) from h)
      -- hcast_eq : Fin.cast _ j = Fin.cast _ k (as Fin L.length)
      -- Since Fin.cast preserves .val, j.val = k.val
      exact Fin.ext (by have := congr_arg Fin.val hcast_eq; simpa using this)
    · -- vertexEnum s hs j ∉ s, but this contradicts vertexEnum_mem
      exact absurd (D.vertexEnum_mem s hs j) h
  · intro h
    subst h
    exact Finset.notMem_erase _ _

/-- findOppositeIdx returns the unique index k such that
vertexEnum t ht k ∉ f. -/
lemma AbstractSimplicialData.findOppositeIdx_eq
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    D.findOppositeIdx s hs (D.faceOf s hs k)
      (D.faceOf_subset s hs k) (D.faceOf_card s hs k) = k := by
  -- findOppositeIdx picks some j with vertexEnum s hs j ∉ faceOf s hs k
  -- We show this j must equal k by uniqueness
  set j := D.findOppositeIdx s hs (D.faceOf s hs k)
    (D.faceOf_subset s hs k) (D.faceOf_card s hs k) with hj_def
  have hj_spec : D.vertexEnum s hs j ∉ D.faceOf s hs k :=
    D.vertexEnum_findOppositeIdx_not_mem s hs _ _ _
  exact (D.vertexEnum_not_mem_faceOf_iff s hs j k).mp hj_spec

end FaceHelpers

/-
## Adjacency Construction

We define adjacency for `AbstractSimplicialData.toTriangulation`
using the face helper library. For each cell `(s, hs)` and face
index `k`:
1. Compute face `f = D.faceOf s hs k`
2. Compute containers `cs = D.containersOf f`
3. If `cs.card = 1`: boundary face, return `none`
4. If `cs.card = 2`: find the other simplex `t != s` in `cs`,
   compute the opposite index in `t`, return `some (t, k')`
-/

/-- Construct a `Triangulation` from `AbstractSimplicialData`.
Uses `V : Type` (universe 0) to match `CellComplex.Cell : Type`.

The vertex map and vertex_injective are fully proved.
The adjacency map is defined using the face helper library.
adj_symm and adj_ne are fully proved. adj_vertex remains sorry'd. -/
noncomputable def AbstractSimplicialData.toTriangulation
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n) :
    Triangulation V n where
  Cell := { s : Finset V // s ∈ D.topSimplices }
  cellDecEq := inferInstance
  cellFintype := Finset.Subtype.fintype D.topSimplices
  vertex := fun ⟨s, hs⟩ k => D.vertexEnum s hs k
  vertex_injective := by
    intro ⟨s, hs⟩ i j hij
    have hnd : (s.sort (· ≤ ·)).Nodup := s.sort_nodup (· ≤ ·)
    set L := s.sort (· ≤ ·) with hL_def
    set i' : Fin L.length := i.cast (by rw [hL_def, Finset.length_sort]; exact (D.card_eq s hs).symm)
    set j' : Fin L.length := j.cast (by rw [hL_def, Finset.length_sort]; exact (D.card_eq s hs).symm)
    have hi'j' : L.get i' = L.get j' := hij
    have key : (i' : ℕ) = (j' : ℕ) := by
      rw [List.nodup_iff_injective_get] at hnd
      exact Fin.val_eq_of_eq (hnd hi'j')
    exact Fin.ext key
  adj := fun ⟨s, hs⟩ k =>
    let f := D.faceOf s hs k
    let cs := D.containersOf f
    if hc : cs.card ≤ 1 then
      -- Boundary face: only s contains f
      none
    else
      -- Interior face: exactly 2 containers (by pseudomanifold)
      -- Find the other simplex t != s in cs
      let cs_without_s := cs.erase s
      if ht_exists : cs_without_s.Nonempty then
        let t := ht_exists.choose
        have ht_mem_erase : t ∈ cs_without_s := ht_exists.choose_spec
        have ht_mem_cs : t ∈ cs := Finset.mem_of_mem_erase ht_mem_erase
        have ht_top : t ∈ D.topSimplices := (Finset.mem_filter.mp ht_mem_cs).1
        have hf_sub_t : f ⊆ t := (Finset.mem_filter.mp ht_mem_cs).2
        let k' := D.findOppositeIdx t ht_top f hf_sub_t (D.faceOf_card s hs k)
        some (⟨t, ht_top⟩, k')
      else
        -- Shouldn't happen if cs.card >= 2, but we handle gracefully
        none
  adj_symm := by
    intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj
    simp only at hadj
    -- Case split on dite branches in hadj (forward direction)
    split_ifs at hadj with hc ht_exists
    -- Main case: adj returned some (both dite conditions positive)
    · -- Extract data from hadj: s' = choose, k' = findOppositeIdx
      have ht_mem_erase := ht_exists.choose_spec
      have ht_mem_cs : ht_exists.choose ∈ D.containersOf (D.faceOf s hs k) :=
        Finset.mem_of_mem_erase ht_mem_erase
      have ht_top : ht_exists.choose ∈ D.topSimplices :=
        (Finset.mem_filter.mp ht_mem_cs).1
      have hf_sub_t : D.faceOf s hs k ⊆ ht_exists.choose :=
        (Finset.mem_filter.mp ht_mem_cs).2
      have h_pair := Option.some.inj hadj
      have h_s'_val : ht_exists.choose = s' :=
        congr_arg Subtype.val (congr_arg Prod.fst h_pair)
      have h_k'_eq : D.findOppositeIdx ht_exists.choose ht_top
        (D.faceOf s hs k) hf_sub_t (D.faceOf_card s hs k) = k' :=
        congr_arg Prod.snd h_pair
      -- Shared face: faceOf s' hs' k' = faceOf s hs k
      -- faceOf s' hs' k' = s'.erase (vertexEnum s' hs' k')
      -- Since s' = ht_exists.choose and k' = findOppositeIdx ...,
      -- by erase_opposite_eq this equals faceOf s hs k
      have hface_eq : D.faceOf s' hs' k' = D.faceOf s hs k := by
        -- faceOf s' hs' k' = s'.erase (vertexEnum s' hs' k') by def
        -- s' = ht_exists.choose (h_s'_val)
        -- k' = findOppositeIdx ht_exists.choose ... (h_k'_eq)
        -- erase_opposite_eq: t.erase (vertexEnum t ht (findOppositeIdx t ht f ...)) = f
        have h1 : D.faceOf s' hs' k' = D.faceOf ht_exists.choose ht_top
          (D.findOppositeIdx ht_exists.choose ht_top
            (D.faceOf s hs k) hf_sub_t (D.faceOf_card s hs k)) := by
          show s'.erase _ = ht_exists.choose.erase _
          congr 1
          · exact h_s'_val.symm
          · show D.vertexEnum s' hs' k' =
              D.vertexEnum ht_exists.choose ht_top
                (D.findOppositeIdx ht_exists.choose ht_top
                  (D.faceOf s hs k) hf_sub_t (D.faceOf_card s hs k))
            congr 1
            · exact h_s'_val.symm
            · exact h_k'_eq.symm
        rw [h1]
        -- Now: faceOf t ht_top (findOppositeIdx t ht_top f hf_sub_t _) = faceOf s hs k
        -- This is erase_opposite_eq applied to t with face = faceOf s hs k
        exact D.erase_opposite_eq ht_exists.choose ht_top
          (D.faceOf s hs k) hf_sub_t (D.faceOf_card s hs k)
      -- s ≠ s'
      have hne_ts : ht_exists.choose ≠ s := (Finset.mem_erase.mp ht_mem_erase).1
      have hs_ne_s' : s ≠ s' := by rw [← h_s'_val]; exact hne_ts.symm
      -- Containers are identical: containersOf (faceOf s' hs' k') = containersOf (faceOf s hs k)
      have hcs_eq : D.containersOf (D.faceOf s' hs' k') =
        D.containersOf (D.faceOf s hs k) := by
        exact congrArg D.containersOf hface_eq
      -- cs has at most 2 elements (pseudomanifold), at least 2 (from hc)
      have hcs_card : (D.containersOf (D.faceOf s hs k)).card = 2 := by
        have := D.containersOf_card_le_two s hs k; omega
      -- s' ∈ containers
      have hs'_in_cs : s' ∈ D.containersOf (D.faceOf s hs k) := by
        rw [← h_s'_val]; exact ht_mem_cs
      -- s ∈ containers
      have hs_in_cs : s ∈ D.containersOf (D.faceOf s hs k) :=
        D.self_mem_containersOf s hs k
      -- containers.erase s' = {s}
      have herase_s' : (D.containersOf (D.faceOf s hs k)).erase s' = {s} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨Finset.mem_erase.mpr ⟨hs_ne_s', hs_in_cs⟩,
           fun x hx => by
             have h_card1 : ((D.containersOf (D.faceOf s hs k)).erase s').card = 1 := by
               rw [Finset.card_erase_of_mem hs'_in_cs, hcs_card]
             obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_card1
             have : s = a := Finset.mem_singleton.mp (ha ▸ Finset.mem_erase.mpr ⟨hs_ne_s', hs_in_cs⟩)
             have : x = a := Finset.mem_singleton.mp (ha ▸ hx)
             rw [‹s = a›, ‹x = a›]⟩
      -- Now show adj ⟨s', hs'⟩ k' computes to some (⟨s, hs⟩, k)
      -- Navigate the dite branches in the goal
      simp only
      -- First dite: ¬ (containers of faceOf s' hs' k').card ≤ 1
      have hc' : ¬ (D.containersOf (D.faceOf s' hs' k')).card ≤ 1 := by
        simp only [hcs_eq, hcs_card]; omega
      rw [dif_neg hc']
      -- Second dite: (containers.erase s').Nonempty
      -- We construct the Nonempty proof carefully to control the choose value
      have hs_in_erase' : s ∈ (D.containersOf (D.faceOf s' hs' k')).erase s' := by
        simp only [hcs_eq]; exact Finset.mem_erase.mpr ⟨hs_ne_s', hs_in_cs⟩
      have hne' : ((D.containersOf (D.faceOf s' hs' k')).erase s').Nonempty :=
        ⟨s, hs_in_erase'⟩
      rw [dif_pos hne']
      -- Goal: some (⟨choose, _⟩, findOppositeIdx choose ...) = some (⟨s, hs⟩, k)
      -- Show choose = s: choose ∈ containers.erase s' = {s} (via hcs_eq)
      have hchoose_mem := hne'.choose_spec
      -- hne'.choose ∈ (D.containersOf (D.faceOf s' hs' k')).erase s'
      -- which equals (D.containersOf (D.faceOf s hs k)).erase s' = {s}
      -- But we can't rw hcs_eq in hchoose_mem (dependent type issue).
      -- Instead, derive hne'.choose = s from the singleton characterization.
      have hchoose_eq : hne'.choose = s := by
        -- We know (containers(face s' hs' k')).erase s' ⊆ containers(face s hs k).erase s'
        -- because containers are equal. So hne'.choose ∈ {s}.
        have : (D.containersOf (D.faceOf s' hs' k')).erase s' =
          (D.containersOf (D.faceOf s hs k)).erase s' :=
          congrArg (fun x => x.erase s') hcs_eq
        have h_mem : hne'.choose ∈ (D.containersOf (D.faceOf s hs k)).erase s' :=
          this ▸ hchoose_mem
        rw [herase_s'] at h_mem
        exact Finset.mem_singleton.mp h_mem
      -- Show the pair equality using congr
      congr 1
      refine Prod.ext (Subtype.ext hchoose_eq) ?_
      -- Goal: findOppositeIdx choose _ (faceOf s' hs' k') _ _ = k
      -- Derive facts about choose using explicit membership
      have hchoose_mem_cs : hne'.choose ∈ D.containersOf (D.faceOf s' hs' k') :=
        Finset.mem_of_mem_erase hchoose_mem
      have ht_top' : hne'.choose ∈ D.topSimplices :=
        (Finset.mem_filter.mp hchoose_mem_cs).1
      have hf_sub' : D.faceOf s' hs' k' ⊆ hne'.choose :=
        (Finset.mem_filter.mp hchoose_mem_cs).2
      -- The findOppositeIdx spec: vertexEnum choose _ j ∉ faceOf s' hs' k'
      have hj_spec := D.vertexEnum_findOppositeIdx_not_mem
        hne'.choose ht_top' (D.faceOf s' hs' k') hf_sub' (D.faceOf_card s' hs' k')
      -- Since choose = s, vertexEnum choose _ = vertexEnum s _
      -- and faceOf s' hs' k' = faceOf s hs k
      -- We can use the iff characterization after transporting
      -- vertexEnum (choose) ht_top' j ∉ faceOf s' hs' k'
      -- ↔ vertexEnum s hs j ∉ faceOf s hs k (because choose = s, faces equal)
      -- ↔ j = k (by vertexEnum_not_mem_faceOf_iff)
      suffices h : D.vertexEnum s hs _ ∉ D.faceOf s hs k by
        exact (D.vertexEnum_not_mem_faceOf_iff s hs _ k).mp h
      -- Transport: vertexEnum choose _ j → vertexEnum s _ j and face → face
      -- hj_spec : vertexEnum choose _ (FOI ...) ∉ faceOf s' hs' k'
      -- Goal: vertexEnum s hs (FOI ...) ∉ faceOf s hs k
      --
      -- The vertex and face both match up to choose=s and hface_eq.
      -- We use the characterization: v ∉ A ↔ v ∉ A
      -- after showing the vertex value and face are the same.
      --
      -- vertexEnum choose ht_top' j ∈ choose = s (by vertexEnum_mem + hchoose_eq)
      -- vertexEnum s hs j ∈ s (by vertexEnum_mem)
      -- Both are the j-th element of s.sort (· ≤ ·) (since choose = s)
      -- So they're the same vertex value.
      --
      -- Instead of fighting dependent types, use the fact that both
      -- vertexEnum applications produce elements of the same underlying set.
      -- Use the iff form: not_mem ↔ j = k from vertexEnum_not_mem_faceOf_iff
      -- applied to choose (= s).
      --
      -- Approach: show directly that the FOI result equals k using
      -- the spec from the OTHER direction (via hj_spec and membership).
      -- hj_spec says vertexEnum choose ht_top' (FOI ...) ∉ faceOf s' hs' k'
      -- faceOf s' hs' k' = faceOf s hs k = s.erase (vertexEnum s hs k)
      -- vertexEnum choose ht_top' (FOI ...) ∈ choose = s (by vertexEnum_mem)
      -- So vertexEnum choose ht_top' (FOI ...) ∈ s but ∉ s.erase (vertexEnum s hs k)
      -- This means vertexEnum choose ht_top' (FOI ...) = vertexEnum s hs k
      -- (it's in s but not in s.erase(v), so it must be v)
      --
      -- And vertexEnum s hs (FOI ...) = vertexEnum choose ht_top' (FOI ...)
      -- (since choose = s, the j-th sorted element is the same)
      --
      -- So vertexEnum s hs (FOI ...) = vertexEnum s hs k
      -- hence vertexEnum s hs (FOI ...) ∉ s.erase (vertexEnum s hs k) = faceOf s hs k
      --
      -- Actually the simplest path: use that vertexEnum s hs (FOI ...) ∉ faceOf s hs k
      -- iff FOI ... = k (by vertexEnum_not_mem_faceOf_iff).
      -- And vertexEnum choose ht_top' (FOI ...) ∉ faceOf s' hs' k'
      -- means vertexEnum choose ht_top' (FOI ...) ∉ faceOf s hs k (by hface_eq)
      -- means the vertex is not in s.erase(vertexEnum s hs k)
      -- means the vertex = vertexEnum s hs k (since it's in s)
      --
      -- Let v := vertexEnum choose ht_top' (FOI ...)
      -- v ∈ choose = s (by vertexEnum_mem + hchoose_eq)
      -- v ∉ faceOf s hs k = s.erase (vertexEnum s hs k)
      -- So v = vertexEnum s hs k
      -- Also v = vertexEnum s hs (FOI ...) (since choose = s)
      -- ... this is circular. Let me just directly prove the result.
      --
      -- Cleaner approach: show FOI = k directly
      -- We already have hj_spec: vertexEnum choose ht_top' (FOI ...) ∉ faceOf s' hs' k'
      -- = ∉ faceOf s hs k (by hface_eq)
      -- vertexEnum choose ht_top' (FOI ...) ∈ s (since ∈ choose = s)
      -- So vertexEnum choose ht_top' (FOI ...) ∉ s.erase(vertexEnum s hs k)
      -- But is in s. So it equals vertexEnum s hs k.
      -- Since vertexEnum s hs is injective: the only j with vertexEnum s hs j = vertexEnum s hs k is j = k.
      -- But vertexEnum choose ht_top' (FOI...) = vertexEnum s hs (FOI ...) (since choose = s)...
      -- We're going in circles. The fundamental issue is showing vertexEnum choose = vertexEnum s.
      --
      -- Let me just use Eq.mpr with hchoose_eq for the dependent transport.
      have key : D.vertexEnum hne'.choose ht_top'
        (D.findOppositeIdx hne'.choose ht_top' (D.faceOf s' hs' k') hf_sub'
          (D.faceOf_card s' hs' k'))
        ∉ D.faceOf s hs k := by
        rwa [← hface_eq]
      -- key says: the SAME vertex value (from vertexEnum choose _) is ∉ faceOf s hs k
      -- We need: vertexEnum s hs (FOI ...) ∉ faceOf s hs k
      -- These are the same vertex because choose = s.
      -- vertexEnum is defined as (t.sort ...).get(j.cast ...)
      -- When t = choose = s, the sorted list is the same.
      -- So the vertex value is the same, just with different proof terms.
      -- faceOf s hs k is a concrete Finset, so membership is decidable
      -- and depends only on the vertex value, not proof terms.
      -- Therefore if v ∉ faceOf s hs k (key), and v' = v, then v' ∉ faceOf s hs k.
      suffices heq_v : D.vertexEnum s hs
        (D.findOppositeIdx hne'.choose ht_top' (D.faceOf s' hs' k') hf_sub'
          (D.faceOf_card s' hs' k'))
        = D.vertexEnum hne'.choose ht_top'
        (D.findOppositeIdx hne'.choose ht_top' (D.faceOf s' hs' k') hf_sub'
          (D.faceOf_card s' hs' k')) by
        rw [heq_v]; exact key
      -- Now prove heq_v: vertexEnum s hs j = vertexEnum choose ht_top' j
      -- Both compute (t.sort ...).get(j.cast(...))
      -- where t is s (resp. choose = s), and the cast proofs differ.
      -- Since choose = s propositionally, the sorted lists are the same list.
      -- The indices are the same nat value.
      -- So the getElem calls return the same value.
      -- vertexEnum s hs j and vertexEnum choose ht_top' j both compute
      -- (t.sort ...).get (j.cast ...) where t = s = choose.
      -- Since choose = s, the sorted lists are identical and the indices
      -- have the same .val, so the getElem results are the same.
      simp only [AbstractSimplicialData.vertexEnum, List.get_eq_getElem]
      -- Goal: L[i] = L'[i'] where L = s.sort ..., L' = choose.sort ...,
      -- i and i' are cast versions of the same FOI result.
      -- Since choose = s, L = L' and i.val = i'.val.
      have hsort : (s.sort (· ≤ ·)) = (hne'.choose.sort (· ≤ ·)) :=
        congrArg (fun x => x.sort (· ≤ ·)) hchoose_eq.symm
      simp [hsort]
    -- The none cases are closed automatically by split_ifs
  adj_vertex := by intro _ _ _ _ _; sorry
  adj_ne := by
    intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj
    simp only at hadj
    split_ifs at hadj with hc ht_exists
    -- Case: adj returned some -- ht_exists gives t ∈ cs.erase s
    · have ht_mem_erase := ht_exists.choose_spec
      have ht_ne_s : ht_exists.choose ≠ s := (Finset.mem_erase.mp ht_mem_erase).1
      -- Extract: ht_exists.choose = s' from the injection chain
      have h_pair := Option.some.inj hadj
      have h_fst := congr_arg Prod.fst h_pair
      -- h_fst : ⟨ht_exists.choose, _⟩ = ⟨s', hs'⟩
      have h_val : ht_exists.choose = s' := congr_arg Subtype.val h_fst
      intro heq
      have hs_eq : s = s' := congr_arg Subtype.val heq
      exact ht_ne_s (h_val ▸ hs_eq |>.symm)
    -- The none cases are closed automatically by split_ifs
    -- (none = some (...) is contradictory)

/-! ## Example: 1-Dimensional Interval Triangulation

A subdivision of an interval into m segments, with all
`CellComplex` axioms fully proved (no sorries).

Vertices are natural numbers {0, 1, ..., m}. Cell i (for
i : Fin m) is the edge [i, i+1] with:
  vertex 0 = i
  vertex 1 = i + 1

Adjacency:
- Face opposite vertex 0 of cell i = {i+1}
  = face opposite vertex 1 of cell (i+1)
  So adj i 0 = some (i+1, 1) when i+1 < m
- Face opposite vertex 1 of cell i = {i}
  = face opposite vertex 0 of cell (i-1)
  So adj i 1 = some (i-1, 0) when 0 < i
-/

section Interval

variable {m : ℕ}

/-- Vertex map for the interval triangulation. -/
private def ivtx (_ : 0 < m) (i : Fin m) (k : Fin 2) : ℕ :=
  if k.val = 0 then i.val else i.val + 1

/-- Adjacency for the interval triangulation. Defined as an
opaque `if/dite` chain. -/
private def iadj (m : ℕ) (i : Fin m)
    (k : Fin 2) : Option (Fin m × Fin 2) :=
  if hk : k.val = 0 then
    if h : i.val + 1 < m then
      some (⟨i.val + 1, h⟩, ⟨1, by omega⟩)
    else
      none
  else
    if h : 0 < i.val then
      some (⟨i.val - 1, by omega⟩, ⟨0, by omega⟩)
    else
      none

/-- Extract data from iadj = some. -/
private lemma iadj_cases {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    (k.val = 0 ∧ s'.val = s.val + 1 ∧ k'.val = 1 ∧
      s.val + 1 < m) ∨
    (k.val ≠ 0 ∧ s'.val = s.val - 1 ∧ k'.val = 0 ∧
      0 < s.val) := by
  unfold iadj at hadj
  by_cases hk : k.val = 0
  · -- k.val = 0
    rw [dif_pos hk] at hadj
    by_cases h : s.val + 1 < m
    · rw [dif_pos h] at hadj
      left
      simp only [Option.some.injEq, Prod.mk.injEq] at hadj
      obtain ⟨hs'_eq, hk'_eq⟩ := hadj
      exact ⟨hk,
        by have := congr_arg Fin.val hs'_eq; simp at this; omega,
        by have := congr_arg Fin.val hk'_eq; simp at this; omega,
        h⟩
    · rw [dif_neg h] at hadj; simp at hadj
  · -- k.val ≠ 0
    rw [dif_neg hk] at hadj
    by_cases h : (0 : ℕ) < s.val
    · rw [dif_pos h] at hadj
      right
      simp only [Option.some.injEq, Prod.mk.injEq] at hadj
      obtain ⟨hs'_eq, hk'_eq⟩ := hadj
      exact ⟨hk,
        by have := congr_arg Fin.val hs'_eq; simp at this; omega,
        by have := congr_arg Fin.val hk'_eq; simp at this; omega,
        h⟩
    · rw [dif_neg h] at hadj; simp at hadj

private lemma iadj_symm' {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    iadj m s' k' = some (s, k) := by
  obtain (⟨hk, hs', hk', hlt⟩ | ⟨hk, hs', hk', hpos⟩) :=
    iadj_cases hadj
  · -- k.val=0, s'=s+1, k'.val=1: need iadj m s' k' = some (s, k)
    -- i.e. iadj m ⟨s.val+1,_⟩ ⟨1,_⟩ = some (s, ⟨0,_⟩)
    -- which reduces to: 0 < s'.val → some (⟨s'.val-1,_⟩, ⟨0,_⟩)
    show iadj m s' k' = some (s, k)
    unfold iadj
    have : ¬(k'.val = 0) := by omega
    rw [dif_neg this]
    have : (0 : ℕ) < s'.val := by omega
    rw [dif_pos this]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩
  · -- k.val≠0, s'=s-1, k'.val=0: need iadj m s' k' = some (s, k)
    show iadj m s' k' = some (s, k)
    unfold iadj
    have : k'.val = 0 := by omega
    rw [dif_pos this]
    have : s'.val + 1 < m := by omega
    rw [dif_pos this]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨Fin.ext (by simp; omega), Fin.ext (by simp; omega)⟩

private lemma iadj_ne' {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    s ≠ s' := by
  obtain (⟨_, hs', _, _⟩ | ⟨_, hs', _, _⟩) := iadj_cases hadj
  · intro heq; have := congr_arg Fin.val heq; omega
  · intro heq; have := congr_arg Fin.val heq; omega

private lemma iadj_vertex' {hm : 0 < m} {s s' : Fin m}
    {k k' : Fin 2}
    (hadj : iadj m s k = some (s', k')) :
    (univ.erase k).image (ivtx hm s) =
    (univ.erase k').image (ivtx hm s') := by
  obtain (⟨hk, hs', hk', _⟩ | ⟨hk, hs', hk', _⟩) :=
    iadj_cases hadj
  · -- k.val=0, s'=s+1, k'.val=1
    have hkeq : k = ⟨0, by omega⟩ := Fin.ext hk
    have hk'eq : k' = ⟨1, by omega⟩ := Fin.ext hk'
    rw [hkeq, hk'eq]
    ext v; constructor
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha1 : a.val = 1 := by have := a.isLt; omega
      refine ⟨⟨0, by omega⟩,
        mem_erase.mpr ⟨by intro h; simp at h, mem_univ _⟩, ?_⟩
      rw [show a = ⟨1, by omega⟩ from Fin.ext ha1] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha0 : a.val = 0 := by have := a.isLt; omega
      refine ⟨⟨1, by omega⟩,
        mem_erase.mpr ⟨by intro h; simp at h, mem_univ _⟩, ?_⟩
      rw [show a = ⟨0, by omega⟩ from Fin.ext ha0] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega
  · -- k.val≠0 (so k.val=1), s'=s-1, k'.val=0
    have hk1 : k.val = 1 := by have := k.isLt; omega
    have hkeq : k = ⟨1, by omega⟩ := Fin.ext hk1
    have hk'eq : k' = ⟨0, by omega⟩ := Fin.ext hk'
    rw [hkeq, hk'eq]
    ext v; constructor
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha0 : a.val = 0 := by have := a.isLt; omega
      refine ⟨⟨1, by omega⟩,
        mem_erase.mpr ⟨by intro h; simp at h, mem_univ _⟩, ?_⟩
      rw [show a = ⟨0, by omega⟩ from Fin.ext ha0] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega
    · intro hv
      rw [mem_image] at hv ⊢
      obtain ⟨a, ha_mem, ha_eq⟩ := hv
      rw [mem_erase] at ha_mem
      have ha1 : a.val = 1 := by have := a.isLt; omega
      refine ⟨⟨0, by omega⟩,
        mem_erase.mpr ⟨by intro h; simp at h, mem_univ _⟩, ?_⟩
      rw [show a = ⟨1, by omega⟩ from Fin.ext ha1] at ha_eq
      simp [ivtx] at ha_eq ⊢; omega

/-- A subdivision of [0,m] into m unit intervals, as a
`Triangulation Nat 1`. All axioms fully proved. -/
def intervalTriangulation (m : ℕ) (hm : 0 < m) :
    Triangulation ℕ 1 where
  Cell := Fin m
  cellDecEq := inferInstance
  cellFintype := inferInstance
  vertex := ivtx hm
  vertex_injective := by
    intro i a b hab
    simp only [ivtx] at hab
    fin_cases a <;> fin_cases b <;> simp_all
  adj := iadj m
  adj_symm := fun s k s' k' hadj => iadj_symm' hadj
  adj_vertex := fun s k s' k' hadj => iadj_vertex' hadj
  adj_ne := fun s k s' k' hadj => iadj_ne' hadj

end Interval

/-! ## Interval Sperner's Lemma

As a sanity check, we state the 1-d Sperner theorem for the
interval triangulation and prove it via the abstract theorem. -/

/-- 1-d Sperner's lemma for intervals: if the boundary doors
are odd, a panchromatic cell exists. -/
theorem interval_sperner (m : ℕ) (hm : 0 < m)
    (c : ℕ → Fin 2)
    (hbdry : Odd (Finset.univ.filter
      (fun p : Fin m × Fin 2 =>
        CellComplex.IsDoor c
          (intervalTriangulation m hm).toCellComplex p.1 p.2 ∧
        (intervalTriangulation m hm).adj p.1 p.2 = none)).card) :
    ∃ s : Fin m,
      CellComplex.IsPanchromatic c
        (intervalTriangulation m hm).toCellComplex s :=
  Triangulation.sperner (intervalTriangulation m hm) c hbdry

end Triangulation

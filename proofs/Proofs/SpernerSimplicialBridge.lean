/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerMathlib

/-
# Bridge from Geometry.SimplicialComplex to Sperner's Lemma

Given a simplicial complex that is pure (all facets have the same
cardinality d+1) and satisfies a pseudomanifold condition (each
codimension-1 face lies in at most 2 facets), we instantiate the
abstract `Sperner.exists_panchromatic` theorem from
`SpernerMathlib.lean`.

The approach uses hypotheses directly (matching `SpernerMathlib.lean`
style) rather than intermediate structures. The key construction:

1. *Cells* are subtypes `{ s // s in topCells }` where `topCells`
   is a `Finset (Finset E)` of facets with cardinality `d+1`.

2. *Vertex ordering* uses `Finset.sort` with a `LinearOrder E` to
   convert unordered vertex sets into ordered tuples.

3. *Adjacency* is defined via shared codimension-1 faces: for cell
   `s` at face position `k`, erase the k-th sorted vertex and look
   for another cell containing that face.

4. The three adjacency axioms (`adj_symm`, `adj_vertex`, `adj_ne`)
   follow from the pseudomanifold property and properties of sorted
   lists.

## Main results

* `Sperner.SimplicialComplex.exists_panchromatic`: Sperner's lemma
  for pure pseudomanifold simplicial complexes.

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]

## Tags

Sperner, simplicial complex, pseudomanifold, bridge
-/

set_option maxHeartbeats 800000

namespace Sperner.SimplicialComplex

open Finset

/-! ## Core Definitions

We define vertex enumeration, codimension-1 faces, containers,
and adjacency for a finite set of top-dimensional simplices. -/

section Definitions

variable {E : Type} [DecidableEq E] [LinearOrder E] {d : Nat}

/-- The ordered vertex enumeration of a simplex `s` with `d+1` vertices.
Uses `Finset.sort` with the linear order on `E`. -/
noncomputable def vertexEnum
    (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) : E :=
  (s.sort (. <= .)).get (k.cast (by rw [Finset.length_sort]; exact hs.symm))

omit [DecidableEq E] in
/-- The k-th vertex belongs to the simplex. -/
lemma vertexEnum_mem
    (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) :
    vertexEnum s hs k ∈ s := by
  unfold vertexEnum
  have hmem := List.get_mem (s.sort (. <= .))
    (k.cast (by rw [Finset.length_sort]; exact hs.symm))
  exact (s.mem_sort (. <= .)).mp hmem

omit [DecidableEq E] in
/-- The vertex enumeration is injective (vertices are distinct). -/
lemma vertexEnum_injective
    (s : Finset E) (hs : s.card = d + 1) :
    Function.Injective (vertexEnum s hs) := by
  intro i j hij
  have hnd : (s.sort (. <= .)).Nodup := s.sort_nodup (. <= .)
  set L := s.sort (. <= .) with hL_def
  set i' : Fin L.length := i.cast
    (by rw [hL_def, Finset.length_sort]; exact hs.symm)
  set j' : Fin L.length := j.cast
    (by rw [hL_def, Finset.length_sort]; exact hs.symm)
  have hi'j' : L.get i' = L.get j' := hij
  have key : (i' : Nat) = (j' : Nat) := by
    rw [List.nodup_iff_injective_get] at hnd
    exact Fin.val_eq_of_eq (hnd hi'j')
  exact Fin.ext key

/-- The vertex enumeration surjects onto `s`: every element of `s`
is some `vertexEnum s hs k`. -/
lemma vertexEnum_image_univ
    (s : Finset E) (hs : s.card = d + 1) :
    Finset.univ.image (vertexEnum s hs) = s := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  . rintro ⟨k, rfl⟩; exact vertexEnum_mem s hs k
  . intro hv
    have hv_sort : v ∈ s.sort (. <= .) := (s.mem_sort (. <= .)).mpr hv
    rw [List.mem_iff_getElem] at hv_sort
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
    have hidx_lt' : idx < d + 1 := by
      rwa [Finset.length_sort, hs] at hidx_lt
    exact ⟨⟨idx, hidx_lt'⟩, by simp [vertexEnum, List.get_eq_getElem, hidx_eq]⟩

/-- The codimension-1 face obtained by deleting the k-th vertex. -/
noncomputable def faceOf
    (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) : Finset E :=
  s.erase (vertexEnum s hs k)

/-- A codimension-1 face has `d` elements. -/
lemma faceOf_card
    (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) :
    (faceOf s hs k).card = d := by
  simp only [faceOf]
  rw [Finset.card_erase_of_mem (vertexEnum_mem s hs k)]
  omega

/-- A codimension-1 face is a subset of the simplex. -/
lemma faceOf_subset
    (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) :
    faceOf s hs k ⊆ s :=
  Finset.erase_subset _ _

/-- Image of `univ.erase k` under vertexEnum equals faceOf. -/
lemma vertexEnum_image_erase
    (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) :
    (Finset.univ.erase k).image (vertexEnum s hs) = faceOf s hs k := by
  have hinj := vertexEnum_injective s hs
  ext v
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true,
             faceOf, Finset.mem_erase]
  constructor
  . rintro ⟨j, hj_ne, rfl⟩
    exact ⟨fun h => hj_ne (hinj h), vertexEnum_mem s hs j⟩
  . rintro ⟨hne, hv⟩
    have hv_sort : v ∈ s.sort (. <= .) := (s.mem_sort (. <= .)).mpr hv
    rw [List.mem_iff_getElem] at hv_sort
    obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
    have hidx_lt' : idx < d + 1 := by
      rwa [Finset.length_sort, hs] at hidx_lt
    refine ⟨⟨idx, hidx_lt'⟩, ?_, ?_⟩
    . intro heq
      apply hne
      have : vertexEnum s hs ⟨idx, hidx_lt'⟩ = v := by
        simp [vertexEnum, List.get_eq_getElem, hidx_eq]
      rw [← this, heq]
    . simp [vertexEnum, List.get_eq_getElem, hidx_eq]

/-- Vertex j is not in face k iff j = k. -/
lemma vertexEnum_not_mem_faceOf_iff
    (s : Finset E) (hs : s.card = d + 1) (j k : Fin (d + 1)) :
    vertexEnum s hs j ∉ faceOf s hs k ↔ j = k := by
  simp only [faceOf, Finset.mem_erase, not_and_or, not_not]
  constructor
  . intro h
    cases h with
    | inl h => exact vertexEnum_injective s hs h
    | inr h => exact absurd (vertexEnum_mem s hs j) h
  . intro h; left; congr 1

/-- Top simplices containing a given face. -/
noncomputable def containersOf
    (topCells : Finset (Finset E))
    (f : Finset E) : Finset (Finset E) :=
  topCells.filter (fun t => f ⊆ t)

/-- The original simplex contains its own face. -/
lemma self_mem_containersOf
    (topCells : Finset (Finset E))
    (s : Finset E) (hs : s ∈ topCells) (hscard : s.card = d + 1)
    (k : Fin (d + 1)) :
    s ∈ containersOf topCells (faceOf s hscard k) := by
  simp only [containersOf, Finset.mem_filter]
  exact ⟨hs, faceOf_subset s hscard k⟩

omit [LinearOrder E] in
/-- The difference `t \ f` is nonempty when `t` has `d+1` elements
and `f` has `d` elements with `f ⊆ t`. -/
lemma sdiff_nonempty_of_card
    (t : Finset E) (htcard : t.card = d + 1)
    (f : Finset E) (_hf : f ⊆ t) (hfc : f.card = d) :
    (t \ f).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have hsub := Finset.sdiff_eq_empty_iff_subset.mp h
  have := Finset.card_le_card hsub
  omega

/-- Given a top simplex `t` containing face `f`, find the index
in `t`'s sorted vertex list of the unique vertex in `t \ f`. -/
noncomputable def findOppositeIdx
    (t : Finset E) (htcard : t.card = d + 1)
    (f : Finset E) (_hf : f ⊆ t) (hfc : f.card = d) :
    Fin (d + 1) :=
  have hex : ∃ k : Fin (d + 1), vertexEnum t htcard k ∉ f := by
    by_contra hall
    push_neg at hall
    have hsub : t ⊆ f := by
      intro v hv
      have hv_sort : v ∈ t.sort (. <= .) := (t.mem_sort (. <= .)).mpr hv
      rw [List.mem_iff_getElem] at hv_sort
      obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
      have hidx_lt' : idx < d + 1 := by
        rwa [Finset.length_sort, htcard] at hidx_lt
      have hmem := hall ⟨idx, hidx_lt'⟩
      have heq : vertexEnum t htcard ⟨idx, hidx_lt'⟩ = v := by
        simp only [vertexEnum, List.get_eq_getElem]
        exact hidx_eq
      rwa [heq] at hmem
    have := Finset.card_le_card hsub
    omega
  hex.choose

/-- The opposite vertex is not in the face. -/
lemma vertexEnum_findOppositeIdx_not_mem
    (t : Finset E) (htcard : t.card = d + 1)
    (f : Finset E) (hf : f ⊆ t) (hfc : f.card = d) :
    vertexEnum t htcard (findOppositeIdx t htcard f hf hfc) ∉ f := by
  unfold findOppositeIdx
  generalize_proofs hex
  exact hex.choose_spec

/-- Erasing the opposite vertex from t gives back f. -/
lemma erase_opposite_eq
    (t : Finset E) (htcard : t.card = d + 1)
    (f : Finset E) (hf : f ⊆ t) (hfc : f.card = d) :
    t.erase (vertexEnum t htcard (findOppositeIdx t htcard f hf hfc)) = f := by
  set v := vertexEnum t htcard (findOppositeIdx t htcard f hf hfc) with hv_def
  have hv_not_f : v ∉ f := vertexEnum_findOppositeIdx_not_mem t htcard f hf hfc
  have hv_mem_t : v ∈ t := vertexEnum_mem t htcard (findOppositeIdx t htcard f hf hfc)
  have h_sub : f ⊆ t.erase v := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => hv_not_f (h ▸ hx), hf hx⟩
  have h_card : (t.erase v).card ≤ f.card := by
    rw [Finset.card_erase_of_mem hv_mem_t, htcard, hfc]
    omega
  exact (Finset.eq_of_subset_of_card_le h_sub h_card).symm

/-- findOppositeIdx of the face obtained by removing vertex k gives back k. -/
lemma findOppositeIdx_eq
    (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) :
    findOppositeIdx s hs (faceOf s hs k) (faceOf_subset s hs k)
      (faceOf_card s hs k) = k := by
  set idx := findOppositeIdx s hs (faceOf s hs k) (faceOf_subset s hs k)
    (faceOf_card s hs k)
  have h_not_mem : vertexEnum s hs idx ∉ faceOf s hs k :=
    vertexEnum_findOppositeIdx_not_mem s hs (faceOf s hs k) (faceOf_subset s hs k)
      (faceOf_card s hs k)
  exact (vertexEnum_not_mem_faceOf_iff s hs idx k).mp h_not_mem

end Definitions

/-! ## Adjacency Construction

For a finite set of top cells satisfying the pseudomanifold condition,
we construct an adjacency function compatible with
`Sperner.exists_panchromatic`. -/

section Adjacency

variable {E : Type} [DecidableEq E] [LinearOrder E] {d : Nat}

/-- The adjacency function for top cells. For cell `s` at face `k`:
1. Compute the codim-1 face `f = faceOf s hs k`
2. Find containers of `f` among topCells
3. If only 1 container (boundary), return `none`
4. If 2 containers (interior), return the other cell with its opposite index -/
noncomputable def adjFn
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (p : { s : Finset E // s ∈ topCells })
    (k : Fin (d + 1)) :
    Option ({ s : Finset E // s ∈ topCells } × Fin (d + 1)) :=
  let f := faceOf p.1 (hcard p.1 p.2) k
  let cs := containersOf topCells f
  if _hc : cs.card ≤ 1 then
    none
  else
    let cs_without_s := cs.erase p.1
    if ht_exists : cs_without_s.Nonempty then
      let t := ht_exists.choose
      have ht_mem_erase : t ∈ cs_without_s := ht_exists.choose_spec
      have ht_mem_cs : t ∈ cs := Finset.mem_of_mem_erase ht_mem_erase
      have ht_top : t ∈ topCells := (Finset.mem_filter.mp ht_mem_cs).1
      have hf_sub_t : f ⊆ t := (Finset.mem_filter.mp ht_mem_cs).2
      let k' := findOppositeIdx t (hcard t ht_top) f hf_sub_t
        (faceOf_card p.1 (hcard p.1 p.2) k)
      some (⟨t, ht_top⟩, k')
    else
      none

/-! ### Adjacency axiom proofs -/

/-- Container count is at most 2 (pseudomanifold). -/
lemma containersOf_card_le_two
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (s : Finset E) (hs : s ∈ topCells) (k : Fin (d + 1)) :
    (containersOf topCells (faceOf s (hcard s hs) k)).card ≤ 2 :=
  hpseudo _ (faceOf_card s (hcard s hs) k)

/-- Container count is 1 or 2. -/
lemma containersOf_card_one_or_two
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (s : Finset E) (hs : s ∈ topCells) (k : Fin (d + 1)) :
    (containersOf topCells (faceOf s (hcard s hs) k)).card = 1 ∨
    (containersOf topCells (faceOf s (hcard s hs) k)).card = 2 := by
  have h1 : 0 < (containersOf topCells (faceOf s (hcard s hs) k)).card :=
    Finset.card_pos.mpr ⟨s, self_mem_containersOf topCells s hs (hcard s hs) k⟩
  have h2 := containersOf_card_le_two topCells hcard hpseudo s hs k
  omega

/-- When `adjFn` returns `some`, the containers have exactly 2 elements. -/
lemma containersOf_card_eq_two_of_adjFn
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (s : Finset E) (hs : s ∈ topCells)
    (k : Fin (d + 1))
    (s' : Finset E) (hs' : s' ∈ topCells)
    (k' : Fin (d + 1))
    (hadj : adjFn topCells hcard ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    (containersOf topCells (faceOf s (hcard s hs) k)).card = 2 := by
  unfold adjFn at hadj
  simp only at hadj
  split_ifs at hadj with hc hne
  . have hco := containersOf_card_one_or_two topCells hcard hpseudo s hs k
    omega


/-- When `adjFn` returns `some`, the shared face sets are equal. -/
lemma adjFn_vertex
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (s : Finset E) (hs : s ∈ topCells)
    (k : Fin (d + 1))
    (s' : Finset E) (hs' : s' ∈ topCells)
    (k' : Fin (d + 1))
    (hadj : adjFn topCells hcard ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    (Finset.univ.erase k).image (vertexEnum s (hcard s hs)) =
    (Finset.univ.erase k').image (vertexEnum s' (hcard s' hs')) := by
  unfold adjFn at hadj
  simp only at hadj
  split_ifs at hadj with hc hne
  . simp only [Option.some.injEq, Prod.mk.injEq] at hadj
    obtain ⟨hs'_sub_eq, hk'_eq⟩ := hadj
    have hs'_val : s' = hne.choose := (Subtype.ext_iff.mp hs'_sub_eq).symm
    set f := faceOf s (hcard s hs) k
    have hLHS : (Finset.univ.erase k).image (vertexEnum s (hcard s hs)) = f :=
      vertexEnum_image_erase s (hcard s hs) k
    have ht_mem_erase := hne.choose_spec
    have ht_mem_cs : hne.choose ∈ containersOf topCells f :=
      Finset.mem_of_mem_erase ht_mem_erase
    have ht_top : hne.choose ∈ topCells :=
      (Finset.mem_filter.mp ht_mem_cs).1
    have hf_sub_t : f ⊆ hne.choose :=
      (Finset.mem_filter.mp ht_mem_cs).2
    have hRHS : (Finset.univ.erase k').image (vertexEnum s' (hcard s' hs')) = f := by
      rw [vertexEnum_image_erase s' (hcard s' hs') k']
      simp only [faceOf]
      subst hs'_val
      rw [← hk'_eq]
      exact erase_opposite_eq hne.choose (hcard hne.choose ht_top) f hf_sub_t
        (faceOf_card s (hcard s hs) k)
    rw [hLHS, hRHS]


/-- When `adjFn` returns `some`, `s' != s` (as `Finset` values). -/
lemma adjFn_ne
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (s : Finset E) (hs : s ∈ topCells)
    (k : Fin (d + 1))
    (s' : Finset E) (hs' : s' ∈ topCells)
    (k' : Fin (d + 1))
    (hadj : adjFn topCells hcard ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    s' ≠ s := by
  unfold adjFn at hadj
  simp only at hadj
  split_ifs at hadj with hc hne
  . simp only [Option.some.injEq, Prod.mk.injEq] at hadj
    obtain ⟨hs'_sub_eq, _⟩ := hadj
    have hs'_val : s' = hne.choose := (Subtype.ext_iff.mp hs'_sub_eq).symm
    have ht_mem_erase := hne.choose_spec
    have ht_ne_s : hne.choose ≠ s := (Finset.mem_erase.mp ht_mem_erase).1
    rw [hs'_val]
    exact ht_ne_s


/-- When `adjFn` returns `some`, `s'` is in the containers of the face. -/
lemma adjFn_s'_mem_containers
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (s : Finset E) (hs : s ∈ topCells)
    (k : Fin (d + 1))
    (s' : Finset E) (hs' : s' ∈ topCells)
    (k' : Fin (d + 1))
    (hadj : adjFn topCells hcard ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    s' ∈ containersOf topCells (faceOf s (hcard s hs) k) := by
  simp only [containersOf, Finset.mem_filter]
  refine ⟨hs', ?_⟩
  unfold adjFn at hadj
  simp only at hadj
  split_ifs at hadj with hc hne
  . simp only [Option.some.injEq, Prod.mk.injEq] at hadj
    obtain ⟨hs'_sub_eq, _⟩ := hadj
    have hs'_val : s' = hne.choose := (Subtype.ext_iff.mp hs'_sub_eq).symm
    have ht_mem_erase := hne.choose_spec
    have ht_mem_cs : hne.choose ∈ containersOf topCells (faceOf s (hcard s hs) k) :=
      Finset.mem_of_mem_erase ht_mem_erase
    rw [hs'_val]
    exact (Finset.mem_filter.mp ht_mem_cs).2


/-- When `adjFn` returns `some`, `faceOf s' hs' k' = faceOf s hs k`. -/
lemma adjFn_face_eq
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (s : Finset E) (hs : s ∈ topCells)
    (k : Fin (d + 1))
    (s' : Finset E) (hs' : s' ∈ topCells)
    (k' : Fin (d + 1))
    (hadj : adjFn topCells hcard ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    faceOf s' (hcard s' hs') k' = faceOf s (hcard s hs) k := by
  have himg := adjFn_vertex topCells hcard s hs k s' hs' k' hadj
  rw [vertexEnum_image_erase s (hcard s hs) k,
      vertexEnum_image_erase s' (hcard s' hs') k'] at himg
  exact himg.symm

/-- Adjacency is symmetric: if `adjFn` maps `(s, k)` to `(s', k')`,
then it maps `(s', k')` back to `(s, k)`. -/
lemma adjFn_symm
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (s : Finset E) (hs : s ∈ topCells)
    (k : Fin (d + 1))
    (s' : Finset E) (hs' : s' ∈ topCells)
    (k' : Fin (d + 1))
    (hadj : adjFn topCells hcard ⟨s, hs⟩ k = some (⟨s', hs'⟩, k')) :
    adjFn topCells hcard ⟨s', hs'⟩ k' = some (⟨s, hs⟩, k) := by
  -- Key facts
  set f := faceOf s (hcard s hs) k with hf_def
  have hne : s' ≠ s := adjFn_ne topCells hcard s hs k s' hs' k' hadj
  have hface_eq : faceOf s' (hcard s' hs') k' = f :=
    adjFn_face_eq topCells hcard s hs k s' hs' k' hadj
  have hs_cont : s ∈ containersOf topCells f :=
    self_mem_containersOf topCells s hs (hcard s hs) k
  have hs'_cont : s' ∈ containersOf topCells f :=
    adjFn_s'_mem_containers topCells hcard s hs k s' hs' k' hadj
  have hcard2 : (containersOf topCells f).card = 2 :=
    containersOf_card_eq_two_of_adjFn topCells hcard hpseudo s hs k s' hs' k' hadj
  -- Step through the dite chain of adjFn ⟨s', hs'⟩ k'
  unfold adjFn
  simp only
  -- First branch: containers not small (card = 2 > 1)
  have hcs_not_le_1 : ¬((containersOf topCells (faceOf s' (hcard s' hs') k')).card ≤ 1) := by
    rw [hface_eq]; omega
  rw [dif_neg hcs_not_le_1]
  -- Second branch: erase s' is nonempty (s is in there)
  have hne_erase : ((containersOf topCells (faceOf s' (hcard s' hs') k')).erase s').Nonempty := by
    rw [hface_eq]
    exact ⟨s, Finset.mem_erase.mpr ⟨hne.symm, hs_cont⟩⟩
  rw [dif_pos hne_erase]
  -- Show hne_erase.choose = s (singleton argument)
  have ht_mem_f : hne_erase.choose ∈ (containersOf topCells f).erase s' := by
    have h := hne_erase.choose_spec
    have hset_eq : (containersOf topCells (faceOf s' (hcard s' hs') k')).erase s' =
        (containersOf topCells f).erase s' := by rw [hface_eq]
    rw [← hset_eq]; exact h
  have ht_in_cs : hne_erase.choose ∈ containersOf topCells f :=
    Finset.mem_of_mem_erase ht_mem_f
  have h_erase_card : ((containersOf topCells f).erase s').card = 1 := by
    rw [Finset.card_erase_of_mem hs'_cont, hcard2]
  have hs_in_erase : s ∈ (containersOf topCells f).erase s' :=
    Finset.mem_erase.mpr ⟨hne.symm, hs_cont⟩
  have ht_eq_s : hne_erase.choose = s := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h_erase_card
    have hs_a : s = a := Finset.mem_singleton.mp (ha ▸ hs_in_erase)
    have ht_a : hne_erase.choose = a := Finset.mem_singleton.mp (ha ▸ ht_mem_f)
    exact ht_a.trans hs_a.symm
  -- Prove the full equality via Option/Prod injectivity
  simp only [Option.some.injEq, Prod.mk.injEq]
  refine ⟨Subtype.ext ht_eq_s, ?_⟩
  -- Fin component: findOppositeIdx hne_erase.choose _ face _ _ = k
  have h_idx_eq : ∀ (ht' : hne_erase.choose ∈ topCells)
      (hf' : faceOf s' (hcard s' hs') k' ⊆ hne_erase.choose)
      (hfc' : (faceOf s' (hcard s' hs') k').card = d),
      findOppositeIdx hne_erase.choose (hcard hne_erase.choose ht')
        (faceOf s' (hcard s' hs') k') hf' hfc' = k := by
    intro ht' hf' hfc'
    set idx := findOppositeIdx hne_erase.choose (hcard hne_erase.choose ht')
      (faceOf s' (hcard s' hs') k') hf' hfc'
    -- The vertex at idx is not in the face
    have h_nmem := vertexEnum_findOppositeIdx_not_mem hne_erase.choose
      (hcard hne_erase.choose ht')
      (faceOf s' (hcard s' hs') k') hf' hfc'
    -- Transport: face = faceOf s' hs' k' = faceOf s hs k = s.erase (vertexEnum s hs k)
    have h_nmem_f : vertexEnum hne_erase.choose (hcard hne_erase.choose ht') idx ∉ f :=
      hface_eq ▸ h_nmem
    -- The vertex IS in hne_erase.choose = s
    have h_mem_s : vertexEnum hne_erase.choose (hcard hne_erase.choose ht') idx ∈ s :=
      ht_eq_s ▸ vertexEnum_mem hne_erase.choose (hcard hne_erase.choose ht') idx
    -- f = faceOf s hs k = s.erase (vertexEnum s hs k), so vertex = vertexEnum s hs k
    have h_eq_vk : vertexEnum hne_erase.choose (hcard hne_erase.choose ht') idx =
        vertexEnum s (hcard s hs) k := by
      rw [show f = s.erase (vertexEnum s (hcard s hs) k) from rfl] at h_nmem_f
      rw [Finset.mem_erase, not_and_or] at h_nmem_f
      cases h_nmem_f with
      | inl h => exact not_not.mp h
      | inr h => exact absurd h_mem_s h
    -- Show vertexEnum hne_erase.choose ht' k = vertexEnum s hs k
    have h_veq : vertexEnum hne_erase.choose (hcard hne_erase.choose ht') k =
        vertexEnum s (hcard s hs) k := by
      unfold vertexEnum
      simp only [List.get_eq_getElem, ht_eq_s]
      rfl
    rw [← h_veq] at h_eq_vk
    exact vertexEnum_injective hne_erase.choose (hcard hne_erase.choose ht') h_eq_vk
  -- The goals remaining after `refine ⟨Subtype.ext ht_eq_s, ?_⟩` ask for
  -- findOppositeIdx with specific proof terms. We discharge them by
  -- providing the membership proof explicitly and letting proof irrelevance handle the rest.
  have ht_top : hne_erase.choose ∈ topCells :=
    (Finset.mem_filter.mp ht_in_cs).1
  exact h_idx_eq ht_top _ _

end Adjacency

/-! ## Bridge Theorem

The main result: Sperner's lemma for finite sets of top cells
satisfying the pseudomanifold condition. -/

section Bridge

variable {E : Type} [DecidableEq E] [LinearOrder E] {d : Nat}

/-- **Sperner's lemma for pseudomanifold simplicial data.**

Given:
- A finite set `topCells` of simplices, each with `d+1` vertices
- The pseudomanifold property (each codim-1 face in at most 2 cells)
- A coloring `c : E -> Fin (d+1)`
- An odd boundary door count

Then a panchromatic cell exists: some cell has all `d+1` colors
on its vertices. -/
theorem exists_panchromatic
    (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2)
    (c : E → Fin (d + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : { s : Finset E // s ∈ topCells } × Fin (d + 1) =>
        Sperner.IsDoor (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hcard σ.1 σ.2))
          c p.1 p.2 ∧
        adjFn topCells hcard p.1 p.2 = none)).card) :
    ∃ s : { s : Finset E // s ∈ topCells },
      Sperner.IsPanchromatic
        (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hcard σ.1 σ.2)) c s := by
  exact Sperner.exists_panchromatic
    (fun (σ : { s // s ∈ topCells }) => vertexEnum σ.1 (hcard σ.1 σ.2))
    (adjFn topCells hcard)
    (by intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj
        exact adjFn_symm topCells hcard hpseudo s hs k s' hs' k' hadj)
    (by intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj
        exact adjFn_vertex topCells hcard s hs k s' hs' k' hadj)
    (by intro ⟨s, hs⟩ k ⟨s', hs'⟩ k' hadj heq
        have hval : s = s' := congr_arg Subtype.val heq
        exact (adjFn_ne topCells hcard s hs k s' hs' k' hadj) hval.symm)
    c hbdry

end Bridge

/-! ## Connection to Geometry.SimplicialComplex

To apply `exists_panchromatic` to a Mathlib `Geometry.SimplicialComplex 𝕜 E`:

1. Extract the facets of cardinality `d+1` as a `Finset (Finset E)`.
   Since `K.faces` is a `Set (Finset E)`, this requires establishing
   finiteness for the specific complex (e.g., a triangulation of a
   polytope).

2. Provide the pseudomanifold condition: each codim-1 face is
   contained in at most 2 of the extracted facets.

3. Apply `exists_panchromatic` with the extracted `topCells`.

The `exists_panchromatic` theorem is parameterized by
`topCells : Finset (Finset E)` directly (no dependency on
`Geometry.SimplicialComplex`), making it usable without importing
`Mathlib.Analysis.Convex.SimplicialComplex.Basic`. -/

end Sperner.SimplicialComplex

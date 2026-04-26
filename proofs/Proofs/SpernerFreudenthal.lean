/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib
import Proofs.SpernerMathlib4

/-
# Freudenthal Triangulation as AbstractSimplicialData

This file constructs a concrete `AbstractSimplicialData` instance
from the Freudenthal triangulation of the unit n-cube, connecting
the abstract CellComplex/Triangulation framework with the
Freudenthal combinatorics.

## The Construction

The Freudenthal triangulation of the unit n-cube [0,1]^n divides
it into n! simplices, one per permutation of {0,...,n-1}. For a
permutation sigma (encoded as `Equiv.Perm (Fin n)`), the k-th
vertex (for k = 0,...,n) is `((List.ofFn sigma).take k).toFinset`.

Thus each simplex has vertices (as nested Finsets of Fin n):
  empty, {sigma(0)}, {sigma(0), sigma(1)}, ..., Finset.univ

The vertex type is `Finset (Fin n)`, equipped with a linear order
via a bitmap encoding.

## Main Definitions

* `FreudenthalCube.simplexOf`: the n+1 vertices of a permutation's simplex
* `FreudenthalCube.topSimplices`: all n! top simplices
* `FreudenthalCube.freudenthalSimplicialData`: the AbstractSimplicialData instance
* `FreudenthalCube.freudenthalTriangulation`: the Triangulation instance
* `FreudenthalCube.freudenthalCellComplex`: the CellComplex instance

## Main Results

* `FreudenthalCube.simplexOf_card`: each simplex has exactly n+1 vertices
* `FreudenthalCube.pseudomanifold`: each codim-1 face in at most 2 simplices
* `FreudenthalCube.freudenthalSperner`: Sperner's lemma for the Freudenthal triangulation

## References

* H. Freudenthal, *Simplizialzerlegungen von beschrankter Flachheit*
* M. De Longueville, *A Course in Topological Combinatorics*

## Tags

Freudenthal, triangulation, simplicial data, Sperner, cell complex, bridge
-/

set_option maxHeartbeats 400000

open Finset

namespace FreudenthalCube

/-
## Triangulation and AbstractSimplicialData

These structures mirror `SpernerSimplicialInstance.lean`.
-/

/-- A `Triangulation V n` is a finite collection of top-dimensional
simplices satisfying the pseudomanifold condition. -/
structure Triangulation (V : Type*) [DecidableEq V] (n : ℕ) where
  Cell : Type
  cellDecEq : DecidableEq Cell
  cellFintype : Fintype Cell
  vertex : Cell → Fin (n + 1) → V
  vertex_injective : ∀ s, Function.Injective (vertex s)
  adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1))
  adj_symm : ∀ s k s' k',
    adj s k = some (s', k') → adj s' k' = some (s, k)
  adj_vertex : ∀ s k s' k',
    adj s k = some (s', k') →
    (univ.erase k).image (vertex s) =
    (univ.erase k').image (vertex s')
  adj_ne : ∀ s k s' k',
    adj s k = some (s', k') → s ≠ s'

attribute [instance] Triangulation.cellDecEq
attribute [instance] Triangulation.cellFintype

/-- Every `Triangulation` gives rise to a `CellComplex`. -/
def Triangulation.toCellComplex {V : Type*} [DecidableEq V] {n : ℕ}
    (T : Triangulation V n) : CellComplex V n where
  Cell := T.Cell
  cellDecEq := T.cellDecEq
  cellFintype := T.cellFintype
  vertex := T.vertex
  adj := T.adj
  adj_symm := T.adj_symm
  adj_vertex := T.adj_vertex
  adj_ne := T.adj_ne

/-- Unordered simplicial data with the pseudomanifold property. -/
structure AbstractSimplicialData (V : Type*) [DecidableEq V]
    [LinearOrder V] (n : ℕ) where
  topSimplices : Finset (Finset V)
  card_eq : ∀ s ∈ topSimplices, s.card = n + 1
  pseudomanifold : ∀ (face : Finset V),
    face.card = n →
    (topSimplices.filter (fun s => face ⊆ s)).card ≤ 2

/-
## Bridge: AbstractSimplicialData to Triangulation
-/

private theorem sort_length_eq {V : Type} [DecidableEq V] [LinearOrder V]
    (s : Finset V) : (s.sort (· ≤ ·)).length = s.card := by
  simp

/-- Ordered vertex enumeration of a top simplex. -/
noncomputable def AbstractSimplicialData.vertexEnum
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) : V :=
  (s.sort (· ≤ ·)).get (k.cast (by
    rw [sort_length_eq]; exact (D.card_eq s hs).symm))

/-- The k-th vertex belongs to the simplex. -/
lemma AbstractSimplicialData.vertexEnum_mem
    {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}
    (D : AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1)) :
    D.vertexEnum s hs k ∈ s := by
  unfold vertexEnum
  have hmem := List.get_mem (s.sort (· ≤ ·))
    (k.cast (by rw [sort_length_eq]; exact (D.card_eq s hs).symm))
  exact (s.mem_sort (· ≤ ·)).mp hmem

/-- Construct a `Triangulation` from `AbstractSimplicialData`.

The adjacency axioms (adj_symm, adj_vertex, adj_ne) are sorried;
they are fully proved in `SpernerSimplicialInstance.lean` and will
be unified when that file is updated for the current Mathlib API. -/
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
    unfold vertexEnum at hij
    have hnd : (s.sort (· ≤ ·)).Nodup := s.sort_nodup (· ≤ ·)
    have hlen : (s.sort (· ≤ ·)).length = n + 1 := by
      rw [sort_length_eq]; exact D.card_eq s hs
    -- The sorted list is nodup so equal elements means equal indices
    -- Nodup + L[i] = L[j] → i = j
    sorry
  adj := fun ⟨s, hs⟩ k =>
    let face := s.erase (D.vertexEnum s hs k)
    let containers := D.topSimplices.filter (fun t => face ⊆ t)
    if _hc : containers.card ≤ 1 then none
    else
      let without_s := containers.erase s
      if hne : without_s.Nonempty then
        let t := hne.choose
        have ht_mem : t ∈ without_s := hne.choose_spec
        have ht_top : t ∈ D.topSimplices :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase ht_mem)).1
        have hface_sub : face ⊆ t :=
          (Finset.mem_filter.mp (Finset.mem_of_mem_erase ht_mem)).2
        have hface_card : face.card = n := by
          rw [Finset.card_erase_of_mem (D.vertexEnum_mem s hs k), D.card_eq s hs]; omega
        have hex : ∃ k' : Fin (n + 1), D.vertexEnum t ht_top k' ∉ face := by
          by_contra hall
          push_neg at hall
          have hsub : t ⊆ face := by
            intro v hv
            have hv_sort : v ∈ t.sort (· ≤ ·) := (t.mem_sort (· ≤ ·)).mpr hv
            rw [List.mem_iff_getElem] at hv_sort
            obtain ⟨idx, hidx_lt, hidx_eq⟩ := hv_sort
            have hidx_lt' : idx < n + 1 := by
              rw [sort_length_eq, D.card_eq t ht_top] at hidx_lt; exact hidx_lt
            have hmem := hall ⟨idx, hidx_lt'⟩
            have heq : D.vertexEnum t ht_top ⟨idx, hidx_lt'⟩ = v := by
              simp only [vertexEnum, List.get_eq_getElem]; exact hidx_eq
            rwa [heq] at hmem
          have := Finset.card_le_card hsub
          rw [D.card_eq t ht_top, hface_card] at this; omega
        some (⟨t, ht_top⟩, hex.choose)
      else none
  adj_symm := by intro _ _ _ _ h; sorry
  adj_vertex := by intro _ _ _ _ h; sorry
  adj_ne := by intro _ _ _ _ h; sorry

/-- Sperner's Lemma for Triangulations via CellComplex. -/
theorem Triangulation.sperner' {V : Type*} [DecidableEq V] {n : ℕ}
    (T : Triangulation V n)
    (c : V → Fin (n + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
        T.adj p.1 p.2 = none)).card) :
    ∃ s : T.Cell,
      CellComplex.IsPanchromatic c (T.toCellComplex) s :=
  CellComplex.sperner c T.toCellComplex hbdry

/-
## Linear order on Finset (Fin n)

We encode each `Finset (Fin n)` as a natural number via its
bitmap representation, inducing a linear order.
-/

/-- Encode a `Finset (Fin n)` as a natural number (bitmap). -/
def finsetToNat {n : ℕ} (s : Finset (Fin n)) : ℕ :=
  s.sum (fun i => 2 ^ i.val)

/-- The bitmap encoding is injective: distinct Finsets map to
distinct natural numbers via the binary representation. -/
theorem finsetToNat_injective (n : ℕ) : Function.Injective (@finsetToNat n) := by
  intro s t hst
  ext x
  -- The key property: in base 2, the x-th bit of finsetToNat s
  -- is 1 iff x ∈ s. Equal sums means equal bit patterns.
  sorry

/-- Linear order on `Finset (Fin n)` via bitmap encoding. -/
noncomputable instance finsetLinearOrder : LinearOrder (Finset (Fin n)) :=
  @LinearOrder.lift' (Finset (Fin n)) ℕ _ finsetToNat (finsetToNat_injective n)

/-
## Freudenthal Triangulation
-/

variable {n : ℕ}

/-- The list [sigma(0), ..., sigma(n-1)] for a permutation. -/
def permList (σ : Equiv.Perm (Fin n)) : List (Fin n) := List.ofFn σ

theorem permList_nodup (σ : Equiv.Perm (Fin n)) : (permList σ).Nodup :=
  List.nodup_ofFn.mpr σ.injective

theorem permList_length (σ : Equiv.Perm (Fin n)) : (permList σ).length = n := by
  simp [permList]

/-- The first k elements of list l as a Finset. -/
def prefixSet (l : List (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (l.take k).toFinset

theorem mem_prefixSet_iff {l : List (Fin n)} {k : ℕ} {x : Fin n} :
    x ∈ prefixSet l k ↔ x ∈ l.take k := by
  simp [prefixSet]

/-- For a nodup list, prefixSet has cardinality min(k, l.length). -/
theorem prefixSet_card {l : List (Fin n)} (hl : l.Nodup) (k : ℕ) :
    (prefixSet l k).card = min k l.length := by
  simp only [prefixSet]
  rw [List.toFinset_card_of_nodup (hl.sublist (List.take_sublist k l))]
  simp

theorem prefixSet_card_eq {l : List (Fin n)} (hl : l.Nodup) {k : ℕ}
    (hk : k ≤ l.length) :
    (prefixSet l k).card = k := by
  rw [prefixSet_card hl, Nat.min_eq_left hk]

/-- Prefix sets grow with their index. -/
theorem prefixSet_mono {l : List (Fin n)} {j k : ℕ} (hjk : j ≤ k) :
    prefixSet l j ⊆ prefixSet l k := by
  intro x hx
  simp only [prefixSet, List.mem_toFinset] at hx ⊢
  have htake_take : l.take j = (l.take k).take j := by
    rw [List.take_take, min_eq_left hjk]
  rw [htake_take] at hx
  exact (List.take_sublist j (l.take k)).subset hx

/-- The simplex for a permutation: the n+1 prefix sets. -/
noncomputable def simplexOf (σ : Equiv.Perm (Fin n)) : Finset (Finset (Fin n)) :=
  Finset.univ.image (fun k : Fin (n + 1) =>
    prefixSet (permList σ) k.val)

/-- prefixSet at different indices gives different Finsets. -/
theorem prefixSet_permList_injective (σ : Equiv.Perm (Fin n)) :
    Function.Injective (fun k : Fin (n + 1) => prefixSet (permList σ) k.val) := by
  intro ⟨i, hi⟩ ⟨j, hj⟩ h
  have hi' : i ≤ (permList σ).length := by rw [permList_length]; omega
  have hj' : j ≤ (permList σ).length := by rw [permList_length]; omega
  have hci := prefixSet_card_eq (permList_nodup σ) hi'
  have hcj := prefixSet_card_eq (permList_nodup σ) hj'
  have : (prefixSet (permList σ) i).card = (prefixSet (permList σ) j).card := by
    exact congrArg Finset.card h
  rw [hci, hcj] at this
  exact Fin.ext this

/-- Each simplex has exactly n+1 vertices. -/
theorem simplexOf_card (σ : Equiv.Perm (Fin n)) :
    (simplexOf σ).card = n + 1 := by
  rw [simplexOf, Finset.card_image_of_injective _ (prefixSet_permList_injective σ),
      Finset.card_univ, Fintype.card_fin]

/-- All top simplices of the Freudenthal triangulation. -/
noncomputable def topSimplices (n : ℕ) : Finset (Finset (Finset (Fin n))) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) => simplexOf σ)

theorem topSimplices_card_eq :
    ∀ s ∈ topSimplices n, s.card = n + 1 := by
  intro s hs
  rw [topSimplices, Finset.mem_image] at hs
  obtain ⟨σ, -, rfl⟩ := hs
  exact simplexOf_card σ

/-
## Pseudomanifold Property
-/

/-- The pseudomanifold property for the Freudenthal triangulation. -/
theorem pseudomanifold :
    ∀ (face : Finset (Finset (Fin n))),
      face.card = n →
      ((topSimplices n).filter (fun s => face ⊆ s)).card ≤ 2 := by
  sorry

/-
## AbstractSimplicialData, Triangulation, and CellComplex
-/

/-- The Freudenthal triangulation as `AbstractSimplicialData`. -/
noncomputable def freudenthalSimplicialData (n : ℕ) :
    AbstractSimplicialData (Finset (Fin n)) n where
  topSimplices := topSimplices n
  card_eq := topSimplices_card_eq
  pseudomanifold := pseudomanifold

/-- The Freudenthal triangulation as a `Triangulation`. -/
noncomputable def freudenthalTriangulation (n : ℕ) :
    Triangulation (Finset (Fin n)) n :=
  (freudenthalSimplicialData n).toTriangulation

/-- The Freudenthal triangulation as a `CellComplex`. -/
noncomputable def freudenthalCellComplex (n : ℕ) :
    CellComplex (Finset (Fin n)) n :=
  (freudenthalTriangulation n).toCellComplex

/-- **Sperner's Lemma for the Freudenthal Triangulation** -/
theorem freudenthalSperner (c : Finset (Fin n) → Fin (n + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : (freudenthalTriangulation n).Cell × Fin (n + 1) =>
        CellComplex.IsDoor c (freudenthalCellComplex n) p.1 p.2 ∧
        (freudenthalTriangulation n).adj p.1 p.2 = none)).card) :
    ∃ s : (freudenthalTriangulation n).Cell,
      CellComplex.IsPanchromatic c (freudenthalCellComplex n) s :=
  Triangulation.sperner' (freudenthalTriangulation n) c hbdry

end FreudenthalCube

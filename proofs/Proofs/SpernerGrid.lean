/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-
# Grid Triangulation Instance for Abstract Sperner's Lemma

We construct a concrete `CellComplex` instance from the standard
triangulation of the d-simplex with subdivision parameter N,
and combine it with the abstract Sperner theorem to obtain a
self-contained concrete Sperner's lemma.

## Main definitions

* `SpernerGrid.BaryPoint d N`: Barycentric lattice points on Δ_N.
* `SpernerGrid.GridSimplex d N`: d-simplices in the grid
  triangulation, represented as ordered chains.
* `SpernerGrid.gridComplex d N`: The `CellComplex` instance.

## Main results

* `SpernerGrid.boundary_doors_odd`: For Sperner colorings,
  boundary doors are odd.
* `SpernerGrid.sperner_grid`: Concrete Sperner's lemma —
  any Sperner coloring of the grid has a panchromatic cell.

## Sorry classification (13 total)

1. `CellComplex.sperner` — proved in SpernerMathlib4.lean,
   duplicated here for self-containment.
2. `GridSimplex Fintype` — engineering (finite subtype of
   finite product).
3. `verts_injective` — medium: show distinct incDir
   prevents vertex repetition.
4. `interiorFlip`, `boundaryFlip0`, `boundaryFlipLast` —
   hard: construct the adjacent simplex through each facet.
5. `gridAdj` — dispatches to the flip functions.
6. `gridAdj_symm/vertex/ne` — follow from flip definitions.
7. `no_boundary_doors_face_lt` — medium: needs boundary
   geometry (vertices on boundary facets have b_k = 0).
8. `boundary_doors_odd` — hard: induction on dimension,
   constructing (d-1)-dim boundary triangulation.

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]
* [M. J. Todd, *The Computation of Fixed Points and Applications*]
-/

set_option maxHeartbeats 3200000

open Finset

namespace SpernerGrid

-- ============================================================
-- SECTION I: CellComplex (from SpernerMathlib4)
-- ============================================================
-- Duplicated here so this file builds independently of
-- SpernerMathlib4.lean. The abstract Sperner theorem is
-- stated and sorry'd; the real proof is in SpernerMathlib4.

/-- An abstract cell complex with adjacency. -/
structure CellComplex (V : Type*) [DecidableEq V]
    (d : ℕ) where
  Cell : Type
  cellDecEq : DecidableEq Cell
  cellFintype : Fintype Cell
  vertex : Cell → Fin (d + 1) → V
  adj : Cell → Fin (d + 1) →
    Option (Cell × Fin (d + 1))
  adj_symm : ∀ s k s' k',
    adj s k = some (s', k') →
    adj s' k' = some (s, k)
  adj_vertex : ∀ s k s' k',
    adj s k = some (s', k') →
    (univ.erase k).image (vertex s) =
    (univ.erase k').image (vertex s')
  adj_ne : ∀ s k s' k',
    adj s k = some (s', k') → s ≠ s'

attribute [instance] CellComplex.cellDecEq
attribute [instance] CellComplex.cellFintype

namespace CellComplex

variable {V : Type*} [DecidableEq V] {d : ℕ}

def IsPanchromatic (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell) : Prop :=
  Function.Surjective (c ∘ K.vertex s)

def IsDoor (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell)
    (k : Fin (d + 1)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin (d + 1),
    i ≠ k ∧ c (K.vertex s i) = Fin.castSucc j

instance decidableIsPanchromatic
    (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Cell) :
    Decidable (IsPanchromatic c K s) := by
  unfold IsPanchromatic Function.Surjective
  exact inferInstance

instance decidableIsDoor (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell)
    (k : Fin (d + 1)) :
    Decidable (IsDoor c K s k) := by
  unfold IsDoor; exact inferInstance

/-- The abstract Sperner theorem (proved in SpernerMathlib4). -/
theorem sperner (c : V → Fin (d + 1))
    (K : CellComplex V d)
    (hbdry : Odd (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 = none)).card) :
    ∃ s : K.Cell, IsPanchromatic c K s := by
  sorry -- Proved in SpernerMathlib4.lean

end CellComplex

-- ============================================================
-- SECTION II: Barycentric Lattice Points
-- ============================================================

/-- A barycentric lattice point on the standard d-simplex with
subdivision parameter N: coordinates (b₀, ..., b_d) with
b_i ≥ 0 and ∑ b_i = N. -/
@[ext]
structure BaryPoint (d N : ℕ) where
  coords : Fin (d + 1) → ℕ
  sum_eq : ∑ i, coords i = N

instance (d N : ℕ) : DecidableEq (BaryPoint d N) := by
  intro a b
  by_cases h : a.coords = b.coords
  · exact isTrue (BaryPoint.ext h)
  · exact isFalse (fun hab =>
      h (congr_arg BaryPoint.coords hab))

instance baryPointFintype (d N : ℕ) :
    Fintype (BaryPoint d N) := by
  have equiv : BaryPoint d N ≃
      { f : Fin (d + 1) → Fin (N + 1) //
        ∑ i, (f i).val = N } :=
    { toFun := fun p =>
        ⟨fun i => ⟨p.coords i, by
          have h1 := Finset.single_le_sum
            (f := p.coords) (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i)
          have h2 := p.sum_eq
          omega⟩,
         by simp [p.sum_eq]⟩
      invFun := fun ⟨f, hf⟩ =>
        ⟨fun i => (f i).val, by simpa using hf⟩
      left_inv := fun p => by ext i; simp
      right_inv := fun ⟨f, hf⟩ => by
        ext i; simp }
  exact Fintype.ofEquiv _ equiv.symm

/-- A vertex lies on face k: its k-th barycentric coordinate
is zero. -/
def BaryPoint.onFace {d N : ℕ} (v : BaryPoint d N)
    (k : Fin (d + 1)) : Prop :=
  v.coords k = 0

instance {d N : ℕ} (v : BaryPoint d N)
    (k : Fin (d + 1)) :
    Decidable (v.onFace k) :=
  inferInstanceAs (Decidable (_ = _))

/-- Sperner condition: on face k (where b_k = 0), color k is
forbidden. -/
def IsSperner {d N : ℕ}
    (c : BaryPoint d N → Fin (d + 1)) : Prop :=
  ∀ (v : BaryPoint d N) (k : Fin (d + 1)),
    v.onFace k → c v ≠ k

-- ============================================================
-- SECTION III: Grid Simplices
-- ============================================================

/-- A d-simplex in the grid triangulation of Δ_N.

A chain of d+1 barycentric lattice points where consecutive
vertices differ by a single unit transfer: one coordinate
increases by 1, another decreases by 1. The d "increased"
coordinates must be distinct (injective), ensuring the chain
spans a full d-simplex.

Each step transfers one unit of "mass" from one barycentric
coordinate to another, maintaining ∑ b_i = N. -/
structure GridSimplex (d N : ℕ) where
  /-- The d+1 vertices in chain order. -/
  verts : Fin (d + 1) → BaryPoint d N
  /-- Which coordinate increases at step k. -/
  incDir : Fin d → Fin (d + 1)
  /-- Which coordinate decreases at step k. -/
  decDir : Fin d → Fin (d + 1)
  /-- Increase and decrease differ at each step. -/
  inc_ne_dec : ∀ k : Fin d, incDir k ≠ decDir k
  /-- The increased coordinate goes up by 1. -/
  step_inc : ∀ k : Fin d,
    (verts k.succ).coords (incDir k) =
    (verts k.castSucc).coords (incDir k) + 1
  /-- The decreased coordinate goes down by 1. -/
  step_dec : ∀ k : Fin d,
    (verts k.castSucc).coords (decDir k) =
    (verts k.succ).coords (decDir k) + 1
  /-- All other coordinates are unchanged. -/
  step_same : ∀ (k : Fin d) (j : Fin (d + 1)),
    j ≠ incDir k → j ≠ decDir k →
    (verts k.succ).coords j =
    (verts k.castSucc).coords j
  /-- The increased directions are all distinct. -/
  inc_injective : Function.Injective incDir

instance gridSimplexDecEq (d N : ℕ) :
    DecidableEq (GridSimplex d N) := by
  intro a b
  by_cases hv : a.verts = b.verts
  · by_cases hi : a.incDir = b.incDir
    · by_cases hd : a.decDir = b.decDir
      · exact isTrue (by
          cases a; cases b
          simp only at hv hi hd
          subst hv; subst hi; subst hd; rfl)
      · exact isFalse (fun h =>
          hd (by cases h; rfl))
    · exact isFalse (fun h =>
        hi (by cases h; rfl))
  · exact isFalse (fun h =>
      hv (by cases h; rfl))

instance gridSimplexFintype (d N : ℕ) :
    Fintype (GridSimplex d N) := by
  sorry -- Fintype via subtype of finite product

-- ============================================================
-- SECTION IV: Basic Properties
-- ============================================================

variable {d N : ℕ}

/-- Consecutive vertices in a GridSimplex are distinct. -/
theorem GridSimplex.verts_succ_ne (s : GridSimplex d N)
    (k : Fin d) :
    s.verts k.succ ≠ s.verts k.castSucc := by
  intro heq
  have h := s.step_inc k
  rw [show (s.verts k.succ).coords (s.incDir k) =
    (s.verts k.castSucc).coords (s.incDir k) from
    congr_arg (fun v => v.coords (s.incDir k)) heq] at h
  omega

/-- All d+1 vertices of a GridSimplex are pairwise distinct. -/
theorem GridSimplex.verts_injective (s : GridSimplex d N) :
    Function.Injective s.verts := by
  sorry

/-- The vertex set (as a Finset) has cardinality d + 1. -/
theorem GridSimplex.vertex_set_card (s : GridSimplex d N) :
    (univ.image s.verts).card = d + 1 := by
  rw [Finset.card_image_of_injective _ s.verts_injective]
  simp [Fintype.card_fin]

-- ============================================================
-- SECTION V: Adjacency
-- ============================================================

/-- Interior flip: commute steps k-1 and k to produce the
adjacent simplex through facet k (for 0 < k < d).

Given chain ... → v_{k-1} --step(k-1)--> v_k --step(k)--> v_{k+1} → ...
the flip gives ... → v_{k-1} --step(k)--> v'_k --step(k-1)--> v_{k+1} → ...
where v'_k = v_{k-1} + e_{incDir(k)} - e_{decDir(k)}.

Returns none if the flip vertex would have a negative
coordinate (boundary facet). -/
noncomputable def GridSimplex.interiorFlip
    (s : GridSimplex d N) (k : Fin d)
    (hk : 0 < k.val) :
    Option (GridSimplex d N × Fin (d + 1)) := by
  sorry

/-- Boundary flip at k = 0: extend the chain backward using
the unique skipped direction. -/
noncomputable def GridSimplex.boundaryFlip0
    (s : GridSimplex d N) :
    Option (GridSimplex d N × Fin (d + 1)) := by
  sorry

/-- Boundary flip at k = d: extend the chain forward using
the unique skipped direction. -/
noncomputable def GridSimplex.boundaryFlipLast
    (s : GridSimplex d N) :
    Option (GridSimplex d N × Fin (d + 1)) := by
  sorry

/-- The adjacency function for the grid CellComplex.
Dispatches to interior or boundary flips based on the
facet position k. -/
noncomputable def gridAdj (d N : ℕ)
    (s : GridSimplex d N) (k : Fin (d + 1)) :
    Option (GridSimplex d N × Fin (d + 1)) := by
  sorry

-- ============================================================
-- SECTION VI: CellComplex Instance
-- ============================================================

/-- Adjacency is symmetric: if s is adjacent to s' through
facet k, then s' is adjacent to s through facet k'. -/
theorem gridAdj_symm (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    gridAdj d N s' k' = some (s, k) := by
  sorry

/-- Adjacent cells share the codimension-1 face. -/
theorem gridAdj_vertex (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    (univ.erase k).image s.verts =
    (univ.erase k').image s'.verts := by
  sorry

/-- Adjacent cells are distinct. -/
theorem gridAdj_ne (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    s ≠ s' := by
  sorry

/-- The grid CellComplex: the standard triangulation of Δ_N
satisfies the abstract adjacency axioms. -/
noncomputable def gridComplex (d N : ℕ) :
    CellComplex (BaryPoint d N) d where
  Cell := GridSimplex d N
  cellDecEq := inferInstance
  cellFintype := inferInstance
  vertex := fun s => s.verts
  adj := gridAdj d N
  adj_symm := gridAdj_symm
  adj_vertex := gridAdj_vertex
  adj_ne := gridAdj_ne

-- ============================================================
-- SECTION VII: Sperner Condition and Boundary Analysis
-- ============================================================

/-- On boundary face k, the Sperner condition prevents doors.
If a simplex has its k-th facet on the boundary (adj = none)
and k is NOT the "last" face, then the facet cannot be a
door because the Sperner condition forbids color k on face k,
but a door at position k requires colors {0,...,d-1} which
includes k (when k < d). -/
theorem no_boundary_doors_face_lt
    (c : BaryPoint d N → Fin (d + 1))
    (hc : IsSperner c)
    (s : GridSimplex d N) (k : Fin (d + 1))
    (hk : k.val < d)
    (hbdry : gridAdj d N s k = none) :
    ¬CellComplex.IsDoor c (gridComplex d N) s k := by
  sorry

/-- The boundary door count for Sperner colorings is odd.

This is the key inductive lemma. The proof is by induction
on d:
- **Base d = 0**: The unique 0-simplex has 1 boundary door.
- **Inductive step**: Restrict the coloring to face d and
  apply the (d-1)-dimensional result. The restricted boundary
  doors correspond to the d-dimensional boundary doors on
  face d. By the above lemma, doors on faces k < d vanish,
  so all boundary doors are on face d, and their count
  matches the (d-1)-dimensional panchromatic count (odd). -/
theorem boundary_doors_odd (d N : ℕ) (hN : 0 < N)
    (c : BaryPoint d N → Fin (d + 1))
    (hc : IsSperner c) :
    Odd (Finset.univ.filter
      (fun p : (gridComplex d N).Cell ×
        Fin (d + 1) =>
        CellComplex.IsDoor c (gridComplex d N)
          p.1 p.2 ∧
        (gridComplex d N).adj p.1 p.2 =
          none)).card := by
  sorry

-- ============================================================
-- SECTION VIII: Concrete Sperner's Lemma
-- ============================================================

/-- **Concrete Sperner's Lemma on the Grid**: For any Sperner
coloring of the grid triangulation of the d-simplex with
subdivision N > 0, there exists a panchromatic cell.

This combines:
1. The abstract Sperner theorem (`CellComplex.sperner`)
2. The grid CellComplex instance (`gridComplex`)
3. The boundary door oddness lemma (`boundary_doors_odd`)

No extra hypotheses needed — the boundary oddness follows
from the Sperner condition and the grid structure. -/
theorem sperner_grid (d N : ℕ) (hN : 0 < N)
    (c : BaryPoint d N → Fin (d + 1))
    (hc : IsSperner c) :
    ∃ s : (gridComplex d N).Cell,
      CellComplex.IsPanchromatic c
        (gridComplex d N) s :=
  CellComplex.sperner c (gridComplex d N)
    (boundary_doors_odd d N hN c hc)

end SpernerGrid

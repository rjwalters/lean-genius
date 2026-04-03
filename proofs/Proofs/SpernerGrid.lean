/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-
# Grid Triangulation Instance for Abstract Sperner's Lemma

We construct a concrete `CellComplex` instance from the standard
Freudenthal triangulation of the d-simplex with subdivision
parameter N, and combine it with the abstract Sperner theorem
to obtain a self-contained concrete Sperner's lemma.

## Main definitions

* `SpernerGrid.BaryPoint d N`: Barycentric lattice points on Δ_N.
* `SpernerGrid.GridSimplex d N`: d-simplices in the grid
  triangulation, represented as ordered chains with a constant
  "miss" (decrease) direction.
* `SpernerGrid.gridComplex d N`: The `CellComplex` instance.

## Main results

* `SpernerGrid.boundary_doors_odd`: For Sperner colorings,
  boundary doors are odd.
* `SpernerGrid.sperner_grid`: Concrete Sperner's lemma —
  any Sperner coloring of the grid has a panchromatic cell.

## Design: constant miss direction

Each grid simplex is a chain v₀ → v₁ → ... → v_d where step k
transfers one unit of mass from the "miss" coordinate to
incDir(k). The miss direction is CONSTANT across all steps —
this is the standard Freudenthal/Kuhn construction.

A variable decrease direction would allow degenerate "cycles"
(e.g., incDir=[0,1], decDir=[1,0] gives v₂ = v₀), making
`verts_injective` unprovable. The constant miss prevents this:
coordinate incDir(k) increases exactly once (at step k) and
never decreases (since miss ≠ incDir(k) for all k), so
vertices at different positions always differ.

## Sorry classification (9 total)

1. `CellComplex.sperner` — proved in SpernerMathlib4.lean,
   duplicated here for self-containment.
2. `interiorFlip`, `boundaryFlip0`, `boundaryFlipLast` —
   hard: construct the adjacent simplex through each facet.
3. `gridAdj` — dispatches to the flip functions.
4. `gridAdj_symm/vertex/ne` — follow from flip definitions.
5. `no_boundary_doors_face_lt` — medium: needs boundary
   geometry (vertices on boundary facets have b_k = 0).
6. `boundary_doors_odd` — hard: induction on dimension,
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

/-- A d-simplex in the Freudenthal triangulation of Δ_N.

A chain of d+1 barycentric lattice points where each step
transfers one unit of mass from a fixed "miss" coordinate to
a varying "incDir" coordinate. The d increase directions must
be distinct (injective), and miss is not among them.

This means the d+1 directions Fin(d+1) decompose as:
- d directions in range(incDir): each increases exactly once
- 1 direction (miss): decreases at every step

This is the standard Freudenthal/Kuhn construction. -/
structure GridSimplex (d N : ℕ) where
  /-- The d+1 vertices in chain order. -/
  verts : Fin (d + 1) → BaryPoint d N
  /-- Which coordinate increases at step k. -/
  incDir : Fin d → Fin (d + 1)
  /-- The coordinate that decreases at every step. -/
  miss : Fin (d + 1)
  /-- The miss direction is not an increase direction. -/
  miss_ne_inc : ∀ k : Fin d, incDir k ≠ miss
  /-- The increased coordinate goes up by 1. -/
  step_inc : ∀ k : Fin d,
    (verts k.succ).coords (incDir k) =
    (verts k.castSucc).coords (incDir k) + 1
  /-- The miss coordinate goes down by 1. -/
  step_dec : ∀ k : Fin d,
    (verts k.castSucc).coords miss =
    (verts k.succ).coords miss + 1
  /-- All other coordinates are unchanged. -/
  step_same : ∀ (k : Fin d) (j : Fin (d + 1)),
    j ≠ incDir k → j ≠ miss →
    (verts k.succ).coords j =
    (verts k.castSucc).coords j
  /-- The increased directions are all distinct. -/
  inc_injective : Function.Injective incDir

instance gridSimplexDecEq (d N : ℕ) :
    DecidableEq (GridSimplex d N) := by
  intro a b
  by_cases hv : a.verts = b.verts
  · by_cases hi : a.incDir = b.incDir
    · by_cases hm : a.miss = b.miss
      · exact isTrue (by
          cases a; cases b
          simp only at hv hi hm
          subst hv; subst hi; subst hm; rfl)
      · exact isFalse (fun h =>
          hm (by cases h; rfl))
    · exact isFalse (fun h =>
        hi (by cases h; rfl))
  · exact isFalse (fun h =>
      hv (by cases h; rfl))

noncomputable instance gridSimplexFintype (d N : ℕ) :
    Fintype (GridSimplex d N) :=
  Fintype.ofInjective
    (fun s : GridSimplex d N => (s.verts, s.incDir, s.miss))
    (fun a b h => by
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h
      subst h1; subst h2; subst h3; rfl)

-- ============================================================
-- SECTION IV: Basic Properties
-- ============================================================

variable {d N : ℕ}

/-- Coordinate incDir(k) is unchanged at step k' ≠ k.
Since incDir is injective, incDir(k') ≠ incDir(k). And
miss ≠ incDir(k) by miss_ne_inc. So step_same applies. -/
theorem GridSimplex.incDir_stable (s : GridSimplex d N)
    (k k' : Fin d) (hne : k ≠ k') :
    (s.verts k'.succ).coords (s.incDir k) =
    (s.verts k'.castSucc).coords (s.incDir k) :=
  s.step_same k' (s.incDir k)
    (fun h => hne (s.inc_injective h))
    (s.miss_ne_inc k)

/-- Coordinate incDir(k) has the same value at vertex m as at
vertex k.succ, for any m ≥ k.succ. This is because the only
step that changes incDir(k) is step k, which occurs before m.

Proved by strong induction on m.val. -/
theorem GridSimplex.incDir_const_after (s : GridSimplex d N)
    (k : Fin d) (m : Fin (d + 1))
    (hm : k.succ ≤ m) :
    (s.verts m).coords (s.incDir k) =
    (s.verts k.succ).coords (s.incDir k) := by
  -- Induction on m.val
  have : ∀ p : ℕ, (hp : p < d + 1) → k.succ.val ≤ p →
      (s.verts ⟨p, hp⟩).coords (s.incDir k) =
      (s.verts k.succ).coords (s.incDir k) := by
    intro p hp hkp
    induction p with
    | zero =>
      -- k.succ.val ≥ 1, so k.succ.val ≤ 0 is impossible
      simp [Fin.succ] at hkp
    | succ p' ih =>
      by_cases hbase : k.succ.val = p' + 1
      · -- k.succ.val = p' + 1
        have hkv : k.val = p' := by
          have := k.isLt; simp [Fin.succ] at hbase; omega
        have heq : (⟨p' + 1, hp⟩ : Fin (d + 1)) = k.succ := by
          apply Fin.ext; simp [Fin.succ]; omega
        rw [show s.verts ⟨p' + 1, hp⟩ = s.verts k.succ from
          congr_arg s.verts heq]
      · -- p' ≥ k.succ.val, so IH applies
        have hp' : p' < d + 1 := by omega
        have hkp' : k.succ.val ≤ p' := by omega
        have ih_val := ih hp' hkp'
        -- Step from p' to p'+1 uses step index ⟨p', _⟩
        have hpd : p' < d := by omega
        let step : Fin d := ⟨p', hpd⟩
        have hstep_ne : k ≠ step := by
          intro heq
          simp [step, Fin.ext_iff] at heq
          simp [Fin.succ] at *; omega
        have hstable := s.incDir_stable k step hstep_ne
        have hsc : step.castSucc = ⟨p', hp'⟩ := by
          ext; simp [step, Fin.castSucc]
        have hss : step.succ = ⟨p' + 1, hp⟩ := by
          ext; simp [step, Fin.succ]
        rw [hss, hsc] at hstable
        rw [hstable, ih_val]
  exact this m.val m.isLt (by exact hm)

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

/-- All d+1 vertices of a GridSimplex are pairwise distinct.

With constant miss, coordinate incDir(k) increases exactly
once (at step k) and never changes at other steps. So for
i < j, taking k = ⟨i, _⟩, we get
  v_j(incDir k) = v_i(incDir k) + 1
since the +1 at step k is the only change, proving v_i ≠ v_j. -/
theorem GridSimplex.verts_injective (s : GridSimplex d N) :
    Function.Injective s.verts := by
  intro i j heq
  suffices i.val = j.val from Fin.val_injective this
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- i < j: track coordinate incDir(⟨i, _⟩)
    have hid : i.val < d := by omega
    let k : Fin d := ⟨i.val, hid⟩
    -- After step k: incDir(k) has increased by 1
    have h1 := s.step_inc k
    -- k.castSucc = i
    have hkc : k.castSucc = i := Fin.ext (by simp [k, Fin.castSucc])
    -- k.succ ≤ j (since i < j means i+1 ≤ j)
    have hksj : k.succ ≤ j := by
      simp [Fin.le_iff_val_le_val, k, Fin.succ]; omega
    -- By incDir_const_after: verts(j) and verts(k.succ) agree on incDir(k)
    have h2 := s.incDir_const_after k j hksj
    -- So verts(j).coords(incDir k) = verts(i).coords(incDir k) + 1
    rw [hkc] at h1
    have : (s.verts j).coords (s.incDir k) =
        (s.verts i).coords (s.incDir k) + 1 := by
      rw [h2, h1]
    -- But heq says verts i = verts j
    rw [congr_arg (fun v => v.coords (s.incDir k)) heq] at this
    omega
  · -- j < i: symmetric
    have hjd : j.val < d := by omega
    let k : Fin d := ⟨j.val, hjd⟩
    have h1 := s.step_inc k
    have hkc : k.castSucc = j := Fin.ext (by simp [k, Fin.castSucc])
    have hksi : k.succ ≤ i := by
      simp [Fin.le_iff_val_le_val, k, Fin.succ]; omega
    have h2 := s.incDir_const_after k i hksi
    rw [hkc] at h1
    have : (s.verts i).coords (s.incDir k) =
        (s.verts j).coords (s.incDir k) + 1 := by
      rw [h2, h1]
    rw [congr_arg (fun v => v.coords (s.incDir k)) heq] at this
    omega

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

Given chain ... → v_{k-1} --[+incDir(k-1),-miss]--> v_k
  --[+incDir(k),-miss]--> v_{k+1} → ...
the flip gives
  ... → v_{k-1} --[+incDir(k),-miss]--> v'_k
  --[+incDir(k-1),-miss]--> v_{k+1} → ...

The new vertex v'_k = v_{k-1} + e_{incDir(k)} - e_{miss}.
Same miss direction. incDir swaps positions k-1 and k.
All vertices except k are shared. -/
noncomputable def GridSimplex.interiorFlip
    (s : GridSimplex d N) (k : Fin d)
    (hk : 0 < k.val) :
    Option (GridSimplex d N × Fin (d + 1)) := by
  sorry

/-- Boundary flip at k = 0: the facet opposite vertex 0 is
shared with a simplex that has a different miss direction.

Returns none if vertex 0 is on the geometric boundary
(v₀.coords(miss) = 0 means miss coordinate can't decrease
further in the other direction). -/
noncomputable def GridSimplex.boundaryFlip0
    (s : GridSimplex d N) :
    Option (GridSimplex d N × Fin (d + 1)) := by
  sorry

/-- Boundary flip at k = d: the facet opposite the last vertex
is shared with a simplex that has a different miss direction.

Returns none if vertex d is on the geometric boundary. -/
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

/-- The boundary door count for Sperner colorings is odd. -/
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

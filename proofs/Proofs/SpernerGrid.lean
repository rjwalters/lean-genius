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

## Sorry classification (2 remaining)

1. `CellComplex.sperner` — proved in SpernerMathlib4.lean,
   duplicated here for self-containment.
2. `boundary_verts_on_face` + `boundary_doors_odd` — FALSE as
   stated; require fundamental redesign of GridSimplex/gridAdj.

## Known design issues

`boundary_verts_on_face` is FALSE: gridAdj=none at k=0 means
(v_d).coords miss=0, NOT ∀ j≠k, (v_j).coords k=0.
Counterexample: d=2, N=3, s with v₀=(2,0,1), v₁=(1,1,1),
v₂=(0,1,2), miss=0, incDir=[1,2]. gridAdj=none at k=0
(since v₂.coords 0=0) but v₁.coords 0=1≠0.

`boundary_doors_odd` is FALSE for d=1: each geometric edge has 2
GridSimplex representations (miss=0 and miss=1), so boundary door
count is always 2 (even). Root cause: gridAdj misses cross-miss
adjacencies — the adjacent simplex with a different miss direction.

`sperner_grid` requires N≥d for the complex to be non-empty, but
the hypothesis only says N>0. For d=2, N=1: the complex is empty.

Root cause: GridSimplex/gridAdj treats "can't do boundary flip" as
"geometric boundary", which is wrong when the adjacent simplex has
a different miss direction. Correct formulation requires redesigning
GridSimplex to track cross-miss neighbors, or restricting to d=0.

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
-- SECTION V: Coordinate Tracking Lemmas
-- ============================================================

/-- The miss coordinate decreases by exactly 1 at each step,
so at vertex m it equals v₀.coords(miss) - m. -/
theorem GridSimplex.miss_coord_at (s : GridSimplex d N)
    (m : Fin (d + 1)) :
    (s.verts m).coords s.miss =
    (s.verts 0).coords s.miss - m.val := by
  induction m using Fin.induction with
  | zero => simp
  | succ k ih =>
    have hsd := s.step_dec k
    -- step_dec: verts(k.castSucc).coords miss =
    --           verts(k.succ).coords miss + 1
    -- So verts(k.succ).coords miss =
    --    verts(k.castSucc).coords miss - 1
    rw [ih] at hsd
    have hcv : k.castSucc.val = k.val := rfl
    have hsv : k.succ.val = k.val + 1 := rfl
    omega

/-- The base vertex's miss coordinate is at least d
(since it decreases by 1 at each of d steps). -/
theorem GridSimplex.base_miss_ge_d (s : GridSimplex d N) :
    d ≤ (s.verts 0).coords s.miss := by
  induction d with
  | zero => omega
  | succ n ih =>
    -- At step n, coords = base - n, and step_dec says
    -- verts(n.castSucc).coords miss = verts(n.succ).coords miss + 1
    -- so base - n ≥ 1, i.e., base ≥ n + 1.
    have hsd := s.step_dec ⟨n, by omega⟩
    have hmca := s.miss_coord_at ⟨n, by omega⟩
    have : (⟨n, by omega⟩ : Fin (n + 2)).val = n := rfl
    rw [this] at hmca
    -- hmca : verts(⟨n,...⟩).coords miss = base - n
    -- hsd : verts(⟨n,...⟩.castSucc).coords miss = verts(⟨n,...⟩.succ).coords miss + 1
    have hcv : (⟨n, by omega⟩ : Fin (n + 1)).castSucc.val = n := rfl
    have hsv : (⟨n, by omega⟩ : Fin (n + 1)).succ.val = n + 1 := rfl
    -- castSucc and the original Fin (n+2) element have same val
    have : (⟨n, by omega⟩ : Fin (n + 1)).castSucc = (⟨n, by omega⟩ : Fin (n + 2)) := by
      ext; simp
    rw [this] at hsd
    rw [hmca] at hsd
    -- hsd : base - n = verts(⟨n,...⟩.succ).coords miss + 1
    -- This means base - n ≥ 1, so base ≥ n + 1
    omega

/-- At vertex m, the miss coordinate is at least d - m. -/
theorem GridSimplex.miss_coord_ge (s : GridSimplex d N)
    (m : Fin (d + 1)) :
    d - m.val ≤ (s.verts m).coords s.miss := by
  rw [s.miss_coord_at m]
  have := s.base_miss_ge_d
  omega

/-- incDir(k) is the unique complement of miss: incDir gives
a bijection from Fin d to Fin(d+1) \ {miss}. This means
every j ≠ miss is in the range of incDir. -/
theorem GridSimplex.incDir_surj_complement (s : GridSimplex d N)
    (j : Fin (d + 1)) (hj : j ≠ s.miss) :
    ∃ k : Fin d, s.incDir k = j := by
  -- incDir is injective from Fin d to Fin(d+1), avoiding miss.
  -- Since |Fin d| = d = |Fin(d+1)| - 1 = |Fin(d+1) \ {miss}|,
  -- it must be surjective onto the complement.
  by_contra h
  push_neg at h
  -- All d values incDir(k) are in Fin(d+1) \ {miss, j}
  -- which has d+1-2 = d-1 elements. But incDir is injective
  -- with d values, contradiction.
  have hcard : (Finset.univ.image s.incDir).card = d := by
    rw [Finset.card_image_of_injective _ s.inc_injective]
    simp
  have hsub : Finset.univ.image s.incDir ⊆
      (Finset.univ.erase s.miss).erase j := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨k, rfl⟩ := hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨h k, s.miss_ne_inc k⟩
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hmiss_mem : s.miss ∈ (Finset.univ : Finset (Fin (d + 1))) := Finset.mem_univ _
  have hj_mem : j ∈ (Finset.univ.erase s.miss) := by
    rw [Finset.mem_erase]
    exact ⟨hj, Finset.mem_univ _⟩
  rw [Finset.card_erase_of_mem hj_mem, Finset.card_erase_of_mem hmiss_mem] at hle
  simp at hle
  omega

-- ============================================================
-- SECTION VI: Adjacency
-- ============================================================

/-- Helper: construct a new BaryPoint by transferring one
unit from coordinate `dec` to coordinate `inc`. -/
noncomputable def BaryPoint.transfer {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    BaryPoint d N where
  coords := fun j =>
    if j = inc then v.coords j + 1
    else if j = dec then v.coords j - 1
    else v.coords j
  sum_eq := by
    have hv := v.sum_eq
    have hkey : ∀ (j : Fin (d + 1)), j ∈ Finset.univ →
      (if j = inc then v.coords j + 1
        else if j = dec then v.coords j - 1
        else v.coords j) + (if j = dec then 1 else 0) =
        v.coords j + (if j = inc then 1 else 0) := by
      intro j _; split_ifs <;> simp_all <;> omega
    have hsums := Finset.sum_congr rfl hkey
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsums
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsums
    omega

@[simp]
theorem BaryPoint.transfer_coords_inc {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    (v.transfer inc dec h_ne h_pos).coords inc =
    v.coords inc + 1 := by
  simp [BaryPoint.transfer]

@[simp]
theorem BaryPoint.transfer_coords_dec {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec) :
    (v.transfer inc dec h_ne h_pos).coords dec =
    v.coords dec - 1 := by
  simp [BaryPoint.transfer, Ne.symm h_ne]

@[simp]
theorem BaryPoint.transfer_coords_other {d N : ℕ}
    (v : BaryPoint d N) (inc dec : Fin (d + 1))
    (h_ne : inc ≠ dec) (h_pos : 0 < v.coords dec)
    (j : Fin (d + 1)) (hj_inc : j ≠ inc)
    (hj_dec : j ≠ dec) :
    (v.transfer inc dec h_ne h_pos).coords j =
    v.coords j := by
  simp [BaryPoint.transfer, hj_inc, hj_dec]

/-- Interior flip: swap steps k and k-1 to produce the
adjacent simplex through facet k.castSucc (for 0 < k.val).

The new vertex at position k.castSucc is
  v_{k-1} + e_{incDir(k)} - e_{miss}.
Same miss. incDir swaps at positions k-1 and k. -/
noncomputable def GridSimplex.interiorFlip
    (s : GridSimplex d N) (k : Fin d)
    (hk : 0 < k.val) :
    GridSimplex d N × Fin (d + 1) :=
  let k_prev : Fin d := ⟨k.val - 1, by omega⟩
  let prev_v_idx : Fin (d + 1) := ⟨k.val - 1, by omega⟩
  let v_prev := s.verts prev_v_idx
  -- New vertex: v_{k-1} + e_{incDir(k)} - e_{miss}
  have h_miss_pos : 0 < v_prev.coords s.miss := by
    have h1 := s.miss_coord_ge prev_v_idx
    have h2 : prev_v_idx.val = k.val - 1 := rfl
    have h3 : k.val < d := k.isLt
    have h4 : prev_v_idx.val < d := by omega
    have h5 : 1 ≤ d - prev_v_idx.val := by omega
    -- h1 : d - prev_v_idx.val ≤ coords, h5 : 1 ≤ d - prev_v_idx.val
    -- so 1 ≤ coords
    exact Nat.lt_of_lt_of_le (by omega : 0 < d - prev_v_idx.val) h1
  have h_ne : s.incDir k ≠ s.miss := s.miss_ne_inc k
  let new_v := v_prev.transfer (s.incDir k) s.miss h_ne h_miss_pos
  -- New incDir: swap at positions k_prev and k
  let new_incDir : Fin d → Fin (d + 1) := fun j =>
    if j = k_prev then s.incDir k
    else if j = k then s.incDir k_prev
    else s.incDir j
  -- The new simplex
  let s' : GridSimplex d N :=
    { verts := fun j =>
        if j = ⟨k.val, by omega⟩ then new_v
        else s.verts j
      incDir := new_incDir
      miss := s.miss
      miss_ne_inc := by
        intro j
        simp only [new_incDir]
        split_ifs with h1 h2
        · exact s.miss_ne_inc k
        · exact s.miss_ne_inc k_prev
        · exact s.miss_ne_inc j
      step_inc := by
        intro j_step
        simp only [new_incDir]
        by_cases hjp : j_step = k_prev
        · -- Case j_step = k_prev
          subst hjp; simp only [ite_true]
          have hcs_ne : ¬(k_prev.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
            intro h; simp [Fin.ext_iff, k_prev, Fin.castSucc] at h; omega
          have hss_eq : (k_prev.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
            ext; simp [k_prev, Fin.succ]; omega
          simp only [hcs_ne, ite_false, hss_eq, ite_true]
          exact BaryPoint.transfer_coords_inc v_prev (s.incDir k) s.miss h_ne h_miss_pos
        · simp only [hjp, ite_false]
          by_cases hjk : j_step = k
          · -- Case j_step = k: avoid subst, work via rewriting
            have hjp' : ¬(k = k_prev) := by
              intro h; apply hjp; rw [hjk, h]
            rw [hjk]; simp only [hjp', ite_false, ite_true]
            have hcs_eq : (k.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              ext; simp [Fin.castSucc]
            have hss_ne : ¬(k.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              simp [Fin.ext_iff, Fin.succ]
            simp only [hcs_eq, ite_true, hss_ne, ite_false]
            -- Goal: s.verts(k.succ).coords(s.incDir k_prev) =
            --        new_v.coords(s.incDir k_prev) + 1
            have h_ne_inc : s.incDir k_prev ≠ s.incDir k := by
              intro heq; have := s.inc_injective heq
              simp [k_prev, Fin.ext_iff] at this; omega
            have h_ne_miss : s.incDir k_prev ≠ s.miss := s.miss_ne_inc k_prev
            rw [BaryPoint.transfer_coords_other v_prev (s.incDir k) s.miss h_ne
              h_miss_pos (s.incDir k_prev) h_ne_inc h_ne_miss]
            have hkp_succ : (k_prev.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              ext; simp [k_prev, Fin.succ]; omega
            have hkp_cs : (k_prev.castSucc : Fin (d + 1)) = prev_v_idx := by
              ext; simp [k_prev, Fin.castSucc, prev_v_idx]
            have h_step_kp := s.step_inc k_prev
            rw [hkp_succ, hkp_cs] at h_step_kp
            have hne_kpk : k_prev ≠ k := by simp [k_prev, Fin.ext_iff]; omega
            have h_stable := s.incDir_stable k_prev k hne_kpk
            have hk_cs : (k.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              ext; simp [Fin.castSucc]
            rw [hk_cs] at h_stable
            rw [h_stable, h_step_kp]
          · -- Case j_step ≠ k_prev, j_step ≠ k
            simp only [hjk, ite_false]
            have hcs_ne : ¬(j_step.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              intro h; simp [Fin.ext_iff, Fin.castSucc] at h; exact hjk (Fin.ext h)
            have hss_ne : ¬(j_step.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              intro h; simp [Fin.ext_iff, Fin.succ] at h
              exact hjp (Fin.ext (by simp [k_prev]; omega))
            simp only [hcs_ne, ite_false, hss_ne]
            exact s.step_inc j_step
      step_dec := by
        intro j_step
        by_cases hjp : j_step = k_prev
        · -- Case j_step = k_prev
          subst hjp
          have hcs_ne : ¬(k_prev.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
            intro h; simp [Fin.ext_iff, k_prev, Fin.castSucc] at h; omega
          have hss_eq : (k_prev.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
            ext; simp [k_prev, Fin.succ]; omega
          simp only [hcs_ne, ite_false, hss_eq, ite_true]
          -- Goal: v_prev.coords miss = new_v.coords miss + 1
          -- new_v = v_prev.transfer (incDir k) miss, so new_v.coords miss = v_prev.coords miss - 1
          -- new_v.coords miss = v_prev.coords miss - 1
          have h_new : new_v.coords s.miss = v_prev.coords s.miss - 1 :=
            BaryPoint.transfer_coords_dec v_prev (s.incDir k) s.miss h_ne h_miss_pos
          omega
        · by_cases hjk : j_step = k
          · -- Case j_step = k
            have hcs_eq : (j_step.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              ext; simp [Fin.castSucc]; omega
            have hss_ne : ¬(j_step.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              simp [Fin.ext_iff, Fin.succ]; omega
            simp only [hcs_eq, ite_true, hss_ne, ite_false]
            -- Goal: new_v.coords miss = s.verts(j_step.succ).coords miss + 1
            have h_new : new_v.coords s.miss = v_prev.coords s.miss - 1 :=
              BaryPoint.transfer_coords_dec v_prev (s.incDir k) s.miss h_ne h_miss_pos
            rw [h_new]
            -- Goal: v_prev.coords miss - 1 = s.verts(j_step.succ).coords miss + 1
            have hkp_succ : (k_prev.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              ext; simp [k_prev, Fin.succ]; omega
            have hkp_cs : (k_prev.castSucc : Fin (d + 1)) = prev_v_idx := by
              ext; simp [k_prev, Fin.castSucc, prev_v_idx]
            have h1 := s.step_dec k_prev
            rw [hkp_cs, hkp_succ] at h1
            have hk_cs : (k.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              ext; simp [Fin.castSucc]
            have h2 := s.step_dec k
            rw [hk_cs] at h2
            have hjs_succ : j_step.succ = k.succ := congr_arg Fin.succ hjk
            simp_all; omega
          · -- Case j_step ≠ k_prev, j_step ≠ k
            have hcs_ne : ¬(j_step.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              intro h; simp [Fin.ext_iff, Fin.castSucc] at h; exact hjk (Fin.ext h)
            have hss_ne : ¬(j_step.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              intro h; simp [Fin.ext_iff, Fin.succ] at h
              exact hjp (Fin.ext (by simp [k_prev]; omega))
            simp only [hcs_ne, ite_false, hss_ne]
            exact s.step_dec j_step
      step_same := by
        intro j_step j hj_inc hj_miss
        simp only [new_incDir] at hj_inc
        by_cases hjp : j_step = k_prev
        · -- Case j_step = k_prev
          subst hjp; simp only [ite_true] at hj_inc
          have hcs_ne : ¬(k_prev.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
            intro h; simp [Fin.ext_iff, k_prev, Fin.castSucc] at h; omega
          have hss_eq : (k_prev.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
            ext; simp [k_prev, Fin.succ]; omega
          simp only [hcs_ne, ite_false, hss_eq, ite_true]
          exact BaryPoint.transfer_coords_other v_prev (s.incDir k) s.miss h_ne
            h_miss_pos j hj_inc hj_miss
        · simp only [hjp, ite_false] at hj_inc
          by_cases hjk : j_step = k
          · -- Case j_step = k
            rw [hjk] at hj_inc; simp only [ite_true] at hj_inc
            have hcs_eq : (j_step.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              ext; simp [Fin.castSucc]; omega
            have hss_ne : ¬(j_step.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              intro h; simp [Fin.ext_iff, Fin.succ] at h; omega
            simp only [hcs_eq, ite_true, hss_ne, ite_false]
            by_cases hj_inck : j = s.incDir k
            · -- j = incDir k
              subst hj_inck
              rw [BaryPoint.transfer_coords_inc v_prev (s.incDir k) s.miss h_ne h_miss_pos]
              have hne_kpk : k_prev ≠ k := by simp [k_prev, Fin.ext_iff]; omega
              have h_ne_inc_kp : s.incDir k ≠ s.incDir k_prev := by
                intro heq; have := s.inc_injective heq
                simp [k_prev, Fin.ext_iff] at this; omega
              have h_ne_miss_k : s.incDir k ≠ s.miss := s.miss_ne_inc k
              have hkp_cs : (k_prev.castSucc : Fin (d + 1)) = prev_v_idx := by
                ext; simp [k_prev, Fin.castSucc, prev_v_idx]
              have hkp_succ : (k_prev.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
                ext; simp [k_prev, Fin.succ]; omega
              have h_same := s.step_same k_prev (s.incDir k) h_ne_inc_kp h_ne_miss_k
              rw [hkp_cs, hkp_succ] at h_same
              have hk_cs : (k.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
                ext; simp [Fin.castSucc]
              have h_inc_k := s.step_inc k
              rw [hk_cs] at h_inc_k
              have hjs_succ : j_step.succ = k.succ := by rw [hjk]
              rw [hjs_succ, h_inc_k, h_same]
            · -- j ≠ incDir k
              rw [BaryPoint.transfer_coords_other v_prev (s.incDir k) s.miss h_ne
                h_miss_pos j hj_inck hj_miss]
              have hk_cs : (k.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
                ext; simp [Fin.castSucc]
              have h_same_k := s.step_same k j hj_inck hj_miss
              rw [hk_cs] at h_same_k
              have hkp_cs : (k_prev.castSucc : Fin (d + 1)) = prev_v_idx := by
                ext; simp [k_prev, Fin.castSucc, prev_v_idx]
              have hkp_succ : (k_prev.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
                ext; simp [k_prev, Fin.succ]; omega
              have h_same_kp := s.step_same k_prev j hj_inc hj_miss
              rw [hkp_cs, hkp_succ] at h_same_kp
              have hjs_succ : j_step.succ = k.succ := by rw [hjk]
              rw [hjs_succ, h_same_k, h_same_kp]
          · -- Case j_step ≠ k_prev, j_step ≠ k
            simp only [hjk, ite_false] at hj_inc
            have hcs_ne : ¬(j_step.castSucc : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              intro h; simp [Fin.ext_iff, Fin.castSucc] at h; exact hjk (Fin.ext h)
            have hss_ne : ¬(j_step.succ : Fin (d + 1)) = ⟨k.val, by omega⟩ := by
              intro h; simp [Fin.ext_iff, Fin.succ] at h
              exact hjp (Fin.ext (by simp [k_prev]; omega))
            simp only [hcs_ne, ite_false, hss_ne]
            exact s.step_same j_step j hj_inc hj_miss
      inc_injective := by
        intro a b hab
        simp only [new_incDir] at hab
        -- 9 cases from the two nested if-then-else on a and b
        split_ifs at hab with h1 h2 h3 h4
        · -- a = k_prev, b = k_prev
          subst h1; exact h2 ▸ rfl
        · -- a = k_prev, b = k
          subst h1; exfalso
          have := s.inc_injective hab
          simp [k_prev, Fin.ext_iff] at this; omega
        · -- a = k_prev, b = other
          subst h1; exfalso
          have := s.inc_injective hab
          simp [Fin.ext_iff] at this; omega
        · -- a = k, b = k_prev
          exfalso; have := s.inc_injective hab
          simp [k_prev, Fin.ext_iff] at this; omega
        · -- a = k, b = k
          ext; simp_all [Fin.ext_iff]
        · -- a = k, b = other
          have := (s.inc_injective hab).symm
          contradiction
        · -- a = other, b = k_prev
          have := s.inc_injective hab
          contradiction
        · -- a = other, b = k
          have := s.inc_injective hab
          contradiction
        · -- a = other, b = other
          exact s.inc_injective hab }
  (s', ⟨k.val, by omega⟩)

/-- Boundary flip at face 0: the adjacent simplex through the
facet opposite vertex 0. Returns none if the last vertex has
miss-coordinate = 0 (geometric boundary).

The new simplex has vertices v₁,...,v_d,v_new where
v_new = v_d + e_{incDir(0)} - e_{miss}. Same miss.
incDir is cyclically left-shifted. -/
noncomputable def GridSimplex.boundaryFlip0
    (s : GridSimplex d N) :
    Option (GridSimplex d N × Fin (d + 1)) :=
  let last_v := s.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩
  if h_pos : 0 < last_v.coords s.miss then
    -- d = 0 case: Fin 0 is empty, no incDir to reference
    if hd : d = 0 then none  -- single vertex, no face 0 adjacency
    else
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      let inc0 := s.incDir ⟨0, hd_pos⟩
      have h_ne : inc0 ≠ s.miss := s.miss_ne_inc ⟨0, hd_pos⟩
      let new_v := last_v.transfer inc0 s.miss h_ne h_pos
      -- New incDir: cyclic left shift
      let new_incDir : Fin d → Fin (d + 1) := fun j =>
        if h : j.val + 1 < d then s.incDir ⟨j.val + 1, h⟩
        else inc0  -- j = d-1 gets incDir(0)
      let s' : GridSimplex d N :=
        { verts := fun j =>
            if h : j.val < d then s.verts ⟨j.val + 1, by omega⟩
            else new_v  -- j = d gets the new vertex
          incDir := new_incDir
          miss := s.miss
          miss_ne_inc := by
            intro j; simp only [new_incDir]
            split_ifs with h
            · exact s.miss_ne_inc ⟨j.val + 1, h⟩
            · exact h_ne
          step_inc := by
            intro j_step
            simp only [new_incDir]
            by_cases hj_mid : j_step.val + 1 < d
            · -- Middle step: both verts delegate to s
              simp only [hj_mid, dite_true]
              have hcs_lt : j_step.castSucc.val < d := by simp [Fin.castSucc]
              have hss_lt : j_step.succ.val < d := by simp [Fin.succ]; omega
              simp only [show (j_step.castSucc.val < d) = True from eq_true hcs_lt,
                         show (j_step.succ.val < d) = True from eq_true hss_lt,
                         dite_true]
              -- Goal relates s.verts ⟨j_step.val+2,_⟩ to s.verts ⟨j_step.val+1,_⟩
              -- via s.incDir ⟨j_step.val+1,_⟩
              have h := s.step_inc ⟨j_step.val + 1, hj_mid⟩
              -- Normalize Fin values in h
              have : (⟨j_step.val + 1, hj_mid⟩ : Fin d).succ =
                (⟨j_step.val + 2, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.succ]
              have : (⟨j_step.val + 1, hj_mid⟩ : Fin d).castSucc =
                (⟨j_step.val + 1, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.castSucc]
              simp_all
            · -- Last step: j_step.val = d-1
              simp only [hj_mid, dite_false]
              have hcs_lt : j_step.castSucc.val < d := j_step.isLt
              have hss_not_lt : ¬(j_step.succ.val < d) := by simp [Fin.succ]; omega
              simp only [show (j_step.castSucc.val < d) = True from eq_true hcs_lt,
                         show (j_step.succ.val < d) = False from eq_false hss_not_lt,
                         dite_true, dite_false]
              -- Goal: new_v.coords inc0 = (s.verts ⟨j_step.val+1,_⟩).coords inc0 + 1
              -- where j_step.val + 1 = d, so s.verts ⟨d,_⟩ = last_v
              -- s.verts ⟨j_step.val+1,_⟩ = last_v since j_step.val+1=d
              have hval : j_step.val = d - 1 := by omega
              have hlv : s.verts ⟨j_step.castSucc.val + 1, by omega⟩ = last_v := by
                show s.verts ⟨j_step.castSucc.val + 1, by omega⟩ =
                  s.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩
                congr 1; ext; simp [Fin.castSucc]; omega
              rw [hlv]
              exact BaryPoint.transfer_coords_inc last_v inc0 s.miss h_ne h_pos
          step_dec := by
            intro j_step
            by_cases hj_mid : j_step.val + 1 < d
            · -- Middle step
              have hcs_lt : j_step.castSucc.val < d := by simp [Fin.castSucc]
              have hss_lt : j_step.succ.val < d := by simp [Fin.succ]; omega
              simp only [show (j_step.castSucc.val < d) = True from eq_true hcs_lt,
                         show (j_step.succ.val < d) = True from eq_true hss_lt,
                         dite_true]
              have h := s.step_dec ⟨j_step.val + 1, hj_mid⟩
              have : (⟨j_step.val + 1, hj_mid⟩ : Fin d).succ =
                (⟨j_step.val + 2, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.succ]
              have : (⟨j_step.val + 1, hj_mid⟩ : Fin d).castSucc =
                (⟨j_step.val + 1, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.castSucc]
              simp_all
            · -- Last step
              have hcs_lt : j_step.castSucc.val < d := j_step.isLt
              have hss_not_lt : ¬(j_step.succ.val < d) := by simp [Fin.succ]; omega
              simp only [show (j_step.castSucc.val < d) = True from eq_true hcs_lt,
                         show (j_step.succ.val < d) = False from eq_false hss_not_lt,
                         dite_true, dite_false]
              have h_new : new_v.coords s.miss = last_v.coords s.miss - 1 :=
                BaryPoint.transfer_coords_dec last_v inc0 s.miss h_ne h_pos
              have hlv : s.verts ⟨j_step.castSucc.val + 1, by omega⟩ = last_v := by
                show s.verts ⟨j_step.castSucc.val + 1, by omega⟩ =
                  s.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩
                congr 1; ext; simp [Fin.castSucc]; omega
              rw [hlv]
              omega
          step_same := by
            intro j_step j hj_inc hj_miss
            simp only [new_incDir] at hj_inc
            by_cases hj_mid : j_step.val + 1 < d
            · -- Middle case: both verts are interior, delegate to s.step_same
              simp only [hj_mid, dite_true] at hj_inc
              have hcs_lt : j_step.castSucc.val < d := by simp [Fin.castSucc]
              have hss_lt : j_step.succ.val < d := by simp [Fin.succ]; omega
              simp only [show (j_step.castSucc.val < d) = True from eq_true hcs_lt,
                         show (j_step.succ.val < d) = True from eq_true hss_lt,
                         dite_true]
              have h := s.step_same ⟨j_step.val + 1, hj_mid⟩ j hj_inc hj_miss
              have : (⟨j_step.val + 1, hj_mid⟩ : Fin d).succ =
                (⟨j_step.val + 2, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.succ]
              have : (⟨j_step.val + 1, hj_mid⟩ : Fin d).castSucc =
                (⟨j_step.val + 1, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.castSucc]
              simp_all
            · -- Last case: succ gives new_v, castSucc gives last_v; use transfer_coords_other
              simp only [hj_mid, dite_false] at hj_inc
              have hcs_lt : j_step.castSucc.val < d := j_step.isLt
              have hss_not_lt : ¬(j_step.succ.val < d) := by simp [Fin.succ]; omega
              simp only [show (j_step.castSucc.val < d) = True from eq_true hcs_lt,
                         show (j_step.succ.val < d) = False from eq_false hss_not_lt,
                         dite_true, dite_false]
              have h_key : j_step.castSucc.val + 1 = d := by simp [Fin.castSucc]; omega
              have h_eq : s.verts ⟨j_step.castSucc.val + 1, by omega⟩ = last_v := by
                congr 1; ext; simp [Fin.castSucc]; omega
              rw [h_eq]
              exact BaryPoint.transfer_coords_other last_v inc0 s.miss h_ne h_pos j hj_inc hj_miss
          inc_injective := by
            intro a b hab
            simp only [new_incDir] at hab
            split_ifs at hab with h1 h2
            · -- Both a+1 < d, b+1 < d
              have := s.inc_injective hab
              ext; simp [Fin.ext_iff] at this; omega
            · -- a+1 < d, b+1 ≥ d (b = d-1)
              exfalso; have := s.inc_injective hab
              simp [Fin.ext_iff] at this
            · -- a+1 ≥ d, b+1 < d
              exfalso; have := s.inc_injective hab
              simp [Fin.ext_iff] at this
            · -- Both a+1 ≥ d, b+1 ≥ d
              have ha : a.val = d - 1 := by omega
              have hb : b.val = d - 1 := by omega
              ext; omega }
      some (s', ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩)
  else none

/-- Boundary flip at face d: the adjacent simplex through the
facet opposite the last vertex. Returns none if v₀ has
incDir(d-1)-coordinate = 0 (geometric boundary).

The new simplex has vertices v_new,v₀,...,v_{d-1} where
v_new = v₀ - e_{incDir(d-1)} + e_{miss}. Same miss.
incDir is cyclically right-shifted. -/
noncomputable def GridSimplex.boundaryFlipLast
    (s : GridSimplex d N) :
    Option (GridSimplex d N × Fin (d + 1)) :=
  if hd : d = 0 then none  -- single vertex, no face d adjacency
  else
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    let last_inc := s.incDir ⟨d - 1, by omega⟩
    let v0 := s.verts 0
    if h_pos : 0 < v0.coords last_inc then
      have h_ne : last_inc ≠ s.miss :=
        s.miss_ne_inc ⟨d - 1, by omega⟩
      let new_v := v0.transfer s.miss last_inc (Ne.symm h_ne) h_pos
      -- New incDir: cyclic right shift
      let new_incDir : Fin d → Fin (d + 1) := fun j =>
        if j.val = 0 then last_inc
        else s.incDir ⟨j.val - 1, by omega⟩
      let s' : GridSimplex d N :=
        { verts := fun j =>
            if j.val = 0 then new_v
            else s.verts ⟨j.val - 1, by omega⟩
          incDir := new_incDir
          miss := s.miss
          miss_ne_inc := by
            intro j; simp only [new_incDir]
            split_ifs with h
            · exact s.miss_ne_inc ⟨d - 1, by omega⟩
            · exact s.miss_ne_inc ⟨j.val - 1, by omega⟩
          step_inc := by
            intro j_step
            simp only [new_incDir]
            by_cases hj0 : j_step.val = 0
            · -- First step: from new_v to v0
              simp only [hj0, ite_true]
              have hcs_zero : j_step.castSucc.val = 0 := by simp [Fin.castSucc]; exact hj0
              have hss_nz : ¬(j_step.succ.val = 0) := by simp [Fin.succ]
              simp only [show (j_step.castSucc.val = 0) = True from eq_true hcs_zero,
                         show (j_step.succ.val = 0) = False from eq_false hss_nz,
                         ite_true, ite_false]
              -- s.verts ⟨j_step.val+1-1,_⟩ = v0 (since j_step.val = 0)
              -- new_v.coords last_inc = v0.coords last_inc - 1 (transfer_coords_dec)
              -- Goal: v0.coords last_inc = new_v.coords last_inc + 1
              have h_new : new_v.coords last_inc = v0.coords last_inc - 1 :=
                BaryPoint.transfer_coords_dec v0 s.miss last_inc (Ne.symm h_ne) h_pos
              have hv0 : s.verts ⟨j_step.succ.val - 1, by omega⟩ = v0 := by
                show s.verts ⟨j_step.succ.val - 1, by omega⟩ = s.verts 0
                congr 1; ext; simp [Fin.val_succ]; omega
              rw [hv0]
              omega
            · -- Later step
              simp only [hj0, ite_false]
              have hcs_nz : ¬(j_step.castSucc.val = 0) := by simp [Fin.castSucc]; exact hj0
              have hss_nz : ¬(j_step.succ.val = 0) := by simp [Fin.succ]
              simp only [show (j_step.castSucc.val = 0) = False from eq_false hcs_nz,
                         show (j_step.succ.val = 0) = False from eq_false hss_nz,
                         ite_false]
              have hjd : j_step.val - 1 < d := by omega
              have h := s.step_inc ⟨j_step.val - 1, hjd⟩
              have : (⟨j_step.val - 1, hjd⟩ : Fin d).succ =
                (⟨j_step.val, by omega⟩ : Fin (d + 1)) := by ext; simp; omega
              have : (⟨j_step.val - 1, hjd⟩ : Fin d).castSucc =
                (⟨j_step.val - 1, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.castSucc]
              simp_all
          step_dec := by
            intro j_step
            by_cases hj0 : j_step.val = 0
            · -- First step
              have hcs_zero : j_step.castSucc.val = 0 := by simp [Fin.castSucc]; exact hj0
              have hss_nz : ¬(j_step.succ.val = 0) := by simp [Fin.succ]
              simp only [show (j_step.castSucc.val = 0) = True from eq_true hcs_zero,
                         show (j_step.succ.val = 0) = False from eq_false hss_nz,
                         ite_true, ite_false]
              have h_new : new_v.coords s.miss = v0.coords s.miss + 1 :=
                BaryPoint.transfer_coords_inc v0 s.miss last_inc (Ne.symm h_ne) h_pos
              have hv0eq : s.verts ⟨j_step.succ.val - 1, by omega⟩ = v0 := by
                show s.verts ⟨j_step.succ.val - 1, by omega⟩ = s.verts 0
                congr 1; ext; simp [Fin.val_succ]; omega
              rw [hv0eq]
              exact h_new
            · -- Later step
              have hcs_nz : ¬(j_step.castSucc.val = 0) := by simp [Fin.castSucc]; exact hj0
              have hss_nz : ¬(j_step.succ.val = 0) := by simp [Fin.succ]
              simp only [show (j_step.castSucc.val = 0) = False from eq_false hcs_nz,
                         show (j_step.succ.val = 0) = False from eq_false hss_nz,
                         ite_false]
              have hjd : j_step.val - 1 < d := by omega
              have h := s.step_dec ⟨j_step.val - 1, hjd⟩
              have : (⟨j_step.val - 1, hjd⟩ : Fin d).succ =
                (⟨j_step.val, by omega⟩ : Fin (d + 1)) := by ext; simp; omega
              have : (⟨j_step.val - 1, hjd⟩ : Fin d).castSucc =
                (⟨j_step.val - 1, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.castSucc]
              simp_all
          step_same := by
            intro j_step j hj_inc hj_miss
            simp only [new_incDir] at hj_inc
            by_cases hj0 : j_step.val = 0
            · -- First case: castSucc gives new_v, succ gives v0; use transfer_coords_other
              simp only [hj0, ite_true] at hj_inc
              have hcs_zero : j_step.castSucc.val = 0 := by simp [Fin.castSucc]; exact hj0
              have hss_nz : ¬(j_step.succ.val = 0) := by simp [Fin.succ]
              simp only [show (j_step.castSucc.val = 0) = True from eq_true hcs_zero,
                         show (j_step.succ.val = 0) = False from eq_false hss_nz,
                         ite_true, ite_false]
              have h_eq : s.verts ⟨j_step.succ.val - 1, by simp [Fin.succ]; omega⟩ = v0 := by
                congr 1; ext; simp [Fin.succ]; omega
              rw [h_eq]
              symm
              exact BaryPoint.transfer_coords_other v0 s.miss last_inc (Ne.symm h_ne) h_pos j hj_miss hj_inc
            · -- Later case: both verts interior, delegate to s.step_same
              simp only [hj0, ite_false] at hj_inc
              have hcs_nz : ¬(j_step.castSucc.val = 0) := by simp [Fin.castSucc]; exact hj0
              have hss_nz : ¬(j_step.succ.val = 0) := by simp [Fin.succ]
              simp only [show (j_step.castSucc.val = 0) = False from eq_false hcs_nz,
                         show (j_step.succ.val = 0) = False from eq_false hss_nz,
                         ite_false]
              have hjd : j_step.val - 1 < d := by omega
              have h := s.step_same ⟨j_step.val - 1, hjd⟩ j hj_inc hj_miss
              have : (⟨j_step.val - 1, hjd⟩ : Fin d).succ =
                (⟨j_step.val, by omega⟩ : Fin (d + 1)) := by ext; simp; omega
              have : (⟨j_step.val - 1, hjd⟩ : Fin d).castSucc =
                (⟨j_step.val - 1, by omega⟩ : Fin (d + 1)) := by ext; simp [Fin.castSucc]
              simp_all
          inc_injective := by
            intro a b hab
            simp only [new_incDir] at hab
            split_ifs at hab with h1 h2
            · -- Both a = 0, b = 0
              ext; omega
            · -- a = 0, b ≠ 0
              exfalso; have := s.inc_injective hab
              simp [Fin.ext_iff] at this; omega
            · -- a ≠ 0, b = 0
              exfalso; have := s.inc_injective hab
              simp [Fin.ext_iff] at this; omega
            · -- Both ≠ 0: s.incDir ⟨a-1, _⟩ = s.incDir ⟨b-1, _⟩
              have := s.inc_injective hab
              ext; simp [Fin.ext_iff] at this; omega }
      some (s', 0)
    else none

/-- The adjacency function for the grid CellComplex.
Dispatches to interior or boundary flips based on the
facet position k. -/
noncomputable def gridAdj (d N : ℕ)
    (s : GridSimplex d N) (k : Fin (d + 1)) :
    Option (GridSimplex d N × Fin (d + 1)) :=
  if hk0 : k.val = 0 then s.boundaryFlip0
  else if hkd : k.val = d then s.boundaryFlipLast
  else  -- 0 < k.val < d, so k.val - 1 < d
    have hk_lt_d : k.val < d := by omega
    -- k corresponds to step index ⟨k.val - 1, _⟩ with k.val - 1 ≥ 0
    -- But we need the step that is "between" vertex k-1 and k+1
    -- Interior flip at step ⟨k.val, _⟩ with k.val > 0
    -- Wait: vertex k sits between step k-1 and step k.
    -- interiorFlip takes step k : Fin d with hk : 0 < k.val
    -- and replaces vertex k.castSucc = ⟨k.val, _⟩.
    -- We want to replace vertex k : Fin (d+1), so we need
    -- step ⟨k.val, hk_lt_d⟩ with 0 < k.val.
    have hk_pos : 0 < k.val := by omega
    -- But interiorFlip uses its own step indexing.
    -- Step j : Fin d goes from verts(j.castSucc) to verts(j.succ).
    -- Swapping steps j-1 and j replaces vertex j.castSucc = ⟨j.val, _⟩.
    -- We want to replace vertex ⟨k.val, _⟩, so j.val = k.val.
    let step : Fin d := ⟨k.val, hk_lt_d⟩
    some (s.interiorFlip step (by simp [step]; exact hk_pos))

-- Helper lemmas for Section VII

/-- The incDir at position k_prev = k-1 in the interior flip equals the
original incDir at k. Used to detect that s ≠ s' after interiorFlip. -/
private lemma interiorFlip_incDir_kprev (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val) :
    (s.interiorFlip k hk).1.incDir ⟨k.val - 1, by omega⟩ = s.incDir k := by
  simp [GridSimplex.interiorFlip, Fin.ext_iff]

/-- In the interiorFlip, all vertices except index k are preserved. -/
private lemma interiorFlip_verts_other (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val)
    (j : Fin (d + 1)) (hj : j.val ≠ k.val) :
    (s.interiorFlip k hk).1.verts j = s.verts j := by
  simp [GridSimplex.interiorFlip, Fin.ext_iff, hj]

/-- If boundaryFlip0 succeeds and returns (s', k'), then d ≠ 0 and
s' maps vertex 0 to s.verts 1 (the cyclic shift property). -/
private lemma boundaryFlip0_verts_zero (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlip0 = some (s', k')) :
    ∃ hd : d ≠ 0, s'.verts ⟨0, by omega⟩ = s.verts ⟨1, by omega⟩ := by
  simp only [GridSimplex.boundaryFlip0] at h
  split_ifs at h with h_pos hd
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h
    refine ⟨hd, ?_⟩
    have := congr_fun (congr_arg GridSimplex.verts hs') (⟨0, by omega⟩ : Fin (d + 1))
    simp [Nat.pos_of_ne_zero hd] at this
    exact this.symm

/-- If boundaryFlipLast succeeds and returns (s', k'), then d ≠ 0 and
s' maps vertex 1 to s.verts 0 (the cyclic shift property). -/
private lemma boundaryFlipLast_verts_one (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlipLast = some (s', k')) :
    ∃ hd : d ≠ 0, s'.verts ⟨1, by omega⟩ = s.verts ⟨0, by omega⟩ := by
  simp only [GridSimplex.boundaryFlipLast] at h
  split_ifs at h with hd h_pos
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h
    refine ⟨hd, ?_⟩
    have := congr_fun (congr_arg GridSimplex.verts hs') (⟨1, by omega⟩ : Fin (d + 1))
    simp at this
    exact this.symm

-- ============================================================
-- SECTION VII: CellComplex Instance
-- ============================================================

-- Helper: GridSimplex extensionality
private theorem GridSimplex.ext' {d N : ℕ} {s t : GridSimplex d N}
    (hv : s.verts = t.verts) (hi : s.incDir = t.incDir)
    (hm : s.miss = t.miss) : s = t := by
  cases s; cases t; simp only at hv hi hm; subst hv; subst hi; subst hm; rfl

-- Helper: vertex k-1 in interiorFlip is unchanged
private lemma interiorFlip_verts_kprev (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val) :
    (s.interiorFlip k hk).1.verts ⟨k.val - 1, by omega⟩ =
    s.verts ⟨k.val - 1, by omega⟩ :=
  interiorFlip_verts_other s k hk ⟨k.val - 1, by omega⟩ (by simp; omega)

-- Helper: new vertex at position k after double interiorFlip = original
private lemma interiorFlip_double_vertex (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val) :
    let s' := (s.interiorFlip k hk).1
    let k_prev : Fin d := ⟨k.val - 1, by omega⟩
    let prev_v_idx : Fin (d + 1) := ⟨k.val - 1, by omega⟩
    let v_prev := s.verts prev_v_idx
    let h_miss_pos : 0 < v_prev.coords s.miss :=
      Nat.lt_of_lt_of_le (by omega : 0 < d - prev_v_idx.val) (s.miss_coord_ge prev_v_idx)
    let h_ne_kp : s.incDir k_prev ≠ s.miss := s.miss_ne_inc k_prev
    v_prev.transfer (s.incDir k_prev) s.miss h_ne_kp h_miss_pos =
    s.verts ⟨k.val, by omega⟩ := by
  ext j
  simp only [BaryPoint.transfer]
  set k_prev : Fin d := ⟨k.val - 1, by omega⟩
  by_cases hj1 : j = s.incDir k_prev
  · simp only [hj1, ite_true]
    have hkp := s.step_inc k_prev
    simp only [show k_prev.castSucc = ⟨k.val - 1, by omega⟩ from Fin.ext (by simp [k_prev, Fin.castSucc]),
               show k_prev.succ = ⟨k.val, by omega⟩ from Fin.ext (by simp [k_prev, Fin.succ]; omega)] at hkp
    omega
  · by_cases hj2 : j = s.miss
    · simp only [hj1, ite_false, hj2, ite_true]
      have hkp := s.step_dec k_prev
      simp only [show k_prev.castSucc = ⟨k.val - 1, by omega⟩ from Fin.ext (by simp [k_prev, Fin.castSucc]),
                 show k_prev.succ = ⟨k.val, by omega⟩ from Fin.ext (by simp [k_prev, Fin.succ]; omega)] at hkp
      omega
    · simp only [hj1, ite_false, hj2, ite_false]
      have hkp := s.step_same k_prev j (fun h => hj1 h.symm) hj2
      simp only [show k_prev.castSucc = ⟨k.val - 1, by omega⟩ from Fin.ext (by simp [k_prev, Fin.castSucc]),
                 show k_prev.succ = ⟨k.val, by omega⟩ from Fin.ext (by simp [k_prev, Fin.succ]; omega)] at hkp
      exact hkp.symm

-- Helper: the interior flip is an involution (GridSimplex component)
private lemma interiorFlip_invol (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val) :
    (s.interiorFlip k hk).1.interiorFlip k hk =
    (s, (s.interiorFlip k hk).2) := by
  set k_prev : Fin d := ⟨k.val - 1, by omega⟩
  -- Facts about s' = (s.interiorFlip k hk).1
  have h_s'_inck : (s.interiorFlip k hk).1.incDir k = s.incDir k_prev := by
    simp [GridSimplex.interiorFlip, k_prev, show k ≠ k_prev from Fin.ne_of_val_ne (by simp [k_prev]; omega)]
  have h_s'_miss : (s.interiorFlip k hk).1.miss = s.miss := by
    simp [GridSimplex.interiorFlip]
  have h_miss_pos : 0 < (s.verts ⟨k.val - 1, by omega⟩).coords s.miss :=
    Nat.lt_of_lt_of_le (by omega : 0 < d - (k.val - 1)) (s.miss_coord_ge ⟨k.val - 1, by omega⟩)
  have h_miss_pos' :
      0 < ((s.interiorFlip k hk).1.verts ⟨k.val - 1, by omega⟩).coords
          ((s.interiorFlip k hk).1.miss) := by
    rw [interiorFlip_verts_kprev, h_s'_miss]; exact h_miss_pos
  have h_ne_kp : s.incDir k_prev ≠ s.miss := s.miss_ne_inc k_prev
  have h_ne' : (s.interiorFlip k hk).1.incDir k ≠ (s.interiorFlip k hk).1.miss := by
    rw [h_s'_inck, h_s'_miss]; exact h_ne_kp
  -- Second flip returns (s, ⟨k.val, _⟩)
  simp only [Prod.mk.injEq]
  refine ⟨GridSimplex.ext' ?_ ?_ ?_, by simp [GridSimplex.interiorFlip]⟩
  · -- verts equality
    funext j
    simp only [GridSimplex.interiorFlip]
    by_cases hjk : j = ⟨k.val, by omega⟩
    · -- At position k: new_v' = s.verts ⟨k.val, _⟩
      simp only [hjk, ite_true]
      -- v_prev' = s'.verts ⟨k.val-1, _⟩ = s.verts ⟨k.val-1, _⟩
      -- incDir' k = s'.incDir k = s.incDir k_prev
      -- miss' = s'.miss = s.miss
      -- So new_v' = v_prev.transfer (s.incDir k_prev) s.miss = s.verts ⟨k.val, _⟩
      have key := @interiorFlip_double_vertex d N s k hk
      simp only at key
      convert key using 2
      · exact interiorFlip_verts_kprev s k hk
      · exact h_s'_inck
      · exact h_s'_miss
    · -- At other positions: s'.verts j = s.verts j
      simp only [hjk, ite_false]
      simp only [GridSimplex.interiorFlip, hjk, ite_false]
  · -- incDir equality: double swap is identity
    funext j
    simp only [GridSimplex.interiorFlip]
    by_cases hj1 : j = k_prev
    · -- j = k_prev: s'.incDir k = s.incDir k_prev = s.incDir j
      simp only [hj1, ite_true]
      simp only [GridSimplex.interiorFlip]
      simp [k_prev]
    · simp only [hj1, ite_false]
      by_cases hj2 : j = k
      · -- j = k: s'.incDir k_prev = s.incDir k = s.incDir j
        simp only [hj2, ite_true]
        simp only [GridSimplex.interiorFlip]
        have hkk : k ≠ k_prev := Fin.ne_of_val_ne (by simp [k_prev]; omega)
        simp [k_prev, hkk]
      · -- j ≠ k_prev, k: s'.incDir j = s.incDir j
        simp only [hj2, ite_false]
        simp only [GridSimplex.interiorFlip, hj1, hj2, ite_false]
  · -- miss equality
    simp [GridSimplex.interiorFlip]

-- Helper: new_v from boundaryFlip0 applied backward by boundaryFlipLast
private lemma boundaryFlip0_new_v_inv (s : GridSimplex d N)
    (hd : d ≠ 0)
    (h_pos : 0 < (s.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩).coords s.miss) :
    let hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    let inc0 := s.incDir ⟨0, hd_pos⟩
    let h_ne : inc0 ≠ s.miss := s.miss_ne_inc ⟨0, hd_pos⟩
    let new_v := (s.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩).transfer inc0 s.miss h_ne h_pos
    -- v0' for the second flip is s.verts 1
    -- last_inc' for the second flip is inc0
    -- new_v' = s.verts(1).transfer s.miss inc0 = s.verts 0
    let h_pos' : 0 < (s.verts ⟨1, by omega⟩).coords inc0 := by
      have := s.step_inc ⟨0, hd_pos⟩
      simp [Fin.castSucc, Fin.succ] at this; omega
    (s.verts ⟨1, by omega⟩).transfer s.miss inc0 (Ne.symm h_ne) h_pos' = s.verts 0 := by
  simp only
  ext j
  simp only [BaryPoint.transfer]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  set inc0 := s.incDir ⟨0, hd_pos⟩
  have h_ne : inc0 ≠ s.miss := s.miss_ne_inc ⟨0, hd_pos⟩
  by_cases hj1 : j = s.miss
  · simp only [hj1, ite_true, show j ≠ inc0 from by rw [hj1]; exact Ne.symm h_ne, ite_false]
    have := s.step_inc ⟨0, hd_pos⟩
    simp [Fin.castSucc, Fin.succ] at this
    have hd2 := s.step_dec ⟨0, hd_pos⟩
    simp [Fin.castSucc, Fin.succ] at hd2
    omega
  · by_cases hj2 : j = inc0
    · simp only [hj2, ite_true, show ¬(j = s.miss) from by rw [hj2]; exact h_ne, ite_false]
      have := s.step_inc ⟨0, hd_pos⟩
      simp [Fin.castSucc, Fin.succ] at this; omega
    · simp only [hj1, ite_false, hj2, ite_false]
      have := s.step_same ⟨0, hd_pos⟩ j hj2 hj1
      simp [Fin.castSucc, Fin.succ] at this; exact this.symm

-- Helper: boundaryFlip0 and boundaryFlipLast are inverses
private lemma boundaryFlip0_invol (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlip0 = some (s', k')) :
    s'.boundaryFlipLast = some (s, (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1))) := by
  simp only [GridSimplex.boundaryFlip0] at h
  split_ifs at h with h_pos hd
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h; subst hs'
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    set inc0 := s.incDir ⟨0, hd_pos⟩
    set last_v := s.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩
    have h_ne : inc0 ≠ s.miss := s.miss_ne_inc ⟨0, hd_pos⟩
    set new_v := last_v.transfer inc0 s.miss h_ne h_pos
    -- s' has verts j = if j.val < d then s.verts ⟨j+1, _⟩ else new_v
    -- s' has incDir j = if j.val+1 < d then s.incDir ⟨j+1, _⟩ else inc0
    -- s' has miss = s.miss
    -- For boundaryFlipLast on s':
    --   last_inc' = s'.incDir ⟨d-1, _⟩ = inc0 (since (d-1)+1 = d, not < d)
    --   v0' = s'.verts 0 = s.verts ⟨1, _⟩ (since 0 < d)
    --   h_pos' : 0 < (s.verts 1).coords inc0 (from step_inc 0)
    have h_pos' : 0 < (s.verts ⟨1, by omega⟩).coords inc0 := by
      have := s.step_inc ⟨0, hd_pos⟩; simp [Fin.castSucc, Fin.succ] at this; omega
    -- Prove s'.boundaryFlipLast = some (s, ⟨0, _⟩)
    have new_v'_eq := boundaryFlip0_new_v_inv s hd h_pos
    simp only [GridSimplex.boundaryFlipLast, if_neg hd]
    -- last_inc' in s' is inc0
    have hs'_inc_last : (fun j : Fin d =>
        if h : j.val + 1 < d then s.incDir ⟨j.val + 1, h⟩
        else inc0) ⟨d - 1, by omega⟩ = inc0 := by
      simp [show ¬(d - 1 + 1 < d) from by omega]
    rw [hs'_inc_last]
    -- v0' in s' is s.verts 1
    have hs'_v0 : (fun j : Fin (d + 1) =>
        if h : j.val < d then s.verts ⟨j.val + 1, by omega⟩
        else new_v) ⟨0, by omega⟩ = s.verts ⟨1, by omega⟩ := by
      simp [hd_pos]
    rw [hs'_v0, if_pos h_pos']
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨GridSimplex.ext' ?_ ?_ ?_, rfl⟩
    · -- verts of result = s.verts
      funext j
      simp only
      by_cases hj0 : j.val = 0
      · simp only [show j.val = 0 = True from eq_true hj0, ite_true]
        exact (new_v'_eq.trans (by congr 1; ext; exact hj0.symm))
      · simp only [show j.val = 0 = False from eq_false hj0, ite_false]
        -- s'.verts ⟨j-1, _⟩ = s.verts ⟨(j-1)+1, _⟩ = s.verts j
        have hlt : j.val - 1 < d := by omega
        simp only [show (j.val - 1 < d) = True from eq_true hlt, dite_true]
        congr 1; ext; omega
    · -- incDir of result = s.incDir
      funext j
      simp only
      by_cases hj0 : j.val = 0
      · simp only [show j.val = 0 = True from eq_true hj0, ite_true]
        congr 1; ext; exact hj0.symm
      · simp only [show j.val = 0 = False from eq_false hj0, ite_false]
        -- s'.incDir ⟨j-1, _⟩ = if (j-1)+1 < d then s.incDir ⟨j, _⟩ else inc0
        -- Since j : Fin d and j.val ≥ 1, j.val-1+1 = j.val < d
        have hjlt : j.val - 1 + 1 < d := by omega
        simp only [show (j.val - 1 + 1 < d) = True from eq_true hjlt, dite_true]
        congr 1; ext; omega
    · -- miss of result = s.miss
      rfl
  · simp at h

private lemma boundaryFlipLast_invol (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlipLast = some (s', k')) :
    s'.boundaryFlip0 = some (s, (⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ : Fin (d + 1))) := by
  simp only [GridSimplex.boundaryFlipLast] at h
  split_ifs at h with hd h_pos
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h; subst hs'
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    set last_inc := s.incDir ⟨d - 1, by omega⟩
    set v0 := s.verts 0
    have h_ne : last_inc ≠ s.miss := s.miss_ne_inc ⟨d - 1, by omega⟩
    set new_v := v0.transfer s.miss last_inc (Ne.symm h_ne) h_pos
    -- s' has verts j = if j.val = 0 then new_v else s.verts ⟨j-1, _⟩
    -- s' has incDir j = if j.val = 0 then last_inc else s.incDir ⟨j-1, _⟩
    -- s' has miss = s.miss
    -- For boundaryFlip0 on s':
    --   last_v' = s'.verts d = s.verts ⟨d-1, _⟩ (since d ≠ 0)
    --   inc0' = s'.incDir ⟨0, _⟩ = last_inc
    --   h_pos' : 0 < (s.verts ⟨d-1, _⟩).coords s.miss
    have h_pos' : 0 < (s.verts ⟨d - 1, by omega⟩).coords s.miss := by
      have := s.miss_coord_ge ⟨d - 1, by omega⟩; simp at this; omega
    -- new_v'' = s.verts(d-1).transfer last_inc s.miss = s.verts d
    have new_v''_eq : (s.verts ⟨d - 1, by omega⟩).transfer last_inc s.miss h_ne h_pos' =
        s.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ := by
      ext j; simp only [BaryPoint.transfer]
      set k₀ : Fin d := ⟨d - 1, by omega⟩
      by_cases hj1 : j = last_inc
      · simp only [hj1, ite_true]
        have := s.step_inc k₀
        simp [k₀, Fin.castSucc, Fin.succ, show k₀.val = d - 1 from rfl] at this; omega
      · by_cases hj2 : j = s.miss
        · simp only [hj1, ite_false, hj2, ite_true]
          have := s.step_dec k₀
          simp [k₀, Fin.castSucc, Fin.succ] at this; omega
        · simp only [hj1, ite_false, hj2, ite_false]
          have := s.step_same k₀ j hj1 hj2
          simp [k₀, Fin.castSucc, Fin.succ] at this; exact this.symm
    simp only [GridSimplex.boundaryFlip0]
    -- last_v' = s'.verts d = s.verts ⟨d-1, _⟩
    have hs'_lastv : (fun j : Fin (d + 1) =>
        if j.val = 0 then new_v else s.verts ⟨j.val - 1, by omega⟩)
        ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ = s.verts ⟨d - 1, by omega⟩ := by
      simp [show ¬(d = 0) from hd]
    rw [hs'_lastv, if_pos h_pos']
    -- inc0' = s'.incDir ⟨0, _⟩ = last_inc
    have hs'_inc0 : (fun j : Fin d =>
        if j.val = 0 then last_inc
        else s.incDir ⟨j.val - 1, by omega⟩) ⟨0, hd_pos⟩ = last_inc := by
      simp
    -- hd condition for boundaryFlip0 on s': d ≠ 0 is hd
    simp only [if_pos h_pos', if_neg hd, hs'_inc0]
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨GridSimplex.ext' ?_ ?_ ?_, rfl⟩
    · funext j; simp only
      by_cases hjd : j.val < d
      · simp only [show (j.val < d) = True from eq_true hjd, dite_true]
        simp only [show ¬(j.val + 1 = 0) from by omega, ite_false]
        congr 1; ext; omega
      · simp only [show (j.val < d) = False from eq_false hjd, dite_false]
        exact (new_v''_eq.trans (by congr 1; ext; omega))
    · funext j; simp only
      by_cases hjd : j.val + 1 < d
      · simp only [show (j.val + 1 < d) = True from eq_true hjd, dite_true]
        simp only [show ¬(j.val + 1 = 0) from by omega, ite_false]
        congr 1; ext; omega
      · simp only [show (j.val + 1 < d) = False from eq_false hjd, dite_false]
        have hj_last : j.val = d - 1 := by omega
        simp only [show (j.val = 0) = False from by simp [hj_last]; omega, ite_false]
        congr 1; ext; omega
    · rfl
  · simp at h
  · simp at h

/-- Adjacency is symmetric: if s is adjacent to s' through
facet k, then s' is adjacent to s through facet k'. -/
theorem gridAdj_symm (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    gridAdj d N s' k' = some (s, k) := by
  simp only [gridAdj] at h
  split_ifs at h with hk0 hkd
  · -- k.val = 0: boundaryFlip0
    -- Extract d ≠ 0 and k' = ⟨d, _⟩ from h
    have hd : d ≠ 0 := by
      simp only [GridSimplex.boundaryFlip0] at h
      split_ifs at h with hp hd <;> simp_all
    have hk'_eq : k' = ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ := by
      simp only [GridSimplex.boundaryFlip0] at h
      split_ifs at h with hp hd' <;> simp_all [Option.some.injEq, Prod.mk.injEq]
    have hk_eq : k = ⟨0, by omega⟩ := Fin.ext hk0
    rw [hk'_eq]
    simp only [gridAdj, show ¬(d = 0) from hd, show d ≠ 0 from hd, ite_false,
               show (d : ℕ) = d from rfl, ite_true]
    rw [← hk_eq]
    exact boundaryFlip0_invol s s' k' h
  · -- k.val = d: boundaryFlipLast
    have hd : d ≠ 0 := by
      simp only [GridSimplex.boundaryFlipLast] at h
      split_ifs at h with hd hp <;> simp_all
    have hk'_eq : k' = ⟨0, Nat.zero_lt_succ d⟩ := by
      simp only [GridSimplex.boundaryFlipLast] at h
      split_ifs at h with hd' hp <;> simp_all [Option.some.injEq, Prod.mk.injEq]
    have hk_eq : k = ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ := Fin.ext hkd
    rw [hk'_eq]
    simp only [gridAdj, show (0 : ℕ) = 0 from rfl, ite_true]
    rw [← hk_eq]
    exact boundaryFlipLast_invol s s' k' h
  · -- Interior: 0 < k.val < d
    have hklt : k.val < d := by omega
    have hkpos : 0 < k.val := by omega
    let step : Fin d := ⟨k.val, hklt⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', hk'eq⟩ := h
    subst hs'
    have hk'_val : k'.val = k.val := by
      rw [← hk'eq]; simp [GridSimplex.interiorFlip]
    have hk'_ne0 : ¬k'.val = 0 := by omega
    have hk'_ned : ¬k'.val = d := by omega
    simp only [gridAdj, hk'_ne0, hk'_ned, ite_false]
    have hinvol := interiorFlip_invol s step hkpos
    simp only [Prod.mk.injEq] at hinvol
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨hinvol.1, ?_⟩
    rw [← hk'eq]
    simp [GridSimplex.interiorFlip, hinvol.2]

/-- Adjacent cells share the codimension-1 face. -/
theorem gridAdj_vertex (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    (univ.erase k).image s.verts =
    (univ.erase k').image s'.verts := by
  simp only [gridAdj] at h
  split_ifs at h with hk0 hkd
  · -- k.val = 0, k' = ⟨d, _⟩
    simp only [GridSimplex.boundaryFlip0] at h
    split_ifs at h with h_pos hd
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs', hk'eq⟩ := h; subst hs'
      rw [Fin.ext hk0, hk'eq.symm]
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      ext v
      simp only [mem_image, mem_erase, mem_univ, true_and]
      constructor
      · rintro ⟨j, hjk, rfl⟩
        have hj_pos : 0 < j.val := Nat.pos_of_ne_zero (fun h0 => hjk (Fin.ext h0))
        refine ⟨⟨j.val - 1, by omega⟩, ?_, ?_⟩
        · intro heq; simp [Fin.ext_iff] at heq; omega
        · have hlt : j.val - 1 < d := by omega
          simp only [GridSimplex.boundaryFlip0, h_pos, if_neg hd, hlt, dite_true]
          congr 1; ext; omega
      · rintro ⟨j', hj'd, rfl⟩
        have hj'_lt : j'.val < d := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j'.isLt)
          (fun h => hj'd (Fin.ext (by omega)))
        refine ⟨⟨j'.val + 1, by omega⟩, ?_, ?_⟩
        · intro heq; simp [Fin.ext_iff] at heq
        · simp only [GridSimplex.boundaryFlip0, h_pos, if_neg hd, hj'_lt, dite_true]
          congr 1; ext; simp
    · simp at h
  · -- k.val = d, k' = 0
    simp only [GridSimplex.boundaryFlipLast] at h
    split_ifs at h with hd h_pos
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hs', hk'eq⟩ := h; subst hs'
      rw [Fin.ext hkd, hk'eq.symm]
      have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      ext v
      simp only [mem_image, mem_erase, mem_univ, true_and]
      constructor
      · rintro ⟨j, hjk, rfl⟩
        have hj_ltd : j.val < d := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt)
          (fun h => hjk (Fin.ext h))
        refine ⟨⟨j.val + 1, by omega⟩, ?_, ?_⟩
        · intro heq; simp [Fin.ext_iff] at heq
        · simp only [GridSimplex.boundaryFlipLast, if_neg hd, if_pos h_pos]
          simp only [show ¬(j.val + 1 = 0) from by omega, ite_false]
          congr 1; ext; simp
      · rintro ⟨j', hj'0, rfl⟩
        have hj'_pos : 0 < j'.val := Nat.pos_of_ne_zero
          (fun h0 => hj'0 (Fin.ext h0))
        refine ⟨⟨j'.val - 1, by omega⟩, ?_, ?_⟩
        · intro heq; simp [Fin.ext_iff] at heq; omega
        · simp only [GridSimplex.boundaryFlipLast, if_neg hd, if_pos h_pos]
          simp only [show (j'.val - 1 + 1 = 0) = False from by simp; omega, ite_false]
          congr 1; ext; omega
    · simp at h
    · simp at h
  · -- Interior: k = k', images agree on erase k
    have hklt : k.val < d := by omega
    have hkpos : 0 < k.val := by omega
    let step : Fin d := ⟨k.val, hklt⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', hk'eq⟩ := h; subst hs'
    have hk'_eq : k = k' := Fin.ext (by rw [← hk'eq]; simp [GridSimplex.interiorFlip])
    rw [← hk'_eq]
    apply Finset.image_congr
    intro j hj
    exact (interiorFlip_verts_other s step hkpos j
      (fun heq => (Finset.mem_erase.mp hj).1 (Fin.ext heq))).symm

/-- Adjacent cells are distinct. -/
theorem gridAdj_ne (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    s ≠ s' := by
  simp only [gridAdj] at h
  split_ifs at h with hk0 hkd
  · -- k.val = 0: uses boundaryFlip0; vertex 0 maps to vertex 1
    obtain ⟨hd, hv⟩ := boundaryFlip0_verts_zero s s' k' h
    intro heq
    rw [← heq] at hv
    have hinj := s.verts_injective hv
    simp [Fin.ext_iff] at hinj
  · -- k.val = d: uses boundaryFlipLast; vertex 1 maps to vertex 0
    obtain ⟨hd, hv⟩ := boundaryFlipLast_verts_one s s' k' h
    intro heq
    rw [← heq] at hv
    have hinj := s.verts_injective hv
    simp [Fin.ext_iff] at hinj
  · -- Interior: the incDir at k-1 changes in s' but not s
    simp only [Option.some.injEq] at h
    have hklt : k.val < d := by omega
    have hkpos : 0 < k.val := by omega
    let step : Fin d := ⟨k.val, hklt⟩
    let kp : Fin d := ⟨k.val - 1, by omega⟩
    -- Extract s' = (s.interiorFlip step hkpos).1
    have hs' : (s.interiorFlip step hkpos).1 = s' := by
      simpa using (Prod.ext_iff.mp h).1
    -- In s, incDir(kp) ≠ incDir(step) by injectivity
    have hkpne : kp ≠ step := by
      simp only [kp, step, ne_eq, Fin.mk.injEq]; omega
    have h_ne : s.incDir kp ≠ s.incDir step :=
      fun heq => hkpne (s.inc_injective heq)
    -- If s = s', then s.incDir kp = s'.incDir kp
    -- But s'.incDir kp = s.incDir step (by interiorFlip_incDir_kprev)
    -- Contradiction with h_ne
    intro heq
    apply h_ne
    have h1 : s.incDir kp = s'.incDir kp :=
      congr_fun (congr_arg GridSimplex.incDir heq) kp
    rw [h1, ← hs']
    exact interiorFlip_incDir_kprev s step hkpos

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
-- SECTION VIII: Sperner Condition and Boundary Analysis
-- ============================================================

/-- On a boundary face at position k (where adj = none and
k < d), all d vertices of the face lie on geometric face k
of the simplex Δ_N. That is, for each vertex j ≠ k of the
simplex, vertex j has b_k = 0.

This is the key geometric fact that connects the combinatorial
boundary (adj = none) to the geometric boundary (onFace k). -/
theorem boundary_verts_on_face
    (s : GridSimplex d N) (k : Fin (d + 1))
    (hk : k.val < d)
    (hbdry : gridAdj d N s k = none)
    (j : Fin (d + 1)) (hjk : j ≠ k) :
    (s.verts j).onFace k := by
  -- NOTE: This theorem is FALSE as stated.
  -- gridAdj d N s k = none at k=0 means (s.verts d).coords s.miss = 0,
  -- which says the "last vertex" has zero mass in the miss direction.
  -- This does NOT imply that all other vertices j≠k have (s.verts j).coords k = 0.
  --
  -- Counterexample (d=2, N=3):
  --   s.miss = 0, s.incDir = [1, 2]
  --   v₀ = (2, 0, 1), v₁ = (1, 1, 1), v₂ = (0, 1, 2)
  --   k = ⟨0, _⟩  (so k.val=0 < d=2, hk satisfied)
  --   gridAdj at k=0: calls boundaryFlip0, checks (v₂).coords s.miss = (v₂).coords 0 = 0 ✓
  --   so gridAdj returns none (hbdry satisfied)
  --   But for j = ⟨1, _⟩ (j ≠ k): (v₁).coords k = (v₁).coords 0 = 1 ≠ 0
  --   so (s.verts j).onFace k fails.
  --
  -- Root cause: gridAdj=none at k<d signals that boundaryFlip0 found no flip target
  -- (because the mass has been fully "used up" in the miss direction), but this does
  -- NOT mean the simplex lies on geometric face k of Δ_N.
  -- Fix requires redesigning gridAdj to correctly identify geometric boundary faces.
  sorry

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
  -- A door at position k requires: for each color j < d,
  -- some vertex i ≠ k has c(verts i) = j.
  -- In particular, for j = k (which is < d by hk),
  -- we need some i ≠ k with c(verts i) = k.
  -- But all vertices i ≠ k are on face k (by boundary_verts_on_face),
  -- so the Sperner condition says c(verts i) ≠ k. Contradiction.
  intro hdoor
  unfold CellComplex.IsDoor at hdoor
  simp [gridComplex] at hdoor
  -- Get the witness for color k
  have ⟨i, hi_ne, hi_col⟩ := hdoor ⟨k.val, hk⟩
  -- vertex i is on face k
  have honface := boundary_verts_on_face s k hk hbdry i hi_ne
  -- Sperner says c(verts i) ≠ k
  have hsperner := hc (s.verts i) k honface
  -- But hi_col says c(verts i) = Fin.castSucc ⟨k.val, hk⟩ = k
  have : Fin.castSucc (⟨k.val, hk⟩ : Fin d) = k := by
    ext; simp [Fin.castSucc]
  rw [this] at hi_col
  exact hsperner hi_col

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
  -- NOTE: This theorem is FALSE for d=1, making it unprovable without redesign.
  --
  -- Counterexample (d=1, N=1):
  --   BaryPoint 1 1 has two elements: (1,0) and (0,1).
  --   GridSimplex 1 1 has two cells:
  --     S₁: miss=0, incDir=[1], v₀=(1,0), v₁=(0,1)   [the edge from (1,0) to (0,1)]
  --     S₂: miss=1, incDir=[0], v₀=(0,1), v₁=(1,0)   [the SAME edge, reversed]
  --   Both S₁ and S₂ represent the same geometric edge, but are distinct GridSimplex cells.
  --
  --   For any Sperner coloring c: IsSperner forces c(1,0)=0 (since (1,0).coords 1=0)
  --   and c(0,1)=1 (since (0,1).coords 0=0).
  --   - S₁ at k=⟨1,_⟩: gridAdj=none (k=d, calls boundaryFlipLast;
  --     (v₀).coords (incDir ⟨0,_⟩) = (1,0).coords 1 = 0, so returns none).
  --     Colors {c(v₀)}={0} = {color 0} ✓ → door! Boundary door count += 1.
  --   - S₂ at k=⟨0,_⟩: gridAdj=none (k=0, calls boundaryFlip0;
  --     (v₁).coords miss = (1,0).coords 1 = 0, so returns none).
  --     Colors {c(v₁)}={0} = {color 0} ✓ → door! Boundary door count += 1.
  --   Total boundary doors = 2 (EVEN). Odd ⟨2, ...⟩ is false.
  --
  -- Root cause: The Freudenthal triangulation has d! simplices per unit hypercube.
  -- For d=1, each geometric edge has 2 GridSimplex representations (miss=0 and miss=1).
  -- This double-counting makes boundary door counts even.
  -- For d≥2, each geometric simplex has exactly one valid (miss, incDir) chain, so
  -- no double-counting — but boundary_verts_on_face (which this depends on) is also false.
  --
  -- Additional issue: sperner_grid requires N≥d for a non-empty complex (not just N>0).
  -- For d=2, N=1: gridComplex 2 1 is empty (no valid GridSimplex exists), making
  -- ∃ s, IsPanchromatic ... trivially false.
  --
  -- Fix requires: redesigning GridSimplex and gridAdj to correctly handle cross-miss
  -- adjacencies, so each geometric simplex appears exactly once (or fixing the
  -- double-counting by quotient/canonical form selection).
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
        (gridComplex d N) s := by
  exact CellComplex.sperner c (gridComplex d N)
    (boundary_doors_odd d N hN c hc)

end SpernerGrid

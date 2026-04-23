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

* `SpernerGrid.gridAdj_symm`: Adjacency is symmetric.
* `SpernerGrid.gridAdj_vertex`: Adjacent cells share the codim-1 face.
* `SpernerGrid.gridComplex d N`: The `CellComplex` instance (fully axiom-proved).
* `SpernerGrid.sperner_grid`: Concrete Sperner's lemma (sorry'd — see Architectural Note).

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

## Architectural Note: Oriented vs Unoriented

The `GridSimplex` uses ORIENTED simplices (each geometric simplex appears
twice: once per miss direction). This causes:
- `boundary_doors_odd` is FALSE: boundary door count is always EVEN
  (each geometric boundary door appears in 2 oriented forms).
- `boundary_verts_on_face` is FALSE: `adj(s,k)=none` does NOT imply
  all non-k vertices lie on geometric face k. Counterexample:
  d=1, N=2, miss=1, incDir(0)=0, verts(0)=(1,1), verts(1)=(2,0):
  adj(s,0)=None (last_v.coords(miss=1)=0) but verts(1).coords(0)=2≠0.

The correct path to `sperner_grid` requires either:
A. Using `SpernerNDim.sperner_ndim` with an UNORIENTED SpernerTriangulation
   (one representative per geometric simplex, satisfying `boundary_face`).
B. A direct inductive proof bypassing the boundary-door parity.

The `gridComplex d N` is a well-formed `CellComplex` (all adjacency axioms
proved), but `CellComplex.sperner` cannot be applied due to the above.

## Sorry classification (4 remaining)

1. `CellComplex.sperner` — proved in SpernerMathlib4.lean,
   duplicated here for self-containment. INTENTIONALLY sorry.
2. `boundary_verts_on_face` — FALSE as stated (see counterexample above).
3. `boundary_doors_odd` — FALSE as stated (boundary doors always even).
4. `sperner_grid` d≥2 case — blocked; needs unoriented SpernerTriangulation.
   d=0 and d=1 cases are now proved (d=1 via discrete IVT, Session 6).

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
          -- Goal: s.verts k_prev.castSucc .coords s.miss = new_v.coords s.miss + 1
          -- Omega needs to see s.verts k_prev.castSucc = v_prev (= s.verts prev_v_idx)
          have hcs_vprev : s.verts k_prev.castSucc = v_prev := by
            show s.verts k_prev.castSucc = s.verts prev_v_idx
            congr 1
          rw [hcs_vprev]
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
-- SECTION VIb: Helpers for gridAdj_symm and gridAdj_vertex
-- ============================================================

/-- GridSimplex extensionality: equality determined by verts, incDir, miss. -/
private theorem GridSimplex.ext' {d N : ℕ} (a b : GridSimplex d N)
    (hv : a.verts = b.verts) (hi : a.incDir = b.incDir)
    (hm : a.miss = b.miss) : a = b := by
  cases a; cases b; simp only at hv hi hm; subst hv; subst hi; subst hm; rfl

/-- In the interiorFlip, the incDir at position k equals
the original incDir at k-1. -/
private lemma interiorFlip_incDir_k (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val) :
    (s.interiorFlip k hk).1.incDir k =
    s.incDir ⟨k.val - 1, by omega⟩ := by
  have hkne : k ≠ ⟨k.val - 1, by omega⟩ := by simp [Fin.ext_iff]; omega
  simp [GridSimplex.interiorFlip, hkne]

/-- Interior flip is an involution: applying it twice returns the original. -/
private lemma interiorFlip_invol (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val) :
    (s.interiorFlip k hk).1.interiorFlip k hk =
    (s, k.castSucc) := by
  let s' := (s.interiorFlip k hk).1
  let k_prev : Fin d := ⟨k.val - 1, by omega⟩
  have hS_kp : s'.incDir k_prev = s.incDir k :=
    interiorFlip_incDir_kprev s k hk
  have hS_k : s'.incDir k = s.incDir k_prev :=
    interiorFlip_incDir_k s k hk
  have hS_vo : ∀ j : Fin (d + 1), j.val ≠ k.val → s'.verts j = s.verts j :=
    interiorFlip_verts_other s k hk
  have h_pos : 0 < (s'.verts ⟨k.val - 1, by omega⟩).coords s'.miss := by
    rw [show s'.miss = s.miss from rfl,
        hS_vo ⟨k.val - 1, by omega⟩ (Nat.ne_of_lt (Nat.sub_lt hk Nat.one_pos))]
    exact Nat.lt_of_lt_of_le (Nat.sub_pos_of_lt (show k.val - 1 < d by omega))
      (s.miss_coord_ge ⟨k.val - 1, by omega⟩)
  apply Prod.ext
  · apply GridSimplex.ext'
    · funext j
      simp only [GridSimplex.interiorFlip]
      by_cases hjk : j.val = k.val
      · have hjeq : j = ⟨k.val, by omega⟩ := Fin.ext hjk
        simp only [hjeq, ite_true]
        rw [show s'.miss = s.miss from rfl, hS_k,
            hS_vo ⟨k.val - 1, by omega⟩ (Nat.ne_of_lt (Nat.sub_lt hk Nat.one_pos))]
        apply BaryPoint.ext; funext i
        simp only [BaryPoint.transfer]
        have hkpsucc : (k_prev.succ : Fin (d + 1)) =
            ⟨k.val, k.isLt⟩ := by ext; simp [k_prev, Fin.succ]; omega
        have hkpcs : (k_prev.castSucc : Fin (d + 1)) =
            ⟨k.val - 1, by omega⟩ := by ext; simp [k_prev, Fin.castSucc]
        have hsi := s.step_inc k_prev
        rw [hkpsucc, hkpcs] at hsi
        have hsd := s.step_dec k_prev
        rw [hkpsucc, hkpcs] at hsd
        split_ifs with hi_inc hi_miss
        · rw [hi_inc]; exact hsi
        · rw [hi_miss]; omega
        · have := s.step_same k_prev i hi_inc hi_miss
          rw [hkpsucc, hkpcs] at this; exact this.symm
      · have hjne : j ≠ (⟨k.val, by omega⟩ : Fin (d + 1)) :=
            fun h => hjk (congrArg Fin.val h)
        simp only [hjne, ite_false]; exact hS_vo j hjk
    · funext j
      simp only [GridSimplex.interiorFlip]
      by_cases hjkp : j = k_prev
      · subst hjkp; simp only [ite_true]; exact hS_k
      · simp only [hjkp, ite_false]
        by_cases hjk : j = k
        · subst hjk; simp only [ite_true]; exact hS_kp
        · simp only [hjk, ite_false]
          simp [s', GridSimplex.interiorFlip, hjkp, hjk]
    · rfl
  · simp [GridSimplex.interiorFlip, Fin.ext_iff, Fin.castSucc]

/-- interiorFlip result is independent of which equal Fin d we pass (proof-irrelevance + Fin.ext). -/
private lemma interiorFlip_congr (A : GridSimplex d N)
    (k1 k2 : Fin d) (hk1 : 0 < k1.val) (hk2 : 0 < k2.val)
    (h12 : k1 = k2) :
    A.interiorFlip k1 hk1 = A.interiorFlip k2 hk2 := by
  subst h12
  exact congrArg (A.interiorFlip k1) (Subsingleton.elim hk1 hk2)

/-- The return index from boundaryFlip0 has value d. -/
private lemma boundaryFlip0_k'_val (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlip0 = some (s', k')) : k'.val = d := by
  simp only [GridSimplex.boundaryFlip0] at h
  split_ifs at h with h_pos hd
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact (congr_arg Fin.val h.2).symm

/-- The return index from boundaryFlipLast has value 0. -/
private lemma boundaryFlipLast_k'_val (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlipLast = some (s', k')) : k'.val = 0 := by
  simp only [GridSimplex.boundaryFlipLast] at h
  split_ifs at h with hd h_pos
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact (congr_arg Fin.val h.2).symm

/-- If boundaryFlip0 succeeds, s'.verts j = s.verts (j+1) for j.val < d. -/
private lemma boundaryFlip0_verts_lt' (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlip0 = some (s', k'))
    (j : Fin (d + 1)) (hj : j.val < d) :
    s'.verts j = s.verts ⟨j.val + 1, by omega⟩ := by
  simp only [GridSimplex.boundaryFlip0] at h
  split_ifs at h with h_pos hd
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h
    have := congr_fun (congr_arg GridSimplex.verts hs') j
    simp [Nat.pos_of_ne_zero hd, hj] at this
    exact this.symm

/-- If boundaryFlipLast succeeds, s'.verts j = s.verts (j-1) for 0 < j.val. -/
private lemma boundaryFlipLast_verts_pos' (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlipLast = some (s', k'))
    (j : Fin (d + 1)) (hj : 0 < j.val) :
    s'.verts j = s.verts ⟨j.val - 1, by omega⟩ := by
  simp only [GridSimplex.boundaryFlipLast] at h
  split_ifs at h with hd h_pos
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h
    have := congr_fun (congr_arg GridSimplex.verts hs') j
    simp [hj.ne'] at this
    exact this.symm

/-- Helper: the vertex restored by composing the two boundary flips. -/
private lemma transfer_eq_prev_verts (s : GridSimplex d N)
    (step : Fin d) :
    let k_prev : Fin d := step
    let kp1 : Fin (d + 1) := ⟨step.val + 1, by omega⟩
    let kp0 : Fin (d + 1) := ⟨step.val, by omega⟩
    let h_ne := s.miss_ne_inc step
    let h_pos : 0 < (s.verts kp0).coords s.miss :=
      Nat.lt_of_lt_of_le (Nat.sub_pos_of_lt step.isLt) (s.miss_coord_ge kp0)
    (s.verts kp0).transfer (s.incDir step) s.miss h_ne h_pos =
    s.verts kp1 := by
  apply BaryPoint.ext; funext i
  simp only [BaryPoint.transfer]
  have hsu : (step.castSucc : Fin (d + 1)) = ⟨step.val, by omega⟩ := by
    ext; simp [Fin.castSucc]
  have hss : (step.succ : Fin (d + 1)) = ⟨step.val + 1, by omega⟩ := by
    ext; simp [Fin.succ]
  have hsi := s.step_inc step; rw [hsu, hss] at hsi
  have hsd := s.step_dec step; rw [hsu, hss] at hsd
  split_ifs with h1 h2
  · rw [h1]; exact hsi
  · rw [h2]; omega
  · exact (s.step_same step i h1 h2).symm

/-- boundaryFlip0 and boundaryFlipLast are inverses:
    boundaryFlipLast(boundaryFlip0(s).1) = some(s, 0). -/
private lemma boundaryFlip0_symm (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlip0 = some (s', k')) :
    s'.boundaryFlipLast = some (s, ⟨0, Nat.zero_lt_succ d⟩) := by
  simp only [GridSimplex.boundaryFlip0] at h
  split_ifs at h with h_pos hd
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have hmiss : s'.miss = s.miss := congr_arg GridSimplex.miss hs'
    have hincDir_last : s'.incDir ⟨d - 1, by omega⟩ =
        s.incDir ⟨0, hd_pos⟩ := by
      have := congr_fun (congr_arg GridSimplex.incDir hs') ⟨d - 1, by omega⟩
      simp [show ¬(d - 1 + 1 < d) from by omega] at this
      exact this
    have hverts_zero : s'.verts ⟨0, Nat.zero_lt_succ d⟩ =
        s.verts ⟨1, hd_pos⟩ := by
      have := congr_fun (congr_arg GridSimplex.verts hs') ⟨0, Nat.zero_lt_succ d⟩
      simp [hd_pos] at this; exact this
    simp only [GridSimplex.boundaryFlipLast, hd, dite_false]
    -- Condition: 0 < s'.verts(0).coords(s'.incDir(d-1))
    have h_cond : 0 < (s'.verts ⟨0, Nat.zero_lt_succ d⟩).coords
        (s'.incDir ⟨d - 1, by omega⟩) := by
      rw [hincDir_last, hverts_zero]
      have hsi := s.step_inc ⟨0, hd_pos⟩
      simp [Fin.castSucc, Fin.succ] at hsi; omega
    simp only [h_cond, dite_true]
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    apply GridSimplex.ext'
    · funext j
      simp only
      by_cases hj0 : j.val = 0
      · have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj0
        subst hjeq
        simp only [hj0, ite_true]
        -- new_v'' = s'.verts(0).transfer(s'.miss)(last_inc') = s.verts(0)
        rw [hmiss, hincDir_last, hverts_zero]
        -- s.verts(1).transfer(s.miss)(s.incDir 0) = s.verts(0)
        -- This follows from transfer_eq_prev_verts applied to step = ⟨0, hd_pos⟩
        have := @transfer_eq_prev_verts d (s.verts 0 |>.coords s.miss) N s ⟨0, hd_pos⟩
        simp at this
        -- Hmm, transfer_eq_prev_verts is in the wrong direction. Let me prove directly.
        apply BaryPoint.ext; funext i
        simp only [BaryPoint.transfer]
        have hsi := s.step_inc ⟨0, hd_pos⟩
        simp [Fin.castSucc, Fin.succ] at hsi
        have hsd := s.step_dec ⟨0, hd_pos⟩
        simp [Fin.castSucc, Fin.succ] at hsd
        split_ifs with hi_miss hi_last
        · omega
        · omega
        · exact (s.step_same ⟨0, hd_pos⟩ i
            (fun h => hi_last (h ▸ rfl))
            (fun h => hi_miss (h ▸ rfl))).symm
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj0
        simp only [hj0, ite_false]
        -- s'.verts ⟨j.val - 1, _⟩ = s.verts j
        have hj1_lt : j.val - 1 < d := by
          have := j.isLt; omega
        rw [congr_fun (congr_arg GridSimplex.verts hs') ⟨j.val - 1, hj1_lt⟩]
        simp [hj1_lt, show j.val - 1 + 1 = j.val from Nat.sub_add_cancel hj_pos]
    · funext j
      simp only
      by_cases hj0 : j.val = 0
      · have hjeq : j = ⟨0, by omega⟩ := Fin.ext hj0
        subst hjeq
        simp only [hj0, ite_true]
        exact hincDir_last
      · have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj0
        simp only [hj0, ite_false]
        have hj1_lt : j.val - 1 < d := by have := j.isLt; omega
        rw [congr_fun (congr_arg GridSimplex.incDir hs') ⟨j.val - 1, hj1_lt⟩]
        simp [show j.val - 1 + 1 = j.val from Nat.sub_add_cancel hj_pos,
              show j.val - 1 + 1 < d ↔ j.val < d from by omega]
        split_ifs with hlt
        · congr 1; ext; simp; omega
        · -- j.val = d (last case maps to inc0 = s.incDir ⟨0, _⟩)
          -- But j : Fin d so j.val < d — contradiction
          exact absurd hlt (by omega)
    · exact hmiss

/-- boundaryFlipLast and boundaryFlip0 are inverses:
    boundaryFlip0(boundaryFlipLast(s).1) = some(s, d). -/
private lemma boundaryFlipLast_symm (s : GridSimplex d N)
    (s' : GridSimplex d N) (k' : Fin (d + 1))
    (h : s.boundaryFlipLast = some (s', k')) :
    s'.boundaryFlip0 = some (s, ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩) := by
  simp only [GridSimplex.boundaryFlipLast] at h
  split_ifs at h with hd h_pos
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hs', _⟩ := h
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have hmiss : s'.miss = s.miss := congr_arg GridSimplex.miss hs'
    have hincDir_zero : s'.incDir ⟨0, hd_pos⟩ =
        s.incDir ⟨d - 1, by omega⟩ := by
      have := congr_fun (congr_arg GridSimplex.incDir hs') ⟨0, hd_pos⟩
      simp at this; exact this
    have hverts_last : s'.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ =
        s.verts ⟨d - 1, by omega⟩ := by
      have := congr_fun (congr_arg GridSimplex.verts hs')
        ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩
      simp [show ¬(d = 0) from hd, show ¬((d : ℕ) = 0) from hd] at this
      exact this
    simp only [GridSimplex.boundaryFlip0, hd, dite_false]
    -- Condition: 0 < s'.verts(d).coords(s'.miss)
    have h_cond : 0 < (s'.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩).coords s'.miss := by
      rw [hmiss, hverts_last]
      have := s.miss_coord_ge ⟨d - 1, by omega⟩
      simp at this; omega
    simp only [h_cond, dite_true, hd, dite_false]
    simp only [Option.some.injEq, Prod.mk.injEq]
    refine ⟨?_, rfl⟩
    apply GridSimplex.ext'
    · funext j
      simp only
      by_cases hjd : j.val < d
      · simp only [hjd, dite_true]
        -- s'.verts ⟨j.val + 1, _⟩
        have hj1 : 0 < j.val + 1 := by omega
        rw [congr_fun (congr_arg GridSimplex.verts hs') ⟨j.val + 1, by omega⟩]
        simp [hj1, show j.val + 1 - 1 = j.val from by omega]
      · simp only [hjd, dite_false]
        -- j.val = d: new_v' = s'.verts(d).transfer(s'.incDir 0)(s'.miss)
        have hjd_eq : j.val = d := by have := j.isLt; omega
        -- = s.verts(d-1).transfer(s.incDir(d-1))(s.miss) = s.verts(d)
        rw [show j = (⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ : Fin (d + 1)) from Fin.ext hjd_eq]
        apply BaryPoint.ext; funext i
        simp only [BaryPoint.transfer]
        -- Rewrite s' fields coordinatewise (avoiding dependent rw on transfer args)
        rw [hmiss, hincDir_zero,
            show (s'.verts ⟨d, Nat.lt_succ_iff.mpr le_rfl⟩).coords i =
                 (s.verts ⟨d - 1, by omega⟩).coords i from
                 congr_arg (fun v => BaryPoint.coords v i) hverts_last]
        have hsi := s.step_inc ⟨d - 1, by omega⟩
        simp [Fin.castSucc, Fin.succ, show d - 1 + 1 = d from by omega] at hsi
        have hsd := s.step_dec ⟨d - 1, by omega⟩
        simp [Fin.castSucc, Fin.succ, show d - 1 + 1 = d from by omega] at hsd
        split_ifs with hi_inc hi_miss
        · rw [hi_inc]; exact hsi
        · rw [hi_miss]; omega
        · have hss := s.step_same ⟨d - 1, by omega⟩ i
            (fun h => hi_inc (h ▸ rfl))
            (fun h => hi_miss (h ▸ rfl))
          simp [Fin.castSucc, Fin.succ, show d - 1 + 1 = d from by omega] at hss
          exact hss.symm
    · funext j
      simp only
      by_cases hjd : j.val + 1 < d
      · simp only [hjd, dite_true]
        -- Goal: s'.incDir ⟨j.val+1, ⋯⟩ = s.incDir j
        -- Unfold s'.incDir via hs'.symm : s' = { BFL_struct },
        -- then evaluate: if j.val+1 = 0 then ... else s.incDir ⟨j.val, ⋯⟩
        have h_inc : s'.incDir ⟨j.val + 1, hjd⟩ = s.incDir j := by
          have h1 := congr_fun (congr_arg GridSimplex.incDir hs'.symm) ⟨j.val + 1, hjd⟩
          simp only [show (j.val + 1 : ℕ) ≠ 0 from by omega, ite_false,
                     show j.val + 1 - 1 = j.val from by omega] at h1
          exact h1.trans (congr_arg s.incDir (Fin.ext rfl))
        exact h_inc
      · -- j.val + 1 ≥ d, so j.val = d - 1
        simp only [hjd, dite_false]
        have hjd_eq : j.val = d - 1 := by have := j.isLt; omega
        -- s'.incDir ⟨0, hd_pos⟩ = s.incDir j via hincDir_zero and hjd_eq
        have key : s'.incDir ⟨0, hd_pos⟩ = s.incDir j :=
          hincDir_zero.trans (congr_arg s.incDir (Fin.ext (by simp [hjd_eq])))
        exact key
    · exact hmiss

-- ============================================================
-- SECTION VII: CellComplex Instance
-- ============================================================

/-- The second component of interiorFlip has value equal to k.val. -/
private lemma interiorFlip_snd_val (s : GridSimplex d N)
    (k : Fin d) (hk : 0 < k.val) :
    (s.interiorFlip k hk).2.val = k.val := by
  simp [GridSimplex.interiorFlip]

/-- Adjacency is symmetric: if s is adjacent to s' through
facet k, then s' is adjacent to s through facet k'. -/
theorem gridAdj_symm (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    gridAdj d N s' k' = some (s, k) := by
  simp only [gridAdj] at h
  split_ifs at h with hk0 hkd
  · -- k.val = 0: boundaryFlip0 case; k'.val = d
    have hk'_val : k'.val = d := boundaryFlip0_k'_val s s' k' h
    obtain ⟨hd_ne, _⟩ := boundaryFlip0_verts_zero s s' k' h
    -- simp resolves inner if (k'.val = d) so split_ifs has 2 cases
    simp only [gridAdj]; split_ifs with hk'0
    · exact absurd hk'0 (by omega)    -- k'.val = 0 contradicts k'.val = d ≠ 0
    · -- k'.val = d branch: goal is s'.boundaryFlipLast = some (s, k)
      have hresult := boundaryFlip0_symm s s' k' h
      rw [show k = (⟨0, Nat.zero_lt_succ d⟩ : Fin (d + 1)) from by ext; omega]
      exact hresult
  · -- k.val = d: boundaryFlipLast case; k'.val = 0
    have hk'_val : k'.val = 0 := boundaryFlipLast_k'_val s s' k' h
    -- Use dif_pos to resolve the outer if (k'.val = 0 is True) → s'.boundaryFlip0 = some (s, k)
    simp only [gridAdj, dif_pos hk'_val]
    have hresult := boundaryFlipLast_symm s s' k' h
    rw [show k = (⟨d, Nat.lt_succ_iff.mpr le_rfl⟩ : Fin (d + 1)) from by ext; omega]
    exact hresult
  · -- interior: 0 < k.val < d
    have hk_lt_d : k.val < d := by omega
    have hk_pos : 0 < k.val := by omega
    let step : Fin d := ⟨k.val, hk_lt_d⟩
    simp only [Option.some.injEq] at h
    have hpair := Prod.ext_iff.mp h
    have hs'_eq : s' = (s.interiorFlip step hk_pos).1 := hpair.1.symm
    have hk'_val : k'.val = k.val := by
      have h2 : (s.interiorFlip step hk_pos).2.val = k'.val :=
        congr_arg Fin.val hpair.2
      rw [interiorFlip_snd_val s step hk_pos] at h2
      exact h2.symm
    have hk'_lt_d : k'.val < d := by omega
    have hk'_pos : 0 < k'.val := by omega
    simp only [gridAdj]; split_ifs with hk'0 hk'd
    · exact absurd hk'0 (by omega)
    · exact absurd hk'd (by omega)
    · rw [hs'_eq,
          interiorFlip_congr _ ⟨k'.val, hk'_lt_d⟩ step hk'_pos hk_pos (Fin.ext hk'_val),
          interiorFlip_invol s step hk_pos]
      exact congrArg some (Prod.ext rfl (Fin.ext rfl))

/-- Adjacent cells share the codimension-1 face. -/
theorem gridAdj_vertex (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    (univ.erase k).image s.verts =
    (univ.erase k').image s'.verts := by
  simp only [gridAdj] at h
  split_ifs at h with hk0 hkd
  · -- k.val = 0: boundaryFlip0; k'.val = d
    have hk'_val : k'.val = d := boundaryFlip0_k'_val s s' k' h
    apply Finset.ext; intro v
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
    constructor
    · rintro ⟨j, hjk, rfl⟩
      -- j.val ≠ 0; find preimage ⟨j.val-1, _⟩ in s'
      have hj_pos : 0 < j.val := by omega
      have hjm1_bd : j.val - 1 < d + 1 := by have := j.isLt; omega
      have hjm1_ltd : j.val - 1 < d := by have := j.isLt; omega
      refine ⟨⟨j.val - 1, hjm1_bd⟩, ?_, ?_⟩
      · change ¬j.val - 1 = k'.val; rw [hk'_val]; omega
      · -- s'.verts ⟨j.val-1,_⟩ = s.verts ⟨j.val-1+1,_⟩ = s.verts j
        have hv := boundaryFlip0_verts_lt' s s' k' h ⟨j.val - 1, hjm1_bd⟩ hjm1_ltd
        -- show the index j.val-1+1 = j.val using definitional unfolding then omega
        have hfin : (⟨j.val - 1, hjm1_bd⟩ : Fin (d + 1)).val + 1 = j.val := by
          show j.val - 1 + 1 = j.val; omega
        rw [hv]; exact congr_arg s.verts (Fin.ext hfin)
    · rintro ⟨j, hjk', rfl⟩
      -- j.val ≠ d = k'.val; find preimage ⟨j.val+1, _⟩ in s
      have hj_ltd : j.val < d := by rw [hk'_val] at hjk'; omega
      have hjp1_bd : j.val + 1 < d + 1 := by omega
      refine ⟨⟨j.val + 1, hjp1_bd⟩, ?_, ?_⟩
      · change ¬j.val + 1 = k.val; rw [hk0]; omega
      · exact (boundaryFlip0_verts_lt' s s' k' h j hj_ltd).symm
  · -- k.val = d: boundaryFlipLast; k'.val = 0
    have hk'_val : k'.val = 0 := boundaryFlipLast_k'_val s s' k' h
    apply Finset.ext; intro v
    simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff]
    constructor
    · rintro ⟨j, hjk, rfl⟩
      -- j.val ≠ d = k.val; find preimage ⟨j.val+1, _⟩ in s'
      have hj_ltd : j.val < d := by rw [hkd] at hjk; omega
      have hjp1_bd : j.val + 1 < d + 1 := by omega
      refine ⟨⟨j.val + 1, hjp1_bd⟩, ?_, ?_⟩
      · change ¬j.val + 1 = k'.val; rw [hk'_val]; omega
      · -- s'.verts ⟨j.val+1,_⟩ = s.verts ⟨j.val+1-1,_⟩ = s.verts j
        have hv := boundaryFlipLast_verts_pos' s s' k' h ⟨j.val + 1, hjp1_bd⟩
                     (show 0 < (⟨j.val + 1, hjp1_bd⟩ : Fin (d + 1)).val from by
                       show 0 < j.val + 1; omega)
        have hfin : (⟨j.val + 1, hjp1_bd⟩ : Fin (d + 1)).val - 1 = j.val := by
          show j.val + 1 - 1 = j.val; omega
        rw [hv]; exact congr_arg s.verts (Fin.ext hfin)
    · rintro ⟨j, hjk', rfl⟩
      -- j.val ≠ 0 = k'.val; find preimage ⟨j.val-1, _⟩ in s
      have hj_pos : 0 < j.val := by rw [hk'_val] at hjk'; omega
      have hjm1_bd : j.val - 1 < d + 1 := by have := j.isLt; omega
      refine ⟨⟨j.val - 1, hjm1_bd⟩, ?_, ?_⟩
      · change ¬j.val - 1 = k.val; rw [hkd]; omega
      · exact (boundaryFlipLast_verts_pos' s s' k' h j hj_pos).symm
  · -- interior: 0 < k.val < d; k' = k
    have hk_lt_d : k.val < d := by omega
    have hk_pos : 0 < k.val := by omega
    let step : Fin d := ⟨k.val, hk_lt_d⟩
    simp only [Option.some.injEq] at h
    have hpair := Prod.ext_iff.mp h
    have hs'_eq : s' = (s.interiorFlip step hk_pos).1 := hpair.1.symm
    have hk'_val : k'.val = k.val := by
      have h2 : (s.interiorFlip step hk_pos).2.val = k'.val :=
        congr_arg Fin.val hpair.2
      rw [interiorFlip_snd_val s step hk_pos] at h2
      exact h2.symm
    have hk'_eq : k' = k := Fin.ext hk'_val
    subst hk'_eq
    apply Finset.image_congr
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq] at hj
    rw [hs'_eq]
    exact (interiorFlip_verts_other s step hk_pos j
      (fun hval => hj (Fin.ext hval))).symm

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

/-- [KNOWN FALSE] This theorem is false as stated.

`adj(s, k) = none` does NOT imply all non-k vertices are on geometric face k.
The combinatorial boundary position (index k in the chain) does not align
with the geometric face index (which coordinate is 0).

Counterexample: d=1, N=2, miss=1, incDir(0)=0.
  verts(0) = (1, 1), verts(1) = (2, 0).
  adj(s, 0) = none [since last_v.coords(miss=1) = 0].
  But verts(1).coords(0) = 2 ≠ 0. ✗

The `boundary_face` axiom of `SpernerNDim.SpernerTriangulation` requires this
property, so `gridComplex` cannot instantiate `SpernerTriangulation`.
A different simplex representation (unoriented, with face-aligned indexing)
is needed to satisfy `boundary_face`. -/
theorem boundary_verts_on_face
    (s : GridSimplex d N) (k : Fin (d + 1))
    (hk : k.val < d)
    (hbdry : gridAdj d N s k = none)
    (j : Fin (d + 1)) (hjk : j ≠ k) :
    (s.verts j).onFace k := by
  -- FALSE: see docstring for counterexample.
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

/-- [KNOWN FALSE] The boundary door count for `gridComplex` is always EVEN, not odd.

Root cause: `GridSimplex` uses ORIENTED simplices. Each geometric simplex
appears TWICE (two orientations: miss=m₁ and miss=m₂). The "reversal involution"
pairs every boundary door (s, k) with (s̄, d-k) where s̄ is the same geometric
simplex in reversed orientation, yielding an even count.

Detailed counterexample (d=1, N=1, Sperner coloring c(1,0)=0, c(0,1)=1):
- Two GridSimplices: S₁=(miss=0, incDir(0)=1), S₂=(miss=1, incDir(0)=0)
- Boundary doors: (S₁, k=1) and (S₂, k=0) — count = 2 (EVEN).

The CORRECT theorem for the oriented gridComplex is:
  `boundary_door_count_even`: the boundary door count is always even.

To prove `sperner_grid`, the correct approach is:
A. Build a `SpernerNDim.SpernerTriangulation` with unoriented simplices
   (one per geometric simplex) satisfying the `boundary_face` axiom.
B. Apply `SpernerNDim.sperner_ndim`. -/
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
  -- FALSE: see docstring. Boundary door count is always even.
  sorry

-- ============================================================
-- SECTION VIII: Concrete Sperner's Lemma
-- ============================================================

/-- d=1 case of sperner_grid: proved directly via discrete IVT.
The path v(k) = (N-k, k) for k=0..N has c(v(0))=0 and c(v(N))=1
by Sperner, so the transition edge at k*=max{k | c(v(k))=0} is
panchromatic. -/
private lemma sperner_grid_one {N : ℕ} (hN : 0 < N)
    (c : BaryPoint 1 N → Fin 2)
    (hc : IsSperner c) :
    ∃ s : (gridComplex 1 N).Cell,
      CellComplex.IsPanchromatic c (gridComplex 1 N) s := by
  -- Path v(k) = (N-k, k) through the 1-simplex
  let v : Fin (N + 1) → BaryPoint 1 N := fun k =>
    ⟨fun i => if i.val = 0 then N - k.val else k.val,
     by
       simp [Fin.sum_univ_two]
       have hk : k.val ≤ N := Nat.lt_succ_iff.mp k.isLt
       omega⟩
  -- v(0) lies on face 1 (coords(1) = 0), so c(v(0)) ≠ 1, hence = 0
  have hv0 : c (v ⟨0, Nat.zero_lt_succ N⟩) = 0 := by
    have honface : (v ⟨0, Nat.zero_lt_succ N⟩).onFace ⟨1, by omega⟩ := by
      show (v ⟨0, _⟩).coords ⟨1, by omega⟩ = 0; simp [v]
    have hne := hc (v ⟨0, _⟩) ⟨1, by omega⟩ honface
    -- c(v(0)) ≠ 1 and c(v(0)) : Fin 2, so c(v(0)).val ∈ {0,1} and ≠ 1 → = 0
    apply Fin.ext
    have hlt := (c (v ⟨0, Nat.zero_lt_succ N⟩)).isLt
    have hne' : (c (v ⟨0, Nat.zero_lt_succ N⟩)).val ≠ 1 :=
      fun heq => hne (Fin.ext heq)
    omega
  -- v(N) lies on face 0 (coords(0) = N-N = 0), so c(v(N)) ≠ 0, hence = 1
  have hvN : c (v ⟨N, Nat.lt_succ_self N⟩) = 1 := by
    have honface : (v ⟨N, Nat.lt_succ_self N⟩).onFace ⟨0, by omega⟩ := by
      show (v ⟨N, _⟩).coords ⟨0, by omega⟩ = 0; simp [v]; omega
    have hne := hc (v ⟨N, _⟩) ⟨0, by omega⟩ honface
    -- c(v(N)) ≠ 0 and c(v(N)) : Fin 2, so c(v(N)).val ∈ {0,1} and ≠ 0 → = 1
    apply Fin.ext
    have hlt := (c (v ⟨N, Nat.lt_succ_self N⟩)).isLt
    have hne' : (c (v ⟨N, Nat.lt_succ_self N⟩)).val ≠ 0 :=
      fun heq => hne (Fin.ext heq)
    omega
  -- S = {k | c(v(k)) = 0}, find maximum k*
  let S := Finset.univ.filter (fun k : Fin (N + 1) => c (v k) = 0)
  have hS_ne : S.Nonempty :=
    ⟨⟨0, Nat.zero_lt_succ N⟩,
     Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv0⟩⟩
  have hN_not : (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) ∉ S := by
    intro hmem
    have hc := (Finset.mem_filter.mp hmem).2
    -- hc : c (v ⟨N, _⟩) = 0, but hvN : c (v ⟨N, _⟩) = 1. Contradiction.
    exact absurd (hc.symm.trans hvN) (by decide)
  let k_star := S.max' hS_ne
  have hks_mem : k_star ∈ S := Finset.max'_mem S hS_ne
  have hks_color : c (v k_star) = 0 := (Finset.mem_filter.mp hks_mem).2
  -- k* < N (cannot be N since N ∉ S)
  have hks_lt : k_star.val < N := by
    by_contra hge
    push_neg at hge
    have heq : k_star = ⟨N, Nat.lt_succ_self N⟩ := by apply Fin.ext; omega
    exact hN_not (heq ▸ hks_mem)
  -- k*+1 ∉ S by maximality, so c(v(k*+1)) ≠ 0, hence = 1
  have hks1_color : c (v ⟨k_star.val + 1, by omega⟩) = 1 := by
    have hns : (⟨k_star.val + 1, by omega⟩ : Fin (N + 1)) ∉ S := by
      intro hmem
      -- k_star = S.max' hS_ne; by maximality, ⟨k_star.val+1, _⟩ ≤ S.max' ⟨_, hmem⟩
      -- Then proof irrelevance equates the two max' witnesses
      have hle : (⟨k_star.val + 1, by omega⟩ : Fin (N + 1)) ≤
          S.max' ⟨⟨k_star.val + 1, by omega⟩, hmem⟩ :=
        Finset.le_max' S _ hmem
      have heq : S.max' ⟨⟨k_star.val + 1, by omega⟩, hmem⟩ = k_star :=
        congr_arg S.max' (Subsingleton.elim _ _)
      exact absurd (heq ▸ hle) (by omega)
    have hne : c (v ⟨k_star.val + 1, by omega⟩) ≠ 0 := by
      intro h
      exact hns (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    -- c(v(k*+1)) ≠ 0 and : Fin 2, so .val ≠ 0 and .val < 2 → .val = 1
    apply Fin.ext
    have hlt := (c (v ⟨k_star.val + 1, by omega⟩)).isLt
    have hne' : (c (v ⟨k_star.val + 1, by omega⟩)).val ≠ 0 :=
      fun heq => hne (Fin.ext heq)
    omega
  -- The edge [v(k*), v(k*+1)] is a GridSimplex with incDir=1, miss=0
  refine ⟨{
    verts := fun i => if i.val = 0 then v k_star
                      else v ⟨k_star.val + 1, by omega⟩
    incDir := fun _ => ⟨1, by omega⟩
    miss := ⟨0, by omega⟩
    miss_ne_inc := fun _ => by
      intro h; exact absurd (Fin.ext_iff.mp h) (by norm_num)
    step_inc := fun k => by
      fin_cases k
      show (v ⟨k_star.val + 1, by omega⟩).coords ⟨1, by omega⟩ =
           (v k_star).coords ⟨1, by omega⟩ + 1
      simp [v]
    step_dec := fun k => by
      fin_cases k
      show (v k_star).coords ⟨0, by omega⟩ =
           (v ⟨k_star.val + 1, by omega⟩).coords ⟨0, by omega⟩ + 1
      simp [v]
      omega
    step_same := fun k j hj1 hj2 => by
      fin_cases k
      fin_cases j
      · exact absurd (Fin.ext rfl) hj2  -- j = miss = 0, contradiction
      · exact absurd (Fin.ext rfl) hj1  -- j = incDir k = 1, contradiction
    inc_injective := fun a _b _h => Subsingleton.elim a _ }, ?_⟩
  -- Panchromatic: color 0 at v(k*), color 1 at v(k*+1)
  intro col
  fin_cases col
  · exact ⟨⟨0, by omega⟩, by
      show c (v k_star) = 0
      exact hks_color⟩
  · exact ⟨⟨1, by omega⟩, by
      show c (v ⟨k_star.val + 1, by omega⟩) = 1
      exact hks1_color⟩

/-- **Concrete Sperner's Lemma on the Grid** (sorry'd — blocked on architecture).

For any Sperner coloring of the grid triangulation of the d-simplex with
subdivision N > 0, there exists a panchromatic cell.

This is MATHEMATICALLY TRUE, but the current proof path through
`boundary_doors_odd` is blocked because `boundary_doors_odd` is FALSE for
the oriented `gridComplex` (see its docstring).

The correct proof requires one of:
A. A `SpernerNDim.SpernerTriangulation d N` instance for the unoriented
   Freudenthal triangulation (satisfying `boundary_face`), then apply
   `SpernerNDim.sperner_ndim`.
B. A direct inductive proof on d, not going through `boundary_doors_odd`.

The `gridComplex d N` is fully well-formed (`adj_symm`, `adj_vertex`,
`adj_ne` all proved without sorry). The gap is existence of panchromatic cells.

Session progress (2026-04-22):
- PROVED: `gridAdj_symm` (by cases on k.val: 0, d, interior)
- PROVED: `gridAdj_vertex` (vertex-set equality for all three cases)
- IDENTIFIED: `boundary_verts_on_face` and `boundary_doors_odd` are both false
- NEEDED: Unoriented SpernerTriangulation instance for the Freudenthal grid -/
theorem sperner_grid (d N : ℕ) (hN : 0 < N)
    (c : BaryPoint d N → Fin (d + 1))
    (hc : IsSperner c) :
    ∃ s : (gridComplex d N).Cell,
      CellComplex.IsPanchromatic c
        (gridComplex d N) s := by
  match d with
  | 0 =>
    -- d=0: only one color (Fin 1), every cell is panchromatic
    refine ⟨{
      verts := fun _ => ⟨fun _ => N, by simp [Fin.sum_univ_one]⟩
      incDir := fun k => k.elim0
      miss := ⟨0, by omega⟩
      miss_ne_inc := fun k => k.elim0
      step_inc := fun k => k.elim0
      step_dec := fun k => k.elim0
      step_same := fun k _j _h1 _h2 => k.elim0
      inc_injective := fun a _b _h => a.elim0 }, ?_⟩
    intro col
    -- col : Fin 1 = Fin (0+1); any two Fin 1 values are equal since both vals < 1
    refine ⟨⟨0, by omega⟩, ?_⟩
    apply Fin.ext; omega
  | 1 =>
    -- d=1: proved by discrete IVT via sperner_grid_one
    exact sperner_grid_one hN c hc
  | d + 2 =>
    -- d≥2: architecture blocked; unoriented SpernerTriangulation needed
    sorry

end SpernerGrid

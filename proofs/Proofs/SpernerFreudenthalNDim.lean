/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# Kuhn/Freudenthal triangulation of the dilated n-simplex — general-n PREP layer

Groundwork for eliminating the general-`n` `sperner_panchromatic` axiom in
`SpernerNDimMathlibOQ02.lean` (n = 0, 1, 2 are already axiom-free via
`SpernerFreudenthalSimplex.lean`).

## Coordinates

We work in *monotone partial-sum coordinates*: the dilated simplex `N·Δⁿ`
(points `y : Fin (n+1) → ℝ` with `y ≥ 0`, `∑ y = N`) is affinely equivalent
to the monotone region

    K = { z : Fin n → ℝ  |  0 ≤ z 0 ≤ z 1 ≤ ⋯ ≤ z (n-1) ≤ N }

via partial sums `z i = y 0 + ⋯ + y i` (and back via differences). Lattice
points of `K` are monotone `z : Fin n → ℕ` with all coordinates `≤ N`
(`IsGridPt` below).

## Cells

The Kuhn (Freudenthal) triangulation of the cube `[0,N]ⁿ` has top cells
indexed by a base vertex `b` and a permutation `σ` of `Fin n`, with vertex
chain

    w 0 = b,   w (i+1) = w i + e_{σ i}

(`kuhnVertex` below; vertex `w i` has incremented exactly the columns `j`
with `σ⁻¹ j < i`). The induced triangulation of `K` — hence of `N·Δⁿ` —
consists of exactly those cells whose `n+1` vertices all lie in `K`
(`IsKuhnCell`).

The main result of this file, `isKuhnCell_iff`, characterizes validity by a
condition on the base alone (`BaseCompatible`):

    (b, σ) is a cell of K  ↔  every `b j + 1 ≤ N`, and for `j < k`:
      `b j ≤ b k`, strictly whenever `σ⁻¹ j < σ⁻¹ k`.

Consistency check against the proven n = 2 development
(`SpernerFreudenthalSimplex.lean`): for `n = 2` the two permutations give
weakly monotone bases (`σ` with an inversion) and strictly monotone bases
(`σ = id`) with `b j ≤ N - 1`, i.e. `C(N+1,2) + C(N,2) = N²` cells — exactly
the Type-1/Type-2 cell count of the proven planar construction.

## Status

PREP layer only: definitions, vertex-chain structure lemmas, and the validity
characterization, all sorry-free and axiom-free. Pseudomanifold adjacency
(the pivot rules) and the Sperner parity argument are future sessions; the
plan is recorded in `research/problems/sperner-ndim-mathlib-oq-02/`.
-/

namespace SpernerFreudNDim

open Finset

variable {n : ℕ}

/-- Lattice point of the monotone region `K`: a monotone tuple with all
coordinates `≤ N`. These are the vertices of the induced triangulation of
the dilated simplex in partial-sum coordinates. -/
def IsGridPt (N : ℕ) (z : Fin n → ℕ) : Prop :=
  Monotone z ∧ ∀ j, z j ≤ N

/-- Vertex `i` of the Kuhn cell with base `b` and permutation `σ`:
`b` plus the sum of the unit vectors `e_{σ 0}, …, e_{σ (i-1)}` — i.e. column
`j` has been incremented exactly when `σ⁻¹ j < i`. -/
def kuhnVertex (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    Fin n → ℕ :=
  fun j => b j + (if (σ.symm j : ℕ) < (i : ℕ) then 1 else 0)

@[simp] theorem kuhnVertex_zero (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    kuhnVertex b σ 0 = b := by
  funext j
  simp [kuhnVertex]

@[simp] theorem kuhnVertex_last (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    kuhnVertex b σ (Fin.last n) = fun j => b j + 1 := by
  funext j
  simp [kuhnVertex, Fin.val_last, (σ.symm j).isLt]

/-- The vertex chain increments exactly one coordinate per step: passing from
vertex `i` to vertex `i+1` adds `1` in column `σ i` and nothing elsewhere. -/
theorem kuhnVertex_succ_apply (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (i : Fin n) (j : Fin n) :
    kuhnVertex b σ i.succ j
      = kuhnVertex b σ i.castSucc j + (if j = σ i then 1 else 0) := by
  by_cases hj : j = σ i
  · subst hj
    simp only [kuhnVertex, Equiv.symm_apply_apply, Fin.val_succ,
      Fin.val_castSucc]
    rw [if_pos (Nat.lt_succ_self (i : ℕ)), if_neg (lt_irrefl (i : ℕ))]
    simp
  · have hne : σ.symm j ≠ i := fun h => hj (by
      have h' := congrArg σ h
      simpa using h')
    have hval : (σ.symm j : ℕ) ≠ (i : ℕ) := fun h => hne (Fin.ext h)
    simp only [kuhnVertex, Fin.val_succ, Fin.val_castSucc, if_neg hj, add_zero]
    congr 1
    by_cases hlt : (σ.symm j : ℕ) < (i : ℕ)
    · rw [if_pos (by omega), if_pos hlt]
    · rw [if_neg (by omega), if_neg hlt]

/-- Vertices increase weakly along the chain, coordinatewise. -/
theorem kuhnVertex_mono (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    {i i' : Fin (n + 1)} (h : i ≤ i') (j : Fin n) :
    kuhnVertex b σ i j ≤ kuhnVertex b σ i' j := by
  have hv : (i : ℕ) ≤ (i' : ℕ) := Fin.le_iff_val_le_val.mp h
  simp only [kuhnVertex]
  split_ifs <;> omega

/-- Coordinate sum of vertex `i`: base sum plus `i`. This pins the "level" of
each vertex and is the engine behind vertex distinctness. -/
theorem kuhnVertex_sum (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    (i : Fin (n + 1)) :
    (∑ j, kuhnVertex b σ i j) = (∑ j, b j) + (i : ℕ) := by
  have hcomp :
      (∑ j, (if (σ.symm j : ℕ) < (i : ℕ) then 1 else 0))
        = ∑ t : Fin n, (if (t : ℕ) < (i : ℕ) then 1 else 0) :=
    Equiv.sum_comp σ.symm (fun t => if (t : ℕ) < (i : ℕ) then 1 else 0)
  have hcount :
      (∑ t : Fin n, (if (t : ℕ) < (i : ℕ) then 1 else 0)) = (i : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun m => if m < (i : ℕ) then 1 else 0) n]
    have hgen : ∀ m, (∑ t ∈ Finset.range m, (if t < (i : ℕ) then 1 else 0))
        = min m (i : ℕ) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        by_cases hm : m < (i : ℕ)
        · rw [if_pos hm]
          omega
        · rw [if_neg hm]
          omega
    rw [hgen n]
    have := i.isLt
    omega
  calc (∑ j, kuhnVertex b σ i j)
      = (∑ j, b j) + ∑ j, (if (σ.symm j : ℕ) < (i : ℕ) then 1 else 0) := by
        simp [kuhnVertex, Finset.sum_add_distrib]
    _ = (∑ j, b j) + (i : ℕ) := by rw [hcomp, hcount]

/-- The `n+1` vertices of a Kuhn cell are pairwise distinct. -/
theorem kuhnVertex_injective (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    Function.Injective (kuhnVertex b σ) := by
  intro i i' h
  have hsum := congrArg (fun w => ∑ j, w j) h
  simp only [kuhnVertex_sum] at hsum
  exact Fin.ext (by omega)

/-- `(b, σ)` is a cell of the induced triangulation of the monotone region:
all `n+1` vertices are lattice points of `K`. -/
def IsKuhnCell (N : ℕ) (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, IsGridPt N (kuhnVertex b σ i)

/-- Base-compatibility: the condition on `(b, σ)` alone that characterizes
cells of `K`. Column bound `b j + 1 ≤ N`, weak monotonicity of the base, and
*strict* growth on exactly those pairs `j < k` whose increments arrive in
order (`σ⁻¹ j < σ⁻¹ k`). -/
def BaseCompatible (N : ℕ) (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ j, b j + 1 ≤ N) ∧
    ∀ ⦃j k : Fin n⦄, j < k →
      b j ≤ b k ∧ ((σ.symm j : ℕ) < (σ.symm k : ℕ) → b j + 1 ≤ b k)

/-- **Validity characterization.** `(b, σ)` is a cell of the monotone region
iff its base is compatible: all the geometry of "every vertex stays monotone
and bounded" collapses to a finite family of pairwise conditions on `b`
governed by the inversion pattern of `σ`.

For `n = 2` this recovers the Type-1/Type-2 cell dichotomy of the proven
planar construction (`σ` with an inversion ⟷ weakly monotone base, `σ`
without ⟷ strictly monotone base). -/
theorem isKuhnCell_iff (N : ℕ) (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) :
    IsKuhnCell N b σ ↔ BaseCompatible N b σ := by
  constructor
  · intro hcell
    refine ⟨fun j => ?_, fun j k hjk => ?_⟩
    · -- column bound, read off at the last vertex where every column has
      -- been incremented
      have hb := (hcell (Fin.last n)).2 j
      simpa using hb
    · constructor
      · -- weak monotonicity, read off at vertex 0 (= the base itself)
        have hb := (hcell 0).1 (le_of_lt hjk)
        simpa using hb
      · -- strictness, read off at the vertex just after the `j`-column
        -- increment (where column `k` has not yet been incremented)
        intro hσ
        have hin : (σ.symm j : ℕ) + 1 < n + 1 := by
          have := (σ.symm j).isLt; omega
        have hmono := (hcell ⟨(σ.symm j : ℕ) + 1, hin⟩).1 (le_of_lt hjk)
        simp only [kuhnVertex] at hmono
        split_ifs at hmono <;> omega
  · rintro ⟨hbound, hpair⟩ i
    constructor
    · -- every vertex is monotone
      intro j k hjk
      rcases eq_or_lt_of_le hjk with rfl | hlt
      · exact le_rfl
      · obtain ⟨hp1, hp2⟩ := hpair hlt
        simp only [kuhnVertex]
        by_cases hj : (σ.symm j : ℕ) < (i : ℕ) <;>
          by_cases hk : (σ.symm k : ℕ) < (i : ℕ)
        · rw [if_pos hj, if_pos hk]; omega
        · -- column `j` incremented, column `k` not yet: the increments
          -- necessarily arrive in order, so strict growth applies
          rw [if_pos hj, if_neg hk]
          have hs := hp2 (by omega)
          omega
        · rw [if_neg hj, if_pos hk]; omega
        · rw [if_neg hj, if_neg hk]; omega
    · -- every vertex is bounded, via the last vertex
      intro j
      have hm := kuhnVertex_mono b σ (Fin.le_last i) j
      have hl : kuhnVertex b σ (Fin.last n) j = b j + 1 := by simp
      have hb := hbound j
      omega

/-- The base of a valid cell is itself a grid point (vertex 0). -/
theorem IsKuhnCell.base_isGridPt {N : ℕ} {b : Fin n → ℕ}
    {σ : Equiv.Perm (Fin n)} (h : IsKuhnCell N b σ) : IsGridPt N b := by
  simpa using h 0

end SpernerFreudNDim

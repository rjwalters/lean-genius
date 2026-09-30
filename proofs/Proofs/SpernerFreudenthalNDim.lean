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

section InteriorSwapPivot

/-! ### Interior swap pivot — existence half of the adjacency rules

First rung of the pseudomanifold pivot rules (facet-adjacency) for Kuhn
cells. Dropping an *interior* vertex `w (t+1)` (`t : Fin n` with
`t + 1 ≤ n - 1`, encoded as `t.succ : Fin (n+1)`) merges the two chain
steps in directions `σ t` and `σ t'` (`t' = t + 1` as positions). The
candidate mate through that facet is the **swap pivot**
`(b, σ * Equiv.swap t t')`, which takes the same two steps in the other
order:

* `kuhnVertex_mul_swap_of_ne` — every vertex except index `t.succ` is
  unchanged, so the two cells share the facet opposite the dropped vertex;
* `kuhnVertex_mul_swap_succ` — the one new vertex is
  `w t.castSucc + e_{σ t'}` (detour through the other corner of the merged
  2-step rectangle), and `kuhnVertex_mul_swap_succ_ne` shows it genuinely
  differs from the dropped vertex;
* `isKuhnCell_mul_swap_iff` — given `(b, σ)` valid, validity of the mate
  collapses to grid-membership of that single new vertex (the facet is
  interior to `K` exactly when it holds — the boundary/reflection
  characterization is the next rung);
* `mul_swap_mul_swap`, `mul_swap_ne` — the pivot is an involution and never
  returns the same cell, the shape needed for the future door-counting
  parity pairing.

NOT claimed here: uniqueness (no third cell through an interior facet),
the end pivots (`base`-shift at dropped index `0` or `n`), and the
boundary-facet characterization — those are the remaining rungs of the
adjacency layer. -/

/-- `symm` of a cell permutation post-composed (in position space) with a
swap: the swap migrates inside. -/
theorem mul_swap_symm_apply (σ : Equiv.Perm (Fin n)) (t t' j : Fin n) :
    (σ * Equiv.swap t t').symm j = Equiv.swap t t' (σ.symm j) := by
  rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]

/-- **Facet sharing.** Away from the dropped index `t + 1`, swapping the two
consecutive step directions does not change the vertex: the indicator
`σ⁻¹ j < i` is insensitive to exchanging positions `t` and `t' = t + 1`
unless `i` separates them, i.e. `i = t + 1`. -/
theorem kuhnVertex_mul_swap_of_ne (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    {t t' : Fin n} (htt : (t' : ℕ) = (t : ℕ) + 1) {i : Fin (n + 1)}
    (hi : (i : ℕ) ≠ (t : ℕ) + 1) :
    kuhnVertex b (σ * Equiv.swap t t') i = kuhnVertex b σ i := by
  funext j
  simp only [kuhnVertex, mul_swap_symm_apply]
  by_cases h1 : σ.symm j = t
  · rw [h1, Equiv.swap_apply_left]
    split_ifs <;> omega
  · by_cases h2 : σ.symm j = t'
    · rw [h2, Equiv.swap_apply_right]
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- **The pivoted vertex.** At the dropped index `t.succ` the swapped cell
detours through the other corner of the merged 2-step rectangle:
`w' (t+1) = w t + e_{σ t'}`. -/
theorem kuhnVertex_mul_swap_succ (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    {t t' : Fin n} (htt : (t' : ℕ) = (t : ℕ) + 1) :
    kuhnVertex b (σ * Equiv.swap t t') t.succ
      = fun j => kuhnVertex b σ t.castSucc j + (if j = σ t' then 1 else 0) := by
  funext j
  have htne : t ≠ t' := fun h => by
    have : (t : ℕ) = (t' : ℕ) := congrArg Fin.val h
    omega
  simp only [kuhnVertex, mul_swap_symm_apply, Fin.val_succ, Fin.val_castSucc]
  by_cases h1 : σ.symm j = t
  · have hjt : j = σ t := by rw [← h1, Equiv.apply_symm_apply]
    have hne : j ≠ σ t' := by
      rw [hjt]
      intro hh
      exact htne (σ.injective hh)
    rw [h1, Equiv.swap_apply_left, if_neg hne]
    split_ifs <;> omega
  · by_cases h2 : σ.symm j = t'
    · have hjt' : j = σ t' := by rw [← h2, Equiv.apply_symm_apply]
      rw [h2, Equiv.swap_apply_right, if_pos hjt']
      split_ifs <;> omega
    · have hne : j ≠ σ t' := fun hh => h2 (by rw [hh]; simp)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, if_neg hne]
      have hx : (σ.symm j : ℕ) ≠ (t : ℕ) := fun hh => h1 (Fin.ext hh)
      split_ifs <;> omega

/-- The pivoted vertex genuinely differs from the dropped one (they disagree
in column `σ t`), so the swap pivot produces a second cell through the
facet, not the same cell again. -/
theorem kuhnVertex_mul_swap_succ_ne (b : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
    {t t' : Fin n} (htt : (t' : ℕ) = (t : ℕ) + 1) :
    kuhnVertex b (σ * Equiv.swap t t') t.succ ≠ kuhnVertex b σ t.succ := by
  intro h
  have hcol := congrFun h (σ t)
  have htne : t ≠ t' := fun hh => by
    have : (t : ℕ) = (t' : ℕ) := congrArg Fin.val hh
    omega
  have hne : σ t ≠ σ t' := fun hh => htne (σ.injective hh)
  rw [kuhnVertex_mul_swap_succ b σ htt] at hcol
  simp only [kuhnVertex, Fin.val_succ, Fin.val_castSucc,
    Equiv.symm_apply_apply, if_neg hne] at hcol
  split_ifs at hcol <;> omega

/-- **Validity of the mate.** Given a valid cell, all vertices of its swap
pivot except the pivoted one are already grid points, so validity of the
mate is exactly grid-membership of the single new vertex. (The facet
opposite the dropped vertex is interior to `K` iff this holds; the
geometric boundary characterization is a future rung.) -/
theorem isKuhnCell_mul_swap_iff (N : ℕ) (b : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) {t t' : Fin n} (htt : (t' : ℕ) = (t : ℕ) + 1)
    (hcell : IsKuhnCell N b σ) :
    IsKuhnCell N b (σ * Equiv.swap t t')
      ↔ IsGridPt N (kuhnVertex b (σ * Equiv.swap t t') t.succ) := by
  constructor
  · intro h
    exact h t.succ
  · intro hnew i
    by_cases hi : (i : ℕ) = (t : ℕ) + 1
    · have hiv : i = t.succ := Fin.ext (by simp [hi])
      rw [hiv]
      exact hnew
    · rw [kuhnVertex_mul_swap_of_ne b σ htt hi]
      exact hcell i

/-- The swap pivot is an involution on cells: pivoting twice returns the
original permutation (the base is untouched throughout). -/
theorem mul_swap_mul_swap (σ : Equiv.Perm (Fin n)) (t t' : Fin n) :
    (σ * Equiv.swap t t') * Equiv.swap t t' = σ := by
  rw [mul_assoc, Equiv.swap_mul_self, mul_one]

/-- The swap pivot never returns the cell it started from. -/
theorem mul_swap_ne (σ : Equiv.Perm (Fin n)) {t t' : Fin n} (h : t ≠ t') :
    σ * Equiv.swap t t' ≠ σ := by
  intro hh
  have happ : (σ * Equiv.swap t t') t = σ t := by rw [hh]
  have : σ t' = σ t := by
    simpa [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using happ
  exact h (σ.injective this.symm)

end InteriorSwapPivot

section EndPivotBase

/-! ### End pivot at the base — existence half of the drop-0 adjacency rule

Second rung of the pseudomanifold pivot rules. Dropping the *base* vertex
`w 0 = b` leaves the facet `{w 1, …, w (n+1)}`; the candidate mate through
that facet takes the step in direction `σ 0` **last** instead of first: its
base is the original second vertex `w 1 = kuhnVertex b σ 1` and its
permutation is the cyclic rotation `σ * finRotate (n+1)` (position `i` steps
in direction `σ (i+1)`, and the last position wraps to `σ 0`).

Coordinates are `Fin (n+1)` throughout this section (so `σ 0` and
`finRotate` make sense); dimension-0 cells have no facet opposite their only
vertex, so nothing is lost.

* `kuhnVertex_mul_finRotate_castSucc` — vertices `0, …, n` of the mate are
  vertices `1, …, n+1` of the original: the two cells share the facet
  opposite the dropped base;
* `kuhnVertex_mul_finRotate_last` — the one new vertex is
  `w (n+1) + e_{σ 0}` (the chain overshoots the top vertex in the wrapped
  direction), and `kuhnVertex_mul_finRotate_last_ne` shows it differs from
  the dropped base;
* `isKuhnCell_mul_finRotate_iff` — given `(b, σ)` valid, validity of the
  mate collapses to grid-membership of that single new vertex;
* `mul_finRotate_last_apply`, `kuhnVertex_one_ne_base`, `endPivot_inj` — the
  mate's **last** step direction is `σ 0` (so this door is the mate's
  drop-last door, not another drop-0 door), the mate is never the original
  cell (the base strictly grows in column `σ 0` — this covers `n = 0`
  coordinates `Fin 1`, where `finRotate 1 = 1` leaves `σ` unchanged), and
  the pivot map is injective on cell data — the pairing shape for the
  future door-counting parity argument.

NOT claimed here: the symmetric drop-last pivot as a standalone rule (it is
the inverse pairing of this one, via `mul_finRotate_last_apply` and
`endPivot_inj`), the boundary-facet characterization, and uniqueness of the
mate — those are the remaining rungs of the adjacency layer. -/

/-- `(finRotate (n+1))⁻¹` sends `0` to the last position: the wrapped step
comes from the end of the rotated chain. -/
theorem finRotate_symm_zero : (finRotate (n + 1)).symm 0 = Fin.last n :=
  (finRotate (n + 1)).symm_apply_eq.mpr finRotate_last.symm

/-- `(finRotate (n+1))⁻¹` shifts a successor position down by one. -/
theorem finRotate_symm_succ (k : Fin n) :
    (finRotate (n + 1)).symm k.succ = k.castSucc :=
  (finRotate (n + 1)).symm_apply_eq.mpr
    (by rw [finRotate_succ_apply, Fin.coeSucc_eq_succ])

/-- `symm` of a cell permutation post-composed (in position space) with the
rotation: the rotation's inverse migrates inside. -/
theorem mul_finRotate_symm_apply (σ : Equiv.Perm (Fin (n + 1)))
    (j : Fin (n + 1)) :
    (σ * finRotate (n + 1)).symm j = (finRotate (n + 1)).symm (σ.symm j) := by
  rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply]

/-- **Facet sharing.** Vertex `i` of the end-pivot mate (base `w 1`,
permutation rotated) is vertex `i + 1` of the original cell, for every
`i ≤ n`: the mate walks the tail `w 1, …, w (n+1)` of the original chain
before taking the wrapped step. -/
theorem kuhnVertex_mul_finRotate_castSucc (b : Fin (n + 1) → ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    kuhnVertex (kuhnVertex b σ 1) (σ * finRotate (n + 1)) i.castSucc
      = kuhnVertex b σ i.succ := by
  funext j
  have hi : (i : ℕ) < n + 1 := i.isLt
  simp only [kuhnVertex, mul_finRotate_symm_apply]
  obtain hm | ⟨k, hm⟩ := Fin.eq_zero_or_eq_succ (σ.symm j) <;> rw [hm]
  · rw [finRotate_symm_zero]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_last, Fin.val_castSucc,
      Fin.val_succ]
    split_ifs <;> omega
  · rw [finRotate_symm_succ]
    simp only [Fin.val_one, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> omega

/-- **The pivoted vertex.** At the last index the mate overshoots the top
vertex of the original cell in the wrapped direction:
`w' (n+1) = w (n+1) + e_{σ 0}`. -/
theorem kuhnVertex_mul_finRotate_last (b : Fin (n + 1) → ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    kuhnVertex (kuhnVertex b σ 1) (σ * finRotate (n + 1)) (Fin.last (n + 1))
      = fun j => kuhnVertex b σ (Fin.last (n + 1)) j
          + (if j = σ 0 then 1 else 0) := by
  funext j
  simp only [kuhnVertex_last, kuhnVertex, Fin.val_one]
  by_cases h : j = σ 0
  · subst h
    rw [Equiv.symm_apply_apply, if_pos h, if_pos rfl]
    · omega
  · have hm : σ.symm j ≠ 0 := fun hh =>
      h (by rw [← Equiv.apply_symm_apply σ j, hh])
    have hval : (σ.symm j : ℕ) ≠ 0 := fun hz => hm (Fin.ext (by simp [hz]))
    rw [if_neg h, if_neg (by omega)]

/-- The pivoted vertex genuinely differs from the dropped base (it exceeds
it by `2` in column `σ 0`), so the end pivot produces a second cell through
the facet, not the same cell again. -/
theorem kuhnVertex_mul_finRotate_last_ne (b : Fin (n + 1) → ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    kuhnVertex (kuhnVertex b σ 1) (σ * finRotate (n + 1)) (Fin.last (n + 1))
      ≠ b := by
  intro h
  have hcol := congrFun h (σ 0)
  rw [kuhnVertex_mul_finRotate_last] at hcol
  simp only [kuhnVertex_last, if_pos rfl] at hcol
  omega

/-- **Validity of the mate.** Given a valid cell, all vertices of its end
pivot except the pivoted one are vertices of the original cell, so validity
of the mate is exactly grid-membership of the single new vertex. -/
theorem isKuhnCell_mul_finRotate_iff (N : ℕ) (b : Fin (n + 1) → ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) (hcell : IsKuhnCell N b σ) :
    IsKuhnCell N (kuhnVertex b σ 1) (σ * finRotate (n + 1))
      ↔ IsGridPt N
          (kuhnVertex (kuhnVertex b σ 1) (σ * finRotate (n + 1))
            (Fin.last (n + 1))) := by
  constructor
  · intro h
    exact h (Fin.last (n + 1))
  · intro hnew i
    induction i using Fin.lastCases with
    | last => exact hnew
    | cast i₀ =>
      rw [kuhnVertex_mul_finRotate_castSucc]
      exact hcell i₀.succ

/-- The mate's **last** step direction is the original's first: the shared
facet is the mate's drop-last facet, so the end pivots at the two ends pair
up with each other (never drop-0 with drop-0). -/
theorem mul_finRotate_last_apply (σ : Equiv.Perm (Fin (n + 1))) :
    (σ * finRotate (n + 1)) (Fin.last n) = σ 0 := by
  rw [Equiv.Perm.mul_apply, finRotate_last]

/-- The mate's base is never the original base (column `σ 0` grows), so the
end pivot never returns the cell it started from — even for `n = 0`
coordinates `Fin 1`, where the rotation is trivial and only the base moves. -/
theorem kuhnVertex_one_ne_base (b : Fin (n + 1) → ℕ)
    (σ : Equiv.Perm (Fin (n + 1))) :
    kuhnVertex b σ 1 ≠ b := by
  intro h
  have hcol := congrFun h (σ 0)
  simp [kuhnVertex] at hcol

/-- **Injectivity of the end pivot on cell data**: distinct cells have
distinct drop-0 mates. Together with `mul_finRotate_last_apply` this is the
bijection shape needed for the door-counting parity pairing. -/
theorem endPivot_inj (b b' : Fin (n + 1) → ℕ)
    (σ σ' : Equiv.Perm (Fin (n + 1)))
    (hb : kuhnVertex b σ 1 = kuhnVertex b' σ' 1)
    (hσ : σ * finRotate (n + 1) = σ' * finRotate (n + 1)) :
    b = b' ∧ σ = σ' := by
  have hσσ : σ = σ' := mul_right_cancel hσ
  subst hσσ
  refine ⟨funext fun j => ?_, rfl⟩
  have hj := congrFun hb j
  simp only [kuhnVertex] at hj
  split_ifs at hj <;> omega

end EndPivotBase

end SpernerFreudNDim

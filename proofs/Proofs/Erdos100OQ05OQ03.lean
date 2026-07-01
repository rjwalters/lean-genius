/-
Erdős Problem #100, Open Question 05, follow-up 03:
Equilateral point sets in ℝ^d — the sharp dimensional bound.

Parent problem (Erdős #100).  For a set A ⊆ ℝ² of n points with all pairwise
distances positive integers, how large must its diameter be?  The parent
gallery entry `erdos-100-oq-05` studies the *qualitative* higher-dimensional
picture (does the problem change in ℝ^d, d ≥ 3?).  Its two existing follow-ups
look at configurations with MANY distinct distances (explicit Heronian
simplices) and at the packing lower bound diam ≳ n^{1/d}.

This file studies the OPPOSITE extreme: point sets with a SINGLE distinct
distance — *equilateral sets* (a.k.a. equidistant sets, the vertex sets of
regular simplices).  Here the qualitative change with dimension is starkest and
completely clean.

## Main results

* `affineIndependent_of_equilateral` — in ANY real inner product space, a
  family of points that is `s`-equilateral (all pairwise distances equal to a
  fixed `s > 0`) is affinely independent.  This is the non-obvious extremal
  direction, proved by a short elementary inner-product argument (no Gram-matrix
  positive-definiteness machinery required).

* `equilateral_card_le_finrank_succ` — consequently, in a finite-dimensional
  real inner product space `E`, an equilateral set has at most
  `finrank ℝ E + 1` points.

* `equilateral_card_le_euclidean` — specialised to `EuclideanSpace ℝ (Fin d)`:
  an equilateral set has at most `d + 1` points.

* `equilateral_plane_card_le_three` — the planar (`d = 2`) case: at most `3`
  mutually equidistant points in ℝ² (the equilateral triangle is maximal).

* `stdSimplex_equilateral` / `exists_large_equilateral` — the `n` standard basis
  vectors of `EuclideanSpace ℝ (Fin n)` form an equilateral (distance `√2`),
  affinely independent set of `n` points.  Hence equilateral sets of size `n`
  exist in dimension `n` for every `n`.

## Qualitative answer to OQ-05

The maximum size of an equilateral set in `EuclideanSpace ℝ (Fin d)` lies in
`{d, d+1}` (lower bound `d` from the basis above; upper bound `d+1`).  In
particular it GROWS WITHOUT BOUND with the dimension.  This is a genuine
qualitative change from the plane, where at most `3` points can be mutually
equidistant.  Unlike the packing / distinct-distance phenomena, the equilateral
bound is dimension-free in statement and sharp up to the additive `±1`.

All results are fully verified, self-contained, and axiom-free.
-/
import Mathlib

open Finset
open scoped RealInnerProductSpace

namespace Erdos100OQ05Equilateral

/-- A family of points `p : ι → E` is **`s`-equilateral** if every two distinct
points are at distance exactly `s`. -/
def Equilateral {ι E : Type*} [PseudoMetricSpace E] (p : ι → E) (s : ℝ) : Prop :=
  ∀ i j, i ≠ j → dist (p i) (p j) = s

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Equilateral sets are affinely independent.**

In a real inner product space, if all pairwise distances of a family `p` equal a
fixed `s > 0`, then `p` is affinely independent.

Proof sketch.  Suppose `∑ w i = 0` and `∑ w i • p i = 0` over a finite index set
`t`.  For each `j ∈ t`, polarisation together with the two vanishing sums gives
`∑ i, w i * ‖p i - p j‖² = ∑ i, w i * ‖p i‖²` (call the common value `Q`), while
the equilateral hypothesis makes the left side `-s² * w j`.  Thus `-s² w j = Q`
for every `j`; summing this over `t` yields `card t * Q = 0`, so `Q = 0`, whence
`w j = 0`.  This is exactly the criterion `affineIndependent_iff`. -/
theorem affineIndependent_of_equilateral {ι : Type*} {p : ι → E} {s : ℝ}
    (hs : 0 < s) (h : Equilateral p s) : AffineIndependent ℝ p := by
  classical
  rw [affineIndependent_iff]
  intro t w hw hwp e he
  -- the "energy" that will be forced to vanish
  set Q : ℝ := ∑ i ∈ t, w i * ‖p i‖ ^ 2 with hQ
  -- key per-index identity: `-s² * w j = Q` for every `j ∈ t`
  have key : ∀ j ∈ t, -s ^ 2 * w j = Q := by
    intro j hj
    -- cross term ⟪∑ w i • p i, p j⟫ = 0
    have hcross : ∑ i ∈ t, w i * ⟪p i, p j⟫ = 0 := by
      have hrw : ⟪∑ i ∈ t, w i • p i, p j⟫ = ∑ i ∈ t, w i * ⟪p i, p j⟫ := by
        rw [sum_inner]
        exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_smul_left])
      rw [hwp, inner_zero_left] at hrw
      exact hrw.symm
    -- polarisation identity: LHS = Q
    have e1 : ∑ i ∈ t, w i * ‖p i - p j‖ ^ 2 = Q := by
      have hstep : ∑ i ∈ t, w i * ‖p i - p j‖ ^ 2
          = ∑ i ∈ t, (w i * ‖p i‖ ^ 2 - 2 * (w i * ⟪p i, p j⟫) + w i * ‖p j‖ ^ 2) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_sub_sq_real]; ring
      rw [hstep, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, hcross, hw]
      simp [hQ]
    -- equilateral evaluation: LHS = -s² * w j
    have e2 : ∑ i ∈ t, w i * ‖p i - p j‖ ^ 2 = -s ^ 2 * w j := by
      rw [← Finset.add_sum_erase t (fun i => w i * ‖p i - p j‖ ^ 2) hj]
      have hz : w j * ‖p j - p j‖ ^ 2 = 0 := by simp
      rw [hz, zero_add]
      have hcongr : ∑ i ∈ t.erase j, w i * ‖p i - p j‖ ^ 2
          = ∑ i ∈ t.erase j, s ^ 2 * w i := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hij : i ≠ j := Finset.ne_of_mem_erase hi
        have hd : ‖p i - p j‖ = s := by rw [← dist_eq_norm]; exact h i j hij
        rw [hd]; ring
      have hwerase : ∑ i ∈ t.erase j, w i = -w j := by
        have hae := Finset.add_sum_erase t w hj
        rw [hw] at hae; linarith
      rw [hcongr, ← Finset.mul_sum, hwerase]; ring
    -- combine
    rw [e2] at e1; exact e1
  -- sum `key` over `t`: `card t * Q = 0`
  have hsum : ∑ j ∈ t, (-s ^ 2 * w j) = ∑ j ∈ t, Q :=
    Finset.sum_congr rfl (fun j hj => key j hj)
  rw [← Finset.mul_sum, hw, mul_zero, Finset.sum_const, nsmul_eq_mul] at hsum
  -- hsum : 0 = card t * Q
  have hcard : (0 : ℝ) < (t.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨e, he⟩
  have hQ0 : Q = 0 := by
    rcases mul_eq_zero.mp hsum.symm with hc | hq
    · exact absurd hc (ne_of_gt hcard)
    · exact hq
  -- finally `-s² * w e = Q = 0` forces `w e = 0`
  have hfin := key e he
  rw [hQ0] at hfin
  have hs2 : s ^ 2 ≠ 0 := by positivity
  have : -s ^ 2 ≠ 0 := by simpa using hs2
  rcases mul_eq_zero.mp hfin with hne | hwe
  · exact absurd hne this
  · exact hwe

/-- **Dimensional upper bound.**  In a finite-dimensional real inner product
space, an equilateral set has at most `finrank + 1` points. -/
theorem equilateral_card_le_finrank_succ [FiniteDimensional ℝ E] {ι : Type*}
    [Fintype ι] {p : ι → E} {s : ℝ} (hs : 0 < s) (h : Equilateral p s) :
    Fintype.card ι ≤ Module.finrank ℝ E + 1 := by
  have hai := affineIndependent_of_equilateral hs h
  calc Fintype.card ι
      ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 := hai.card_le_finrank_succ
    _ ≤ Module.finrank ℝ E + 1 := by gcongr; exact Submodule.finrank_le _

end InnerProduct

section Euclidean

/-- **Equilateral sets in ℝ^d have at most `d + 1` points.** -/
theorem equilateral_card_le_euclidean {d : ℕ} {ι : Type*} [Fintype ι]
    {p : ι → EuclideanSpace ℝ (Fin d)} {s : ℝ} (hs : 0 < s) (h : Equilateral p s) :
    Fintype.card ι ≤ d + 1 := by
  have hb := equilateral_card_le_finrank_succ hs h
  rwa [finrank_euclideanSpace_fin] at hb

/-- **Planar case.**  At most three points in the plane can be mutually
equidistant — the equilateral triangle is the maximal equilateral set. -/
theorem equilateral_plane_card_le_three {ι : Type*} [Fintype ι]
    {p : ι → EuclideanSpace ℝ (Fin 2)} {s : ℝ} (hs : 0 < s) (h : Equilateral p s) :
    Fintype.card ι ≤ 3 :=
  equilateral_card_le_euclidean hs h

/-- The `n` standard basis vectors of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def stdSimplex (n : ℕ) : Fin n → EuclideanSpace ℝ (Fin n) :=
  fun i => EuclideanSpace.single i (1 : ℝ)

/-- The standard basis vectors are pairwise at distance `√2`: an equilateral set
of `n` points realising the lower end of the dimensional bound. -/
theorem stdSimplex_equilateral (n : ℕ) : Equilateral (stdSimplex n) (Real.sqrt 2) := by
  intro i j hij
  rw [dist_eq_norm]
  have h2 : ‖(stdSimplex n i) - stdSimplex n j‖ ^ 2 = 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [stdSimplex, inner_sub_left, inner_sub_right,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, map_one, one_mul]
    rw [if_neg hij, if_neg (Ne.symm hij)]
    norm_num
  rw [← Real.sqrt_sq (norm_nonneg (stdSimplex n i - stdSimplex n j)), h2]

/-- The standard basis vectors are affinely independent (a non-degenerate
regular simplex), a direct corollary of the equilateral criterion. -/
theorem stdSimplex_affineIndependent (n : ℕ) :
    AffineIndependent ℝ (stdSimplex n) :=
  affineIndependent_of_equilateral (Real.sqrt_pos.mpr (by norm_num)) (stdSimplex_equilateral n)

/-- **Unbounded equilateral sets.**  For every `n`, `EuclideanSpace ℝ (Fin n)`
contains an equilateral, affinely independent set of `n` points.  Hence the
maximum equilateral-set size grows without bound with the dimension — the
qualitative contrast with the plane's bound of `3`. -/
theorem exists_large_equilateral (n : ℕ) :
    ∃ p : Fin n → EuclideanSpace ℝ (Fin n),
      Equilateral p (Real.sqrt 2) ∧ AffineIndependent ℝ p :=
  ⟨stdSimplex n, stdSimplex_equilateral n, stdSimplex_affineIndependent n⟩

end Euclidean

end Erdos100OQ05Equilateral

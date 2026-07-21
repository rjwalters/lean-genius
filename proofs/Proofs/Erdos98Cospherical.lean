/-
# A constant row-sum of squared distances forces cospherical points

This file extracts, in full generality, the linear-algebraic core that closes
`h 5 = 3` for Erdős problem #98 (see `Proofs/Erdos98WIP01.lean`,
`three_le_h_five`).  There the pentagon-rigidity "C₅ endgame" was bypassed by a
purely metric observation:

> If every point of a finite family has the **same sum of squared distances to
> all the points** (a "constant row sum"), then all the points are equidistant
> from their centroid — they are cospherical.

The proof is the parallel-axis / centroid identity

  `n² · ‖Pᵢ − O‖²  =  n · (∑ₖ dist(Pᵢ,Pₖ)²)  −  ½ · (∑ₖ ∑ₗ dist(Pₖ,Pₗ)²)`,

where `O = n⁻¹ ∑ₖ Pₖ` is the centroid.  The second term is independent of `i`,
so equal row sums `∑ₖ dist(Pᵢ,Pₖ)²` give equal `‖Pᵢ − O‖²`.

Everything here holds in an arbitrary real inner-product space (any dimension),
generalising the `EuclideanSpace ℝ (Fin 2)`, `n = 5` special case used for
`h 5`.  In `Erdos98WIP01.lean` the hypothesis "constant row sum" is supplied for
a general-position two-distance `5`-set by `two_distance_row_sq_sum`
(row `= 2a² + 2b²`), and the cospherical conclusion contradicts
`NoFourConcyclic`.

Reference: https://erdosproblems.com/98
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos98Cospherical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The centroid (arithmetic mean) of a finite indexed family of points. -/
noncomputable def centroid {n : ℕ} (P : Fin n → E) : E := (n : ℝ)⁻¹ • ∑ k, P k

/-- `n • centroid = ∑ Pₖ` (needs `n ≠ 0`). -/
theorem nsmul_centroid {n : ℕ} (hn : 0 < n) (P : Fin n → E) :
    (n : ℝ) • centroid P = ∑ k, P k := by
  rw [centroid, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]

/-- The vector from the centroid to `Pᵢ`, scaled by `n`, is `∑ₖ (Pᵢ − Pₖ)`. -/
theorem nsmul_sub_centroid {n : ℕ} (hn : 0 < n) (P : Fin n → E) (i : Fin n) :
    ∑ k, (P i - P k) = (n : ℝ) • (P i - centroid P) := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_sub, nsmul_centroid hn P, Nat.cast_smul_eq_nsmul]

/-- Sum over `Fin n` of a constant real is `n` times it. -/
private theorem sum_const_fin {n : ℕ} (c : ℝ) : ∑ _l : Fin n, c = (n : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Centroid squared-distance identity.**  In any real inner-product space,
for `n` points `P : Fin n → E` with centroid `O = n⁻¹ ∑ₖ Pₖ`,

  `n² · ‖Pᵢ − O‖² = n · (∑ₖ dist(Pᵢ,Pₖ)²) − ½ · ∑ₖ ∑ₗ dist(Pₖ,Pₗ)²`.

The final double sum does not depend on `i`, which is the whole point:
equal row sums `∑ₖ dist(Pᵢ,Pₖ)²` force equal `‖Pᵢ − O‖²`. -/
theorem centroid_sq_dist_identity {n : ℕ} (hn : 0 < n) (P : Fin n → E) (i : Fin n) :
    (n : ℝ) ^ 2 * ‖P i - centroid P‖ ^ 2
      = (n : ℝ) * (∑ k, (dist (P i) (P k)) ^ 2)
        - (1 / 2) * ∑ k, ∑ l, (dist (P k) (P l)) ^ 2 := by
  -- Polarisation: ⟪Pᵢ−Pₖ, Pᵢ−Pₗ⟫ = ½(dᵢₖ² + dᵢₗ² − dₖₗ²).
  have pol : ∀ k l : Fin n, (inner ℝ (P i - P k) (P i - P l) : ℝ)
      = ((dist (P i) (P k)) ^ 2 + (dist (P i) (P l)) ^ 2 - (dist (P k) (P l)) ^ 2) / 2 := by
    intro k l
    have h := norm_sub_sq_real (P i - P k) (P i - P l)
    have esub : (P i - P k) - (P i - P l) = P l - P k := by abel
    rw [esub] at h
    rw [show ‖P i - P k‖ = dist (P i) (P k) from (dist_eq_norm _ _).symm,
        show ‖P i - P l‖ = dist (P i) (P l) from (dist_eq_norm _ _).symm,
        show ‖P l - P k‖ = dist (P k) (P l) from by rw [← dist_eq_norm, dist_comm]] at h
    linarith
  -- LHS = ‖∑ₖ (Pᵢ−Pₖ)‖².
  have hnormsq : ‖∑ k, (P i - P k)‖ ^ 2 = (n : ℝ) ^ 2 * ‖P i - centroid P‖ ^ 2 := by
    rw [nsmul_sub_centroid hn P i, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    ring
  -- Expand ‖∑‖² as a double inner-product sum.
  have hexpand : ‖∑ k, (P i - P k)‖ ^ 2
      = ∑ k, ∑ l, (inner ℝ (P i - P k) (P i - P l) : ℝ) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  -- Substitute polarisation.
  have hpolsum : ∑ k, ∑ l, (inner ℝ (P i - P k) (P i - P l) : ℝ)
      = ∑ k, ∑ l, ((dist (P i) (P k)) ^ 2 + (dist (P i) (P l)) ^ 2
          - (dist (P k) (P l)) ^ 2) / 2 := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    exact Finset.sum_congr rfl (fun l _ => pol k l)
  -- Inner sum over `l` for fixed `k`.
  have hinner : ∀ k : Fin n,
      ∑ l, ((dist (P i) (P k)) ^ 2 + (dist (P i) (P l)) ^ 2 - (dist (P k) (P l)) ^ 2) / 2
        = (n : ℝ) * ((dist (P i) (P k)) ^ 2 / 2)
          + (∑ l, (dist (P i) (P l)) ^ 2) / 2
          - (∑ l, (dist (P k) (P l)) ^ 2) / 2 := by
    intro k
    have hterm : ∀ l : Fin n,
        ((dist (P i) (P k)) ^ 2 + (dist (P i) (P l)) ^ 2 - (dist (P k) (P l)) ^ 2) / 2
          = (dist (P i) (P k)) ^ 2 / 2 + (dist (P i) (P l)) ^ 2 / 2
            - (dist (P k) (P l)) ^ 2 / 2 := by
      intro l; ring
    rw [Finset.sum_congr rfl (fun l _ => hterm l), Finset.sum_sub_distrib,
      Finset.sum_add_distrib, sum_const_fin, ← Finset.sum_div, ← Finset.sum_div]
  -- Outer sum over `k`.
  rw [← hnormsq, hexpand, hpolsum, Finset.sum_congr rfl (fun k _ => hinner k)]
  have hA : ∑ k, (n : ℝ) * ((dist (P i) (P k)) ^ 2 / 2)
      = (n : ℝ) * (∑ k, (dist (P i) (P k)) ^ 2) / 2 := by
    rw [← Finset.mul_sum, ← Finset.sum_div]; ring
  have hB : ∑ _k : Fin n, (∑ l, (dist (P i) (P l)) ^ 2) / 2
      = (n : ℝ) * (∑ l, (dist (P i) (P l)) ^ 2) / 2 := by
    rw [sum_const_fin]; ring
  have hC : ∑ k, (∑ l, (dist (P k) (P l)) ^ 2) / 2
      = (∑ k, ∑ l, (dist (P k) (P l)) ^ 2) / 2 := by
    rw [← Finset.sum_div]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC]
  ring

/-- **Cospherical from constant row sum (pairwise form).**  If every point has
the same sum of squared distances to all points, then any two points are
equidistant from the centroid. -/
theorem dist_centroid_eq_of_const_row {n : ℕ} (hn : 0 < n) (P : Fin n → E)
    (R : ℝ) (hrow : ∀ i, ∑ k, (dist (P i) (P k)) ^ 2 = R) (i j : Fin n) :
    dist (P i) (centroid P) = dist (P j) (centroid P) := by
  have hi := centroid_sq_dist_identity hn P i
  have hj := centroid_sq_dist_identity hn P j
  rw [hrow i] at hi
  rw [hrow j] at hj
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  have hsq : ‖P i - centroid P‖ ^ 2 = ‖P j - centroid P‖ ^ 2 :=
    mul_left_cancel₀ (ne_of_gt hn2) (by rw [hi, hj])
  have hnn1 : (0 : ℝ) ≤ ‖P i - centroid P‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖P j - centroid P‖ := norm_nonneg _
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖P i - centroid P‖ = Real.sqrt (‖P i - centroid P‖ ^ 2) := (Real.sqrt_sq hnn1).symm
    _ = Real.sqrt (‖P j - centroid P‖ ^ 2) := by rw [hsq]
    _ = ‖P j - centroid P‖ := Real.sqrt_sq hnn2

/-- **Cospherical from constant row sum (existence form).**  A nonempty finite
family whose points all have the same sum of squared distances to all points is
cospherical: there is a common centre (the centroid) and radius equidistant from
every point. -/
theorem exists_cosphere_of_const_row {n : ℕ} (hn : 0 < n) (P : Fin n → E)
    (R : ℝ) (hrow : ∀ i, ∑ k, (dist (P i) (P k)) ^ 2 = R) :
    ∃ (center : E) (radius : ℝ), ∀ i, dist (P i) center = radius :=
  ⟨centroid P, dist (P ⟨0, hn⟩) (centroid P),
    fun i => dist_centroid_eq_of_const_row hn P R hrow i ⟨0, hn⟩⟩

end Erdos98Cospherical

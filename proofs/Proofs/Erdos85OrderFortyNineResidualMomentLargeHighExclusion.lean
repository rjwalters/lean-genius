import Proofs.Erdos85OrderFortyNineResidualRootMoments

/-!
# Large-high-count residual moment exclusions

For `h = 19` or `h = 21`, the exact residual moments are incompatible
with the squared Perron lower bound and Cauchy--Schwarz on the remaining
residual roots.  These denominator-free arithmetic terminals isolate the
last two analytic inputs needed by the graph-level consumer.
-/

namespace Erdos85

/-- Cauchy--Schwarz for the squared roots after removing one distinguished
root.  This is the analytic inequality used by both large-high terminals. -/
theorem remaining_root_squares_cauchy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lambda : ι → ℝ) (i0 : ι) :
    (∑ i ∈ Finset.univ.erase i0, lambda i ^ 2) ^ 2 ≤
      ((Fintype.card ι - 1 : ℕ) : ℝ) *
        ∑ i ∈ Finset.univ.erase i0, lambda i ^ 4 := by
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ.erase i0) (f := fun i => lambda i ^ 2)
  simp_rw [show ∀ i, (lambda i ^ 2) ^ 2 = lambda i ^ 4 by
    intro i
    ring] at h
  simpa [Finset.card_erase_of_mem] using h

/-- Moment form of `remaining_root_squares_cauchy`: if `x` is the square of
one distinguished root, then the remaining second and fourth moments obey
the denominator-free inequality used below. -/
theorem residual_moment_cauchy_of_distinguished_root
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lambda : ι → ℝ) (i0 : ι) (second fourth x : ℝ)
    (hsecond : (∑ i, lambda i ^ 2) = second)
    (hfourth : (∑ i, lambda i ^ 4) = fourth)
    (hx : lambda i0 ^ 2 = x) :
    (second - x) ^ 2 ≤
      ((Fintype.card ι - 1 : ℕ) : ℝ) * (fourth - x ^ 2) := by
  have h := remaining_root_squares_cauchy lambda i0
  have hsecondErase :
      (∑ i ∈ Finset.univ.erase i0, lambda i ^ 2) = second - x := by
    have hadd := Finset.add_sum_erase Finset.univ
      (fun i => lambda i ^ 2) (Finset.mem_univ i0)
    rw [hsecond, hx] at hadd
    linarith
  have hfourthErase :
      (∑ i ∈ Finset.univ.erase i0, lambda i ^ 4) = fourth - x ^ 2 := by
    have hadd := Finset.add_sum_erase Finset.univ
      (fun i => lambda i ^ 4) (Finset.mem_univ i0)
    rw [hfourth] at hadd
    have hi : lambda i0 ^ 4 = x ^ 2 := by
      rw [show lambda i0 ^ 4 = (lambda i0 ^ 2) ^ 2 by ring, hx]
    rw [hi] at hadd
    linarith
  rwa [hsecondErase, hfourthErase] at h

/-- The `h = 19` residual profile is impossible once `x = ρ²` satisfies
the degree-square Rayleigh lower bound and the remaining-root Cauchy bound. -/
theorem false_of_orderFortyNine_h19_residualMoment_bounds
    (x : ℝ)
    (hrayleigh : (2686 : ℝ) / 49 ≤ x)
    (hcauchy : (110 - x) ^ 2 ≤ 12 * (3246 - x ^ 2)) : False := by
  nlinarith [sq_nonneg (x - (2686 : ℝ) / 49)]

/-- The analogous arithmetic terminal for `h = 21`. -/
theorem false_of_orderFortyNine_h21_residualMoment_bounds
    (x : ℝ)
    (hrayleigh : (2716 : ℝ) / 49 ≤ x)
    (hcauchy : (84 - x) ^ 2 ≤ 8 * (3108 - x ^ 2)) : False := by
  nlinarith [sq_nonneg (x - (2716 : ℝ) / 49)]

/-- Uniform wrapper for the two high-count cases eliminated by the fourth
residual moment. -/
theorem false_of_orderFortyNine_h19_or_h21_residualMoment_bounds
    (h : ℕ) (hh : h = 19 ∨ h = 21) (x : ℝ)
    (hrayleigh :
      (if h = 19 then (2686 : ℝ) / 49 else (2716 : ℝ) / 49) ≤ x)
    (hcauchy :
      if h = 19 then
        (110 - x) ^ 2 ≤ 12 * (3246 - x ^ 2)
      else
        (84 - x) ^ 2 ≤ 8 * (3108 - x ^ 2)) : False := by
  rcases hh with rfl | rfl
  · exact false_of_orderFortyNine_h19_residualMoment_bounds x
      (by simpa using hrayleigh) (by simpa using hcauchy)
  · exact false_of_orderFortyNine_h21_residualMoment_bounds x
      (by simpa using hrayleigh) (by simpa using hcauchy)

end Erdos85

/-
  Aristotle targets for TaylorSinCosConvergenceOQ03
  Routine supporting lemmas for automated proof search.
  See TaylorSinCosConvergenceOQ03.lean for the main formalization.

  Criteria for inclusion:
  - All results are well-known analysis facts
  - Alternating series estimation, monotonicity, convergence
  - Clean theorem statements with no definition sorries
  - No axioms, no open conjectures
-/
import Mathlib

open Finset Real Set
open scoped Nat

namespace AlternatingSeriesEstimation

/-- The absolute value of the k-th term of the sin Taylor series. -/
noncomputable def sinTermAbs (x : ℝ) (k : ℕ) : ℝ :=
  |x| ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)

/-- The absolute value of the k-th term of the cos Taylor series. -/
noncomputable def cosTermAbs (x : ℝ) (k : ℕ) : ℝ :=
  |x| ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)

/-- Alternating Series Estimation (partial sum form):
    For a decreasing non-negative sequence, the alternating partial sum
    through an even index lies between 0 and a₀. -/
theorem alternating_partial_sum_even_bounds {a : ℕ → ℝ}
    (ha_pos : ∀ k, 0 ≤ a k) (ha_dec : Antitone a) (m : ℕ) :
    0 ≤ ∑ k ∈ range (2 * m + 1), (-1 : ℝ) ^ k * a k ∧
    ∑ k ∈ range (2 * m + 1), (-1 : ℝ) ^ k * a k ≤ a 0 := by
  suffices h : a (2 * m) ≤ ∑ k ∈ range (2 * m + 1), (-1 : ℝ) ^ k * a k ∧
      ∑ k ∈ range (2 * m + 1), (-1 : ℝ) ^ k * a k ≤ a 0 from
    ⟨le_trans (ha_pos _) h.1, h.2⟩
  induction m with
  | zero => simp [sum_range_one]
  | succ n ih =>
    set S := ∑ k ∈ range (2 * n + 1), (-1 : ℝ) ^ k * a k
    have h_sum : ∑ k ∈ range (2 * (n + 1) + 1), (-1 : ℝ) ^ k * a k =
        S - a (2 * n + 1) + a (2 * (n + 1)) := by
      have h1 : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
      rw [h1, sum_range_succ, sum_range_succ]
      have hodd : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_pow ⟨n, by omega⟩
      have heven : (-1 : ℝ) ^ (2 * n + 1 + 1) = 1 := by rw [pow_succ, hodd]; ring
      have hidx : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [hodd, heven, hidx]
      ring
    rw [h_sum]
    exact ⟨by linarith [ih.1, ha_dec (show 2 * n ≤ 2 * n + 1 by omega)],
           by linarith [ih.2, ha_dec (show 2 * n + 1 ≤ 2 * (n + 1) by omega)]⟩

/-- Alternating Series Estimation (tail bound):
    For a decreasing non-negative sequence converging to 0,
    the tail after n terms is bounded by aₙ. -/
theorem alternating_tail_bound {a : ℕ → ℝ}
    (ha_pos : ∀ k, 0 ≤ a k) (ha_dec : Antitone a)
    (ha_lim : Filter.Tendsto a Filter.atTop (nhds 0))
    (ha_sum : Summable (fun k => (-1 : ℝ) ^ k * a k)) (n : ℕ) :
    ‖∑' k, (-1 : ℝ) ^ (k + n) * a (k + n)‖ ≤ a n := by
  sorry

/-- Sin series terms are eventually decreasing for |x| ≤ 1.
    PROVED in main file via pow_le_pow_of_le_one + factorial_mono. -/
theorem sinTermAbs_antitone (x : ℝ) (hx : |x| ≤ 1) :
    Antitone (sinTermAbs x) := by
  intro m n hmn
  unfold sinTermAbs
  apply div_le_div
  · exact pow_nonneg (abs_nonneg x) _
  · exact pow_le_pow_of_le_one (abs_nonneg x) hx (by omega)
  · exact Nat.cast_pos.mpr (Nat.factorial_pos _)
  · exact Nat.cast_le.mpr (Nat.factorial_mono (by omega))

/-- Sin series terms tend to 0 for any fixed x.
    PROVED in main file via composition with tendsto_pow_div_factorial_atTop. -/
theorem sinTermAbs_tendsto (x : ℝ) :
    Filter.Tendsto (sinTermAbs x) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n => |x| ^ n / (Nat.factorial n : ℝ))
      Filter.atTop (nhds 0) := by
    have := Real.tendsto_pow_div_factorial_atTop |x|
    simp only [Nat.cast_ofNat] at this ⊢
    exact this
  have hf : Filter.Tendsto (fun k => 2 * k + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun n => ⟨n, by omega⟩
  have heq : sinTermAbs x = (fun n => |x| ^ n / (Nat.factorial n : ℝ)) ∘
      (fun k => 2 * k + 1) := by
    ext k; simp [sinTermAbs, Function.comp]
  rw [heq]
  exact hg.comp hf

/-- Alternating series remainder bound for sin Taylor series. -/
theorem sin_alternating_remainder (n : ℕ) (x : ℝ) :
    ‖Real.sin x - ∑ k ∈ range n,
      (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)‖ ≤
    sinTermAbs x n := by
  sorry

/-- Alternating series remainder bound for cos Taylor series. -/
theorem cos_alternating_remainder (n : ℕ) (x : ℝ) :
    ‖Real.cos x - ∑ k ∈ range n,
      (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)‖ ≤
    cosTermAbs x n := by
  sorry

end AlternatingSeriesEstimation

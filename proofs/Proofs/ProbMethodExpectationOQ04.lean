/-
  First Moment Method — OQ-04: non-strict averaging (some outcome meets the mean)

  The gallery entry `ProbMethodExpectation` proves the *strict* first moment
  principle: `E[X] > t ⟹ ∃ ω, X(ω) > t` (`first_moment_principle`) and its dual.
  The strict form cannot conclude anything at the threshold `E[X] = t`, yet the
  most common use of the probabilistic method is exactly the non-strict statement
  *"some outcome is at least the average"* — used to extract a witness meeting the
  expectation.  This file supplies the non-strict averaging lemmas.

  * `exists_ge_of_card_mul_le` / `exists_le_of_card_mul_ge` — the division-free
    practical forms: `t·|s| ≤ ∑ f ⟹ ∃ a, t ≤ f a` (and dual).  This is the shape
    actually used in lower-bound arguments (avoids dividing by `|s|`).
  * `exists_ge_average` / `exists_le_average` — *some element is at least / at most
    the mean*: `∃ a ∈ s, (∑ f)/|s| ≤ f a` and the dual.  The pigeonhole core of the
    first moment method.
  * `first_moment_ge` / `first_moment_le` — the non-strict threshold forms,
    `E[X] ≥ t ⟹ ∃ a, f a ≥ t`, completing the strict `first_moment_principle` at
    the boundary.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Spencer, *The Probabilistic Method*, Ch. 2 (first moment).
-/

import Mathlib

namespace ProbMethod.ExpectationOQ04

open Finset BigOperators

variable {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℚ} {t : ℚ}

/-- **Division-free first moment (≥).**  If `t·|s| ≤ ∑ f` over a nonempty set, then
    some element is at least `t`.  This is the practical lower-bound shape of the
    first moment method (no division by `|s|`). -/
theorem exists_ge_of_card_mul_le (hs : s.Nonempty) (h : t * s.card ≤ s.sum f) :
    ∃ a ∈ s, t ≤ f a := by
  by_contra hc
  push_neg at hc
  have hlt : s.sum f < s.sum (fun _ => t) := Finset.sum_lt_sum_of_nonempty hs hc
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at hlt
  linarith

/-- **Division-free first moment (≤).**  If `∑ f ≤ t·|s|`, some element is at most
    `t`. -/
theorem exists_le_of_card_mul_ge (hs : s.Nonempty) (h : s.sum f ≤ t * s.card) :
    ∃ a ∈ s, f a ≤ t := by
  by_contra hc
  push_neg at hc
  have hlt : s.sum (fun _ => t) < s.sum f := Finset.sum_lt_sum_of_nonempty hs hc
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at hlt
  linarith

/-- **Some element is at least the mean.**  `∃ a ∈ s, (∑ f)/|s| ≤ f a`. -/
theorem exists_ge_average (hs : s.Nonempty) :
    ∃ a ∈ s, (s.sum f) / s.card ≤ f a := by
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs.card_pos)
  refine exists_ge_of_card_mul_le hs (le_of_eq ?_)
  field_simp

/-- **Some element is at most the mean.**  `∃ a ∈ s, f a ≤ (∑ f)/|s|`. -/
theorem exists_le_average (hs : s.Nonempty) :
    ∃ a ∈ s, f a ≤ (s.sum f) / s.card := by
  have hne : (s.card : ℚ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hs.card_pos)
  refine exists_le_of_card_mul_ge hs (le_of_eq ?_)
  field_simp

/-- **Non-strict first moment principle (≥).**  If the average is at least `t`,
    some element is at least `t` — the boundary case the strict
    `first_moment_principle` cannot reach. -/
theorem first_moment_ge (hs : s.Nonempty) (havg : t ≤ (s.sum f) / s.card) :
    ∃ a ∈ s, t ≤ f a := by
  obtain ⟨a, ha, hfa⟩ := exists_ge_average hs
  exact ⟨a, ha, le_trans havg hfa⟩

/-- **Non-strict first moment principle (≤).**  Dual of `first_moment_ge`. -/
theorem first_moment_le (hs : s.Nonempty) (havg : (s.sum f) / s.card ≤ t) :
    ∃ a ∈ s, f a ≤ t := by
  obtain ⟨a, ha, hfa⟩ := exists_le_average hs
  exact ⟨a, ha, le_trans hfa havg⟩

end ProbMethod.ExpectationOQ04

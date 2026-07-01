/-
  First Moment Method — OQ-05: the WEIGHTED (non-uniform) first moment principle

  The gallery entry `ProbMethodExpectation` and its child `…OQ04` both work with the
  *uniform* average `(∑ f)/|s|`: every outcome is weighted equally.  The genuine
  probabilistic setting, however, attaches an arbitrary finite probability
  distribution (or, more generally, a nonnegative weighting) to the outcomes, and
  the expectation is the weighted sum `E_w[X] = ∑ w a · f a`.  This file proves the
  first moment principle in that general form.  The uniform results are recovered as
  the special case `w ≡ 1` (see `weighted_generalizes_uniform`), so this strictly
  subsumes the parent.

  Setup: `w : α → ℚ` with `w a ≥ 0` on `s`, total weight `W := ∑_{a∈s} w a`.  The
  weighted mean is `(∑ w·f)/W` when `W > 0`.

  Results:
  * `weighted_first_moment_gt` / `_lt` — strict:  if the weighted mean beats `t`,
    some *supported* outcome (`w a > 0`) beats `t`.  Getting `w a > 0` on the witness
    is strictly stronger than the uniform statement — zero-weight outcomes are
    genuinely irrelevant.
  * `weighted_first_moment_ge` / `_le` — non-strict threshold forms `E_w ≥ t ⟹
    ∃ a, w a > 0 ∧ f a ≥ t`.
  * `exists_ge_weighted_mean` / `exists_le_weighted_mean` — the titular statement:
    *some outcome meets the weighted average* — with the sharper conclusion that the
    witness carries positive weight.
  * `weighted_mean_mem_Icc` — the weighted mean lies between the min and max of the
    supported values (sandwich form).
  * `weighted_generalizes_uniform` — with all weights `1`, `E_w = (∑ f)/|s|`, so the
    uniform first-moment results are the `w ≡ 1` instance.

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Alon–Spencer, *The Probabilistic Method*, Ch. 2 (first moment / linearity
  of expectation for general finite distributions).
-/

import Mathlib

namespace ProbMethod.ExpectationOQ05

open Finset BigOperators

variable {α : Type*} {s : Finset α} {w f : α → ℚ} {t : ℚ}

/-- The total weight of a nonnegatively-weighted set is nonnegative. -/
theorem totalWeight_nonneg (hw : ∀ a ∈ s, 0 ≤ w a) : 0 ≤ s.sum w :=
  Finset.sum_nonneg hw

/-- **Weighted first moment (strict, ≥).**  If the weighted mean exceeds `t`, then
    some *supported* outcome (positive weight) exceeds `t`.  Equivalent hypothesis
    `∑ w·f > t · W` avoids dividing by the total weight `W`. -/
theorem weighted_first_moment_gt (hw : ∀ a ∈ s, 0 ≤ w a)
    (h : t * s.sum w < s.sum (fun a => w a * f a)) :
    ∃ a ∈ s, 0 < w a ∧ t < f a := by
  by_contra hc
  push_neg at hc
  -- On every outcome, `w a * f a ≤ w a * t`: either `w a = 0`, or `w a > 0` forces
  -- `f a ≤ t` by `hc`.
  have hpoint : ∀ a ∈ s, w a * f a ≤ w a * t := by
    intro a ha
    rcases eq_or_lt_of_le (hw a ha) with hwa | hwa
    · simp [← hwa]
    · exact mul_le_mul_of_nonneg_left (hc a ha hwa) (le_of_lt hwa)
  have hsum : s.sum (fun a => w a * f a) ≤ s.sum (fun a => w a * t) :=
    Finset.sum_le_sum hpoint
  have : s.sum (fun a => w a * t) = s.sum w * t := by
    rw [← Finset.sum_mul]
  rw [this] at hsum
  nlinarith [hsum]

/-- **Weighted first moment (strict, ≤ / dual).**  If the weighted mean is below `t`,
    some supported outcome is below `t`. -/
theorem weighted_first_moment_lt (hw : ∀ a ∈ s, 0 ≤ w a)
    (h : s.sum (fun a => w a * f a) < t * s.sum w) :
    ∃ a ∈ s, 0 < w a ∧ f a < t := by
  by_contra hc
  push_neg at hc
  have hpoint : ∀ a ∈ s, w a * t ≤ w a * f a := by
    intro a ha
    rcases eq_or_lt_of_le (hw a ha) with hwa | hwa
    · simp [← hwa]
    · exact mul_le_mul_of_nonneg_left (hc a ha hwa) (le_of_lt hwa)
  have hsum : s.sum (fun a => w a * t) ≤ s.sum (fun a => w a * f a) :=
    Finset.sum_le_sum hpoint
  have : s.sum (fun a => w a * t) = s.sum w * t := by
    rw [← Finset.sum_mul]
  rw [this] at hsum
  nlinarith [hsum]

/-- **Weighted first moment (non-strict, ≥).**  If the weighted mean is at least `t`
    over a set of positive total weight, then some supported outcome is `≥ t`. -/
theorem weighted_first_moment_ge (hw : ∀ a ∈ s, 0 ≤ w a) (hW : 0 < s.sum w)
    (h : t * s.sum w ≤ s.sum (fun a => w a * f a)) :
    ∃ a ∈ s, 0 < w a ∧ t ≤ f a := by
  by_contra hc
  push_neg at hc
  -- Every supported outcome has `f a < t`, so weighted sum is *strictly* below `t·W`.
  have hpoint : ∀ a ∈ s, w a * f a ≤ w a * t := by
    intro a ha
    rcases eq_or_lt_of_le (hw a ha) with hwa | hwa
    · simp [← hwa]
    · exact mul_le_mul_of_nonneg_left (le_of_lt (hc a ha hwa)) (le_of_lt hwa)
  -- Since `W > 0`, at least one outcome carries positive weight; there the point
  -- inequality is strict, upgrading the sum bound to strict.
  have hex : ∃ a ∈ s, 0 < w a := by
    by_contra hnone
    push_neg at hnone
    have : s.sum w = 0 :=
      Finset.sum_eq_zero (fun a ha => le_antisymm (hnone a ha) (hw a ha))
    rw [this] at hW; exact lt_irrefl _ hW
  obtain ⟨b, hb, hwb⟩ := hex
  have hstrict : s.sum (fun a => w a * f a) < s.sum (fun a => w a * t) :=
    Finset.sum_lt_sum hpoint ⟨b, hb, by
      exact mul_lt_mul_of_pos_left (hc b hb hwb) hwb⟩
  have : s.sum (fun a => w a * t) = s.sum w * t := by
    rw [← Finset.sum_mul]
  rw [this] at hstrict
  nlinarith [hstrict]

/-- **Weighted first moment (non-strict, ≤ / dual).** -/
theorem weighted_first_moment_le (hw : ∀ a ∈ s, 0 ≤ w a) (hW : 0 < s.sum w)
    (h : s.sum (fun a => w a * f a) ≤ t * s.sum w) :
    ∃ a ∈ s, 0 < w a ∧ f a ≤ t := by
  by_contra hc
  push_neg at hc
  have hpoint : ∀ a ∈ s, w a * t ≤ w a * f a := by
    intro a ha
    rcases eq_or_lt_of_le (hw a ha) with hwa | hwa
    · simp [← hwa]
    · exact mul_le_mul_of_nonneg_left (le_of_lt (hc a ha hwa)) (le_of_lt hwa)
  have hex : ∃ a ∈ s, 0 < w a := by
    by_contra hnone
    push_neg at hnone
    have : s.sum w = 0 :=
      Finset.sum_eq_zero (fun a ha => le_antisymm (hnone a ha) (hw a ha))
    rw [this] at hW; exact lt_irrefl _ hW
  obtain ⟨b, hb, hwb⟩ := hex
  have hstrict : s.sum (fun a => w a * t) < s.sum (fun a => w a * f a) :=
    Finset.sum_lt_sum hpoint ⟨b, hb, by
      exact mul_lt_mul_of_pos_left (hc b hb hwb) hwb⟩
  have : s.sum (fun a => w a * t) = s.sum w * t := by
    rw [← Finset.sum_mul]
  rw [this] at hstrict
  nlinarith [hstrict]

/-- **Some outcome meets the weighted average (≥).**  There is a supported outcome
    whose value is at least the weighted mean `(∑ w·f)/W`.  This is the pigeonhole
    core of the first moment method in the general (non-uniform) setting. -/
theorem exists_ge_weighted_mean (hw : ∀ a ∈ s, 0 ≤ w a) (hW : 0 < s.sum w) :
    ∃ a ∈ s, 0 < w a ∧ (s.sum (fun a => w a * f a)) / s.sum w ≤ f a := by
  obtain ⟨a, ha, hwa, hle⟩ :=
    weighted_first_moment_ge (t := (s.sum (fun a => w a * f a)) / s.sum w) hw hW
      (by rw [div_mul_cancel₀ _ (ne_of_gt hW)])
  exact ⟨a, ha, hwa, hle⟩

/-- **Some outcome meets the weighted average (≤ / dual).** -/
theorem exists_le_weighted_mean (hw : ∀ a ∈ s, 0 ≤ w a) (hW : 0 < s.sum w) :
    ∃ a ∈ s, 0 < w a ∧ f a ≤ (s.sum (fun a => w a * f a)) / s.sum w := by
  obtain ⟨a, ha, hwa, hle⟩ :=
    weighted_first_moment_le (t := (s.sum (fun a => w a * f a)) / s.sum w) hw hW
      (by rw [div_mul_cancel₀ _ (ne_of_gt hW)])
  exact ⟨a, ha, hwa, hle⟩

/-- **Sandwich: the weighted mean lies between the extreme supported values.**
    If every supported outcome satisfies `lo ≤ f a ≤ hi`, then the weighted mean is
    itself in `[lo, hi]`.  (A convex combination stays within the range of its
    inputs.) -/
theorem weighted_mean_mem_Icc {lo hi : ℚ} (hw : ∀ a ∈ s, 0 ≤ w a) (hW : 0 < s.sum w)
    (hlo : ∀ a ∈ s, 0 < w a → lo ≤ f a) (hhi : ∀ a ∈ s, 0 < w a → f a ≤ hi) :
    lo ≤ (s.sum (fun a => w a * f a)) / s.sum w ∧
      (s.sum (fun a => w a * f a)) / s.sum w ≤ hi := by
  have hpoint_lo : ∀ a ∈ s, w a * lo ≤ w a * f a := by
    intro a ha
    rcases eq_or_lt_of_le (hw a ha) with hwa | hwa
    · simp [← hwa]
    · exact mul_le_mul_of_nonneg_left (hlo a ha hwa) (le_of_lt hwa)
  have hpoint_hi : ∀ a ∈ s, w a * f a ≤ w a * hi := by
    intro a ha
    rcases eq_or_lt_of_le (hw a ha) with hwa | hwa
    · simp [← hwa]
    · exact mul_le_mul_of_nonneg_left (hhi a ha hwa) (le_of_lt hwa)
  have hsum_lo : s.sum w * lo ≤ s.sum (fun a => w a * f a) := by
    have := Finset.sum_le_sum hpoint_lo
    rwa [← Finset.sum_mul] at this
  have hsum_hi : s.sum (fun a => w a * f a) ≤ s.sum w * hi := by
    have := Finset.sum_le_sum hpoint_hi
    rwa [← Finset.sum_mul] at this
  constructor
  · rw [le_div_iff₀ hW, mul_comm]; exact hsum_lo
  · rw [div_le_iff₀ hW, mul_comm]; exact hsum_hi

/-- **Weighted mean generalizes the uniform average.**  Taking every weight equal to
    `1`, the weighted sum `∑ (1 · f a)` is the plain sum and the total weight is the
    cardinality, so `E_w = (∑ f)/|s|`.  The uniform first-moment results of the parent
    are therefore the `w ≡ 1` instance of the weighted ones. -/
theorem weighted_generalizes_uniform :
    s.sum (fun a => (1 : ℚ) * f a) = s.sum f ∧ s.sum (fun _ : α => (1 : ℚ)) = s.card := by
  refine ⟨by simp, ?_⟩
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

end ProbMethod.ExpectationOQ05

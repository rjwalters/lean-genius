/-
  Quantitative Paley-Zygmund Inequality

  Extension of the second moment method with a threshold parameter θ.

  The standard Paley-Zygmund inequality states:
    P[X > θ · E[X]] ≥ (1 - θ)² · E[X]² / E[X²]

  for non-negative X, 0 ≤ θ ≤ 1. The qualitative version (θ = 0, proved in
  ProbMethodSecondMoment.lean) says P[X > 0] > 0 when E[X] > 0.

  The quantitative version provides a lower bound on the probability that X
  exceeds any fraction θ of its mean. This is a fundamental tool in the
  probabilistic method for combinatorics (Alon-Spencer, Chapter 4).

  This file proves the finite/rational version over Finset, consistent with
  the infrastructure in ProbMethodSecondMoment.lean.
-/
import Mathlib
import Proofs.ProbMethodSecondMoment

set_option linter.unusedVariables false

namespace ProbMethod.SecondMoment

/-
## Quantitative Paley-Zygmund Inequality

For f : α → ℚ non-negative on Finset s, with 0 ≤ θ < 1:

  (1-θ)² · (∑ f)² ≤ |{a : f(a) > θ·μ}| · ∑ f²

where μ = (∑ f) / |s| is the mean.
-/

/-- Cauchy-Schwarz for finite sums (re-export for convenience). -/
private lemma sq_sum_le {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) :
    (s.sum f) ^ 2 ≤ ↑s.card * s.sum (fun a => f a ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hsq : 0 ≤ s.sum (fun b => (f a - f b) ^ 2) :=
      Finset.sum_nonneg (fun b _ => sq_nonneg _)
    have hexpand : s.sum (fun b => (f a - f b) ^ 2) =
        ↑s.card * (f a) ^ 2 - 2 * f a * s.sum f + s.sum (fun b => (f b) ^ 2) := by
      simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.mul_sum]
      ring
    push_cast [Nat.cast_add, Nat.cast_one]
    nlinarith

/-- The quantitative Paley-Zygmund inequality (counting form).

  For non-negative f on a Finset with positive sum, and threshold 0 ≤ θ < 1:
  the number of elements exceeding θ times the mean satisfies

    (1-θ)² · (∑ f)² ≤ |above| · ∑ f²

  where above = {a ∈ s : f(a) > θ · mean}. -/
theorem paley_zygmund_quantitative {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} {θ : ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    (1 - θ) ^ 2 * (s.sum f) ^ 2 ≤
      ↑(s.filter (fun a => θ * (s.sum f / ↑s.card) < f a)).card *
      s.sum (fun a => f a ^ 2) := by
  set μ := s.sum f / ↑s.card with hμ_def
  set above := s.filter (fun a => θ * μ < f a) with habove_def
  set below := s.filter (fun a => ¬(θ * μ < f a)) with hbelow_def
  have hn_pos : (0 : ℚ) < ↑s.card := Nat.cast_pos.mpr (Finset.Nonempty.card_pos hs)
  have hn_ne : (↑s.card : ℚ) ≠ 0 := ne_of_gt hn_pos
  -- Step 1: Decompose sum f = sum over above + sum over below
  have hsum_split : s.sum f = above.sum f + below.sum f := by
    rw [habove_def, hbelow_def]
    exact (Finset.sum_filter_add_sum_filter_not s (fun a => θ * μ < f a) f).symm
  -- Step 2: Bound below sum ≤ θ · sum f
  have hbelow_le : ∀ a ∈ below, f a ≤ θ * μ := by
    intro a ha
    exact le_of_not_lt (Finset.mem_filter.mp ha).2
  have hbelow_sum : below.sum f ≤ ↑below.card * (θ * μ) := by
    calc below.sum f ≤ below.sum (fun _ => θ * μ) :=
            Finset.sum_le_sum (fun a ha => hbelow_le a ha)
      _ = ↑below.card * (θ * μ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
  have hbelow_card_le : (↑below.card : ℚ) ≤ ↑s.card := by
    exact_mod_cast Finset.card_filter_le s _
  have hμ_eq : ↑s.card * μ = s.sum f := by
    rw [hμ_def, mul_div_cancel₀ _ hn_ne]
  have hbelow_bound : below.sum f ≤ θ * s.sum f := by
    calc below.sum f ≤ ↑below.card * (θ * μ) := hbelow_sum
      _ ≤ ↑s.card * (θ * μ) := by nlinarith [hθ0, hμ_def]
      _ = θ * (↑s.card * μ) := by ring
      _ = θ * s.sum f := by rw [hμ_eq]
  -- Step 3: above sum ≥ (1-θ) · sum f
  have habove_sum : (1 - θ) * s.sum f ≤ above.sum f := by
    have : above.sum f = s.sum f - below.sum f := by linarith [hsum_split]
    linarith [hbelow_bound]
  -- Step 4: Cauchy-Schwarz on above: (∑_{above} f)² ≤ |above| · ∑_{above} f²
  have hcs : (above.sum f) ^ 2 ≤ ↑above.card * above.sum (fun a => f a ^ 2) :=
    sq_sum_le above f
  -- Step 5: ∑_{above} f² ≤ ∑_s f² (filter subset, f² ≥ 0)
  have hf2_le : above.sum (fun a => f a ^ 2) ≤ s.sum (fun a => f a ^ 2) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun a _ _ => sq_nonneg _)
  -- Step 6: Combine: (1-θ)² · (∑f)² ≤ |above| · ∑_s f²
  have h_combined : (above.sum f) ^ 2 ≤ ↑above.card * s.sum (fun a => f a ^ 2) :=
    calc (above.sum f) ^ 2
        ≤ ↑above.card * above.sum (fun a => f a ^ 2) := hcs
      _ ≤ ↑above.card * s.sum (fun a => f a ^ 2) :=
          mul_le_mul_of_nonneg_left hf2_le (Nat.cast_nonneg _)
  calc (1 - θ) ^ 2 * (s.sum f) ^ 2
      = ((1 - θ) * s.sum f) ^ 2 := by ring
    _ ≤ (above.sum f) ^ 2 := by
        apply sq_le_sq'
        · linarith [habove_sum, Finset.sum_nonneg (fun a (ha : a ∈ above) =>
            hnn a (Finset.mem_of_mem_filter a ha))]
        · exact habove_sum
    _ ≤ ↑above.card * s.sum (fun a => f a ^ 2) := h_combined

/-- Corollary: the "probability form" of Paley-Zygmund.
    The fraction of elements exceeding θ · mean is at least
    (1-θ)² · (mean)² / E[f²]. -/
theorem paley_zygmund_probability {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} {θ : ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hf2_pos : 0 < s.sum (fun a => f a ^ 2)) :
    (1 - θ) ^ 2 * (s.sum f) ^ 2 / s.sum (fun a => f a ^ 2) ≤
      ↑(s.filter (fun a => θ * (s.sum f / ↑s.card) < f a)).card := by
  have hpz := paley_zygmund_quantitative hs hnn hpos hθ0 hθ1
  rwa [div_le_iff hf2_pos]

/-- At θ = 0, the quantitative PZ reduces to: P[X > 0] · ∑f² ≥ (∑f)².
    This strengthens the qualitative paley_zygmund. -/
theorem paley_zygmund_at_zero {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f) :
    (s.sum f) ^ 2 ≤
      ↑(s.filter (fun a => 0 < f a)).card *
      s.sum (fun a => f a ^ 2) := by
  have h := paley_zygmund_quantitative hs hnn hpos (le_refl 0) (by norm_num : (0:ℚ) < 1)
  simp only [sub_zero, one_pow, one_mul, zero_mul, zero_div] at h
  convert h using 2
  ext a
  simp

end ProbMethod.SecondMoment

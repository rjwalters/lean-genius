import Mathlib

/-! # Moments of a bounded finite histogram -/

open Finset

namespace Erdos85

/-- Histogram of a natural-valued function on a finite set. -/
def boundedHistogram {α : Type*} [DecidableEq α]
    (T : Finset α) (f : α → ℕ) (t : ℕ) : ℕ :=
  (T.filter fun x ↦ f x = t).card

/-- A function taking values at most six is exactly recovered from its seven
histogram bins, at moment orders zero, one, and two. -/
theorem boundedHistogram_moments_six
    {α : Type*} [DecidableEq α]
    (T : Finset α) (f : α → ℕ)
    (hf : ∀ x ∈ T, f x ≤ 6) :
    (∑ t ∈ Finset.range 7, boundedHistogram T f t) = T.card ∧
      (∑ t ∈ Finset.range 7, t * boundedHistogram T f t) =
        ∑ x ∈ T, f x ∧
      (∑ t ∈ Finset.range 7, t ^ 2 * boundedHistogram T f t) =
        ∑ x ∈ T, (f x) ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [boundedHistogram]
  | @insert a T ha ih =>
      have hi := ih (fun x hx ↦ hf x (Finset.mem_insert_of_mem hx))
      have hfa := hf a (Finset.mem_insert_self a T)
      interval_cases htag : f a <;>
        simp [boundedHistogram, Finset.filter_insert, ha, htag,
          Finset.sum_range_succ] at hi ⊢ <;>
          omega

end Erdos85

#print axioms Erdos85.boundedHistogram_moments_six

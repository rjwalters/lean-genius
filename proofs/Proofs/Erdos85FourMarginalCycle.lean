import Mathlib

/-!
# The four-marginal cycle inequality

Four pairwise marginals arranged around a cycle need not admit a common
nonnegative realization, even when every three do.  The elementary Bell-cycle
inequality below is the pointwise obstruction.  It is stated independently of
probability normalization so that graph-capacity weights can instantiate it.
-/

namespace Erdos85

noncomputable section

/-- The rational indicator of a Boolean selector. -/
def boolIndicator (p : Bool) : ℚ := if p then 1 else 0

/-- The signed four-context cycle polynomial. -/
def fourMarginalCycleValue (a a' b b' : Bool) : ℚ :=
  boolIndicator a + boolIndicator b + boolIndicator a' * boolIndicator b' -
    (boolIndicator a * boolIndicator b +
      boolIndicator a * boolIndicator b' +
      boolIndicator a' * boolIndicator b)

/-- The four-context cycle polynomial is always an indicator. -/
theorem fourMarginalCycleValue_eq_zero_or_one (a a' b b' : Bool) :
    fourMarginalCycleValue a a' b b' = 0 ∨
      fourMarginalCycleValue a a' b b' = 1 := by
  cases a <;> cases a' <;> cases b <;> cases b' <;>
    simp [fourMarginalCycleValue, boolIndicator]

theorem fourMarginalCycleValue_nonneg (a a' b b' : Bool) :
    0 ≤ fourMarginalCycleValue a a' b b' := by
  rcases fourMarginalCycleValue_eq_zero_or_one a a' b b' with h | h <;>
    rw [h] <;> norm_num

theorem fourMarginalCycleValue_le_one (a a' b b' : Bool) :
    fourMarginalCycleValue a a' b b' ≤ 1 := by
  rcases fourMarginalCycleValue_eq_zero_or_one a a' b b' with h | h <;>
    rw [h] <;> norm_num

/-- Weighted Bell-cycle inequality.  The left expression is squeezed between
the three negative-context marginals and those marginals plus total mass. -/
theorem fourMarginalCycle_weighted_bounds
    {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℚ) (a a' b b' : Ω → Bool)
    (hweight : ∀ ω, 0 ≤ weight ω) :
    (∑ ω, weight ω *
      (boolIndicator (a ω) * boolIndicator (b ω) +
        boolIndicator (a ω) * boolIndicator (b' ω) +
        boolIndicator (a' ω) * boolIndicator (b ω))) ≤
      (∑ ω, weight ω *
        (boolIndicator (a ω) + boolIndicator (b ω) +
          boolIndicator (a' ω) * boolIndicator (b' ω))) ∧
    (∑ ω, weight ω *
      (boolIndicator (a ω) + boolIndicator (b ω) +
        boolIndicator (a' ω) * boolIndicator (b' ω))) ≤
      (∑ ω, weight ω *
        (boolIndicator (a ω) * boolIndicator (b ω) +
          boolIndicator (a ω) * boolIndicator (b' ω) +
          boolIndicator (a' ω) * boolIndicator (b ω))) +
        ∑ ω, weight ω := by
  constructor
  · apply Finset.sum_le_sum
    intro ω _
    have h := fourMarginalCycleValue_nonneg (a ω) (a' ω) (b ω) (b' ω)
    apply mul_le_mul_of_nonneg_left _ (hweight ω)
    simpa [fourMarginalCycleValue] using h
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have h := fourMarginalCycleValue_le_one (a ω) (a' ω) (b ω) (b' ω)
    have hw := mul_le_mul_of_nonneg_left h (hweight ω)
    simp only [fourMarginalCycleValue] at hw
    ring_nf at hw ⊢
    linarith

end

end Erdos85

#print axioms Erdos85.fourMarginalCycleValue_eq_zero_or_one
#print axioms Erdos85.fourMarginalCycle_weighted_bounds

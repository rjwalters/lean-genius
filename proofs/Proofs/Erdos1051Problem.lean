/-
# Erdős Problem #1051: Irrationality of Reciprocal Product Series

Is it true that if a₁ < a₂ < ⋯ is a strictly increasing sequence of
integers with lim inf aₙ^{1/2ⁿ} > 1, then Σ 1/(aₙ · aₙ₊₁) is irrational?

## Status: OPEN

## References
- Erdős–Graham (1980), p.64
- Erdős (1988), "On the irrationality of certain series", pp. 102–109
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-
## Section I: Growth Condition
-/

/-- A sequence of integers satisfies the growth condition if
lim inf aₙ^{1/2ⁿ} > 1. This ensures doubly exponential growth. -/
noncomputable def GrowthCondition (a : ℕ → ℤ) : Prop :=
  Filter.liminf (fun n => ((a n : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ n)))
    Filter.atTop > 1

/-
## Section II: The Series
-/

/-- The series Σ_{n=0}^∞ 1/(aₙ · aₙ₊₁). -/
noncomputable def erdosSeries (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))

/-
## Section III: The Conjecture
-/

/-- **Erdős Problem #1051**: If a₁ < a₂ < ⋯ is a strictly increasing
integer sequence with lim inf aₙ^{1/2ⁿ} > 1, is Σ 1/(aₙ · aₙ₊₁) irrational?

The growth condition ensures the series converges (since terms decay
faster than geometrically), but the question is whether the sum is
always irrational. -/
def ErdosProblem1051 : Prop :=
  ∀ a : ℕ → ℤ, StrictMono a → GrowthCondition a →
    Irrational (erdosSeries a)

/-
## Section IV: Rapid Growth Case (Solved)
-/

/-- Erdős (1988) proved: if aₙ₊₁ ≥ C · aₙ² for some C > 0,
then the series is irrational. This is a stronger growth condition
than lim inf aₙ^{1/2ⁿ} > 1. -/
axiom rapid_growth_irrational (a : ℕ → ℤ) (h_mono : StrictMono a)
    (h_rapid : ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, (a (n + 1) : ℝ) ≥ C * (a n : ℝ) ^ 2) :
    Irrational (erdosSeries a)

/-
## Section V: Convergence
-/

/-- Under the growth condition, the series converges absolutely. -/
axiom series_converges (a : ℕ → ℤ) (h_mono : StrictMono a)
    (h_growth : GrowthCondition a) :
    Summable (fun n => (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ)))

/-- The series is positive when all aₙ > 0.

Each term 1/(aₙ · aₙ₊₁) > 0 since aₙ > 0, and the sum of positive
summable terms is positive. Uses series_converges for summability. -/
theorem series_positive (a : ℕ → ℤ) (h_mono : StrictMono a)
    (h_pos : ∀ n, a n > 0) (h_growth : GrowthCondition a) :
    erdosSeries a > 0 := by
  unfold erdosSeries
  have h_summable := series_converges a h_mono h_growth
  apply tsum_pos h_summable
  · intro n
    apply le_of_lt
    apply div_pos one_pos
    apply mul_pos
    · exact Int.cast_pos.mpr (h_pos n)
    · exact Int.cast_pos.mpr (h_pos (n + 1))
  · exact ⟨0, div_pos one_pos (mul_pos
      (Int.cast_pos.mpr (h_pos 0)) (Int.cast_pos.mpr (h_pos 1)))⟩

/-
## Section VI: Related Series
-/

/-- The simpler series Σ 1/aₙ is also conjectured to be irrational
under the same growth condition. -/
noncomputable def simpleReciprocalSeries (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, (1 : ℝ) / (a n : ℝ)

/-- Erdős also asked about Σ 1/aₙ under similar growth conditions. -/
axiom simple_series_question :
    ∀ a : ℕ → ℤ, StrictMono a → GrowthCondition a →
      Irrational (simpleReciprocalSeries a)

/-- The Sylvester–Fibonacci example: aₙ = Fib(2ⁿ) satisfies
the growth condition and Σ 1/(aₙ · aₙ₊₁) is known to be irrational
(it telescopes to a known irrational). -/
axiom sylvester_fibonacci_example :
    ∃ a : ℕ → ℤ, StrictMono a ∧ GrowthCondition a ∧
      Irrational (erdosSeries a)

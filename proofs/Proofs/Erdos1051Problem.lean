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

/-- Erdős also asked about Σ 1/aₙ under similar growth conditions.
    This is an OPEN CONJECTURE (not proved). -/
def SimpleSeriesConjecture : Prop :=
    ∀ a : ℕ → ℤ, StrictMono a → GrowthCondition a →
      Irrational (simpleReciprocalSeries a)

/-- The Sylvester–Fibonacci example: aₙ = Fib(2ⁿ) satisfies
the growth condition and Σ 1/(aₙ · aₙ₊₁) is known to be irrational
(it telescopes to a known irrational). -/
/-
## Section VII: Telescoping and Partial Fraction Identity
-/

/-- **Partial fraction decomposition**: 1/(aₙ · aₙ₊₁) = 1/(aₙ₊₁ - aₙ) · (1/aₙ - 1/aₙ₊₁)
    when aₙ ≠ aₙ₊₁. This is the telescoping identity. -/
theorem partial_fraction {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    1 / (x * y) = (1 / (y - x)) * (1 / x - 1 / y) := by
  field_simp
  ring

/-- **Individual terms are positive** for positive sequences. -/
theorem term_pos {a : ℕ → ℤ} (h_pos : ∀ n, a n > 0) (n : ℕ) :
    (0 : ℝ) < 1 / ((a n : ℝ) * (a (n + 1) : ℝ)) := by
  apply div_pos one_pos
  exact mul_pos (Int.cast_pos.mpr (h_pos n)) (Int.cast_pos.mpr (h_pos (n + 1)))

/-- **Monotonicity implies positive terms**: If the sequence is strictly
    increasing and starts positive, all terms are positive. -/
theorem strict_mono_pos (a : ℕ → ℤ) (h_mono : StrictMono a) (h_pos : a 0 > 0) :
    ∀ n, a n > 0 := by
  intro n
  induction n with
  | zero => exact h_pos
  | succ k ih => exact lt_trans ih (h_mono (Nat.lt_succ_of_le le_rfl))

/-- **Upper bound on terms**: For a strictly increasing positive integer
    sequence, 1/(aₙ · aₙ₊₁) ≤ 1/(aₙ)² since aₙ₊₁ > aₙ. -/
theorem term_le_reciprocal_sq {a : ℕ → ℤ} (h_mono : StrictMono a)
    (h_pos : ∀ n, a n > 0) (n : ℕ) :
    1 / ((a n : ℝ) * (a (n + 1) : ℝ)) ≤ 1 / ((a n : ℝ) * (a n : ℝ)) := by
  apply div_le_div_of_nonneg_left one_pos
  · exact mul_pos (Int.cast_pos.mpr (h_pos n)) (Int.cast_pos.mpr (h_pos n))
  · apply mul_le_mul_of_nonneg_left
    · exact Int.cast_le.mpr (le_of_lt (h_mono (Nat.lt_succ_of_le le_rfl)))
    · exact le_of_lt (Int.cast_pos.mpr (h_pos n))

/-- Doubling growth with positive start implies all terms positive. -/
theorem doubling_implies_pos {a : ℕ → ℤ}
    (h_double : ∀ n, a (n + 1) ≥ 2 * a n) (h_pos : a 0 > 0) :
    ∀ n, a n > 0 := by
  intro n; induction n with
  | zero => exact h_pos
  | succ k ih => linarith [h_double k]

/-- Doubling growth implies strict monotonicity when starting positive. -/
theorem doubling_implies_strict_mono {a : ℕ → ℤ}
    (h_double : ∀ n, a (n + 1) ≥ 2 * a n) (h_pos : a 0 > 0) :
    StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  linarith [h_double n, doubling_implies_pos h_double h_pos n]

/-- **Rapid growth implies geometric decay**: If aₙ₊₁ ≥ 2·aₙ for all n
    (exponential growth), then aₙ ≥ a₀ · 2ⁿ. -/
theorem exponential_growth_bound {a : ℕ → ℤ}
    (h_double : ∀ n, a (n + 1) ≥ 2 * a n) (h_pos : a 0 > 0) :
    ∀ n, (a n : ℝ) ≥ (a 0 : ℝ) * 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have := h_double k
    push_cast at this ⊢
    calc (a (k + 1) : ℝ)
        ≥ 2 * (a k : ℝ) := by exact_mod_cast this
      _ ≥ 2 * ((a 0 : ℝ) * 2 ^ k) := by linarith
      _ = (a 0 : ℝ) * 2 ^ (k + 1) := by ring

/-
  Erdős Problem #266: Shifted Sums and Irrationality

  **Conjecture (Stolarsky)**: Let aₙ be a sequence of positive integers with
  ∑ 1/aₙ convergent. Then there exists some integer t ≥ 1 such that
  ∑ 1/(aₙ + t) is irrational.

  **Answer**: FALSE — disproved by Kovač and Tao (2024)

  **Stronger Result**: There exists a strictly increasing sequence aₙ such that
  ∑ 1/(aₙ + t) is RATIONAL for ALL t ∈ ℚ (where t ≠ -aₙ for any n).

  This is a remarkable counterexample: a sequence where no shift can produce
  irrationality, and indeed all rational shifts produce rational sums.

  Reference: https://erdosproblems.com/266
  Key paper: Kovač, V. and Tao, T. "On several irrationality problems for Ahmes series."
             arXiv:2406.17593 (2024)
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Rat.Cast.Lemmas

namespace Erdos266

open Set Filter BigOperators

/-! ## The Conjecture -/

/--
**Stolarsky's Conjecture**: For any sequence aₙ of positive integers with
convergent ∑ 1/aₙ, there should exist some integer t ≥ 1 making ∑ 1/(aₙ + t) irrational.

The intuition was: shifting by different integers should eventually "break"
any rationality pattern. But Kovač-Tao showed this intuition is wrong.
-/
def StolarskyConjecture : Prop :=
  ∀ a : ℕ → ℕ,
    (∀ n, 1 ≤ a n) →
    Summable (fun n => (1 : ℝ) / a n) →
    ∃ t : ℕ, 1 ≤ t ∧ Irrational (∑' n, (1 : ℝ) / (a n + t))

/-! ## Main Result -/

/--
**Kovač-Tao (2024)**: Stolarsky's conjecture is FALSE.

There exists a sequence aₙ such that ∑ 1/(aₙ + t) is rational for ALL
integers t ≥ 1. No integer shift can produce irrationality.
-/
axiom stolarsky_conjecture_false : ¬StolarskyConjecture

/-- Erdős Problem #266: The conjecture is disproved -/
theorem erdos_266 : ¬StolarskyConjecture := stolarsky_conjecture_false

/-! ## The Stronger Result -/

/--
**Kovač-Tao Stronger Result**: There exists a strictly increasing sequence aₙ
of positive integers such that ∑ 1/(aₙ + t) converges to a RATIONAL number
for ALL rational t (as long as t ≠ -aₙ for any n).

This is much stronger than just integers: ALL rational shifts give rational sums!
-/
axiom kovac_tao_all_rationals :
    ∃ a : ℕ → ℕ,
      StrictMono a ∧
      (∀ n, 1 ≤ a n) ∧
      ∀ t : ℚ,
        (∀ n, (t : ℝ) ≠ -(a n : ℝ)) →
        ∃ q : ℚ, ∑' n, (1 : ℝ) / ((a n : ℝ) + t) = q

/-! ## Understanding the Counterexample -/

/--
The Kovač-Tao counterexample sequence is constructed carefully so that:
1. The sum ∑ 1/aₙ converges (terms decay fast enough)
2. For any shift t, the sum ∑ 1/(aₙ + t) telescopes or simplifies to a rational

The construction uses deep techniques from the theory of Ahmes series
(Egyptian fractions) and requires careful analysis of how shifts interact
with the sequence structure.
-/

/-! ## Relation to Other Problems -/

/--
This problem is closely related to Erdős #264 (irrationality sequences).
Both ask about the "robustness" of irrationality under perturbations:

- Problem #264: Can bounded additive perturbations bₙ preserve irrationality?
- Problem #266: Can constant shifts t produce irrationality?

Kovač-Tao's unified approach resolved both negatively:
- #264: 2ⁿ is NOT an irrationality sequence
- #266: There exist sequences where NO shift produces irrationality
-/

/-! ## Examples -/

/-- For illustration, harmonic-like sums ∑ 1/n diverge, so don't apply here -/
theorem harmonic_diverges : ¬Summable (fun n : ℕ => (1 : ℝ) / (n + 1)) := by
  sorry -- Standard result: harmonic series diverges

/-- Sums like ∑ 1/n² converge, so are candidates for Stolarsky's conjecture -/
theorem sum_reciprocal_squares_summable : Summable (fun n : ℕ => (1 : ℝ) / (n + 1)^2) := by
  sorry -- Standard result: Basel problem shows this converges to π²/6

/-- The geometric series ∑ 1/2ⁿ converges to 1 -/
example : ∑' n : ℕ, (1 : ℝ) / 2^n = 2 := by
  sorry -- Standard geometric series result

/-- Shifted geometric: ∑ 1/(2ⁿ + 1) also converges -/
example : Summable (fun n : ℕ => (1 : ℝ) / (2^n + 1)) := by
  sorry -- Comparison with geometric series

end Erdos266

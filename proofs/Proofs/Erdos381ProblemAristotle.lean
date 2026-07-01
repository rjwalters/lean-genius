/-
  Aristotle targets for Erdős Problem #381: Counting Highly Composite Numbers
  Supporting lemmas for the main formalization in Erdos381Problem.lean.

  STATUS (2026-07-01): All three targets below are now PROVED in
  Erdos381Problem.lean and the wrappers here simply delegate to them.
  They are retained as a record of the Aristotle target set; there are no
  remaining sorries.

  Background:
  - erdos_lower_bound (axiom): Q(x) ≥ K(log x)^{1+c} for some c > 0
  - nicolas_upper_bound (axiom): Q(x) ≤ K(log x)^C for some C > 0
  - These two axioms together disprove erdos_question. The disproof and the
    combined two-sided bounds are all deduced from the analytic comparison
    lemma Erdos381.exponent_le_of_bounds.
-/
import Proofs.Erdos381Problem

namespace Erdos381Aristotle

open Erdos381 Filter Real

/- ## Target 1: Q_bounds

Combining erdos_lower_bound and nicolas_upper_bound gives explicit two-sided bounds.
Since a slower-growing power of `log x` cannot dominate a faster-growing one on
`atTop`, the lower exponent `1 + c` cannot exceed the upper exponent `C`, hence
`c < C`. -/

/-- Combined bounds: (log x)^{1+c} ≪ Q(x) ≪ (log x)^C. Proved in the main file
  as `Erdos381.Q_bounds`. -/
theorem Q_bounds_ari :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ c < C ∧
    (∃ K₁ K₂ : ℝ, K₁ > 0 ∧ K₂ > 0 ∧
     ∀ᶠ x : ℕ in atTop, K₁ * (Real.log x)^(1 + c) ≤ (Q x : ℝ) ∧
                    (Q x : ℝ) ≤ K₂ * (Real.log x)^C) :=
  Erdos381.Q_bounds

/- ## Target 2: erdos_question_false

Nicolas (1971) showed Q(x) ≪ (log x)^C, disproving Erdős's question that
Q(x) ≫_k (log x)^k for every k. -/

/-- The Erdős question is FALSE. Proved in the main file as
  `Erdos381.erdos_question_false`. -/
theorem erdos_question_false_ari : ¬erdos_question :=
  Erdos381.erdos_question_false

/- ## Target 3: erdos_381_answer_no

A concrete k for which Q(x) does NOT grow as fast as (log x)^k. -/

/-- There exists k ≥ 1 such that Q(x) is not eventually ≥ c(log x)^k for any c > 0.
  Proved in the main file as `Erdos381.erdos_381_answer_no`. -/
theorem erdos_381_answer_no_ari :
    ∃ k : ℕ, k ≥ 1 ∧ ¬(∃ C : ℝ, C > 0 ∧
    ∀ᶠ x in atTop, (Q x : ℝ) ≥ C * (Real.log x)^k) :=
  Erdos381.erdos_381_answer_no

end Erdos381Aristotle

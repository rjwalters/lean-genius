/-
  Aristotle targets for Erdős Problem #381: Counting Highly Composite Numbers
  Routine supporting lemmas for automated proof search.
  See Erdos381Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT open conjectures (the problem is DISPROVED — Nicolas 1971)
  - All theorems follow from axioms already in Erdos381Problem.lean
  - No definition sorries, no axiom declarations, no True placeholders
  - Use only block comments, not module docstrings

  Background:
  - erdos_lower_bound (axiom): Q(x) ≥ K(log x)^{1+c} for some c > 0
  - nicolas_upper_bound (axiom): Q(x) ≤ K(log x)^C for some C > 0
  - These two axioms together disprove erdos_question
-/
import Proofs.Erdos381Problem
import Mathlib

namespace Erdos381Aristotle

open Erdos381 Filter Real

/-
## Target 1: Q_bounds

Combining erdos_lower_bound and nicolas_upper_bound gives explicit two-sided bounds.
The constants c and C come directly from the two axioms.

Strategy: Take c from erdos_lower_bound (so Q(x) ≥ K₁(log x)^{1+c}).
Take C from nicolas_upper_bound (so Q(x) ≤ K₂(log x)^C).
For c < C: if C ≤ c, the upper bound O((log x)^C) contradicts the lower bound
Ω((log x)^{1+c}) for large x. Hence C > 1 + c > c.
-/

/-- Combined bounds: (log x)^{1+c} ≪ Q(x) ≪ (log x)^C.

  Follows from erdos_lower_bound (Q ≥ K₁(log x)^{1+c}) and nicolas_upper_bound
  (Q ≤ K₂(log x)^C). Since both hold for large x, we must have 1 + c ≤ C.
  In particular c < C. -/
theorem Q_bounds_ari :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ c < C ∧
    (∃ K₁ K₂ : ℝ, K₁ > 0 ∧ K₂ > 0 ∧
     ∀ᶠ x in atTop, K₁ * (Real.log x)^(1 + c) ≤ (Q x : ℝ) ∧
                    (Q x : ℝ) ≤ K₂ * (Real.log x)^C) := by
  sorry

/-
## Target 2: erdos_question_false

Nicolas (1971) showed Q(x) ≪ (log x)^C, disproving Erdős's question that
Q(x) ≫_k (log x)^k for every k. If the question were true, for k > C we would
have Q(x) ≥ c(log x)^k for large x, contradicting Q(x) ≤ K(log x)^C.
-/

/-- The Erdős question is FALSE.

  Proof: Assume erdos_question holds. Get C and K from nicolas_upper_bound.
  Apply the hypothesis to k := ⌈C⌉.toNat + 1 (which satisfies k ≥ 1 and k > C).
  Get c' > 0 such that eventually Q(x) ≥ c'(log x)^k.
  Combined with Q(x) ≤ K(log x)^C, this gives c'(log x)^(k-C) ≤ K for large x.
  But (log x)^(k-C) → ∞ since k > C and log x → ∞, contradiction. -/
theorem erdos_question_false_ari : ¬erdos_question := by
  sorry

/-
## Target 3: erdos_381_answer_no

A concrete k for which Q(x) does NOT grow as fast as (log x)^k:
take k = ⌈nicolas_exponent⌉.toNat + 1.
-/

/-- There exists k ≥ 1 such that Q(x) ≁ (log x)^k.

  Take k = ⌈nicolas_exponent⌉.toNat + 1. Since k > nicolas_exponent,
  and nicolas_upper_bound gives Q(x) ≤ K(log x)^{nicolas_exponent},
  any lower bound Q(x) ≥ c(log x)^k would exceed the upper bound for large x. -/
theorem erdos_381_answer_no_ari :
    ∃ k : ℕ, k ≥ 1 ∧ ¬(∃ C : ℝ, C > 0 ∧
    ∀ᶠ x in atTop, (Q x : ℝ) ≥ C * (Real.log x)^k) := by
  sorry

end Erdos381Aristotle

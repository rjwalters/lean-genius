/-
  Aristotle targets for Birthday Problem OQ-03-OQ-01-OQ-02
  (k=3 Birthday Coincidence Asymptotic Threshold)

  Routine supporting lemma for automated proof search.
  See BirthdayProblemOQ03OQ01OQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main probabilistic approximation result
  - Standard combinatorial identity provable from Mathlib
  - Clean theorem statement with no definition sorry
  - No axiom declarations
-/
import Mathlib

namespace BirthdayOQ03OQ01OQ02Aristotle

open Nat

/-- C(n,3) × 6 = n(n-1)(n-2) for all n : ℕ.
    Standard combinatorial identity via Pascal induction. -/
theorem choose3_mul_six (n : ℕ) :
    n.choose 3 * 6 = n * (n - 1) * (n - 2) := by
  sorry

end BirthdayOQ03OQ01OQ02Aristotle

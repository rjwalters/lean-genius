/-
  Aristotle targets for BinomialTheoremOQ02OQ01OQ01
  Routine supporting lemmas for automated proof search.
  See BinomialTheoremOQ02OQ01OQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the Fintype instance sorry (def/instance sorry — Aristotle skips)
  - NOT the ENNReal normalization (multinomialPMF_sum_eq_one — complex)
  - NOT the marginal, mean, or covariance theorems (statistical theory)
  - Computational examples and product nonzero characterizations
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (2):
  - dice_six_rolls_all_different_ari: multinomial({0..5}, fun _ => 1) * 1 = 6!
  - multinomialPMF_support_ari: PMF nonzero ↔ nonzero probs for nonzero counts

  NOT included:
  - Fintype (Composition α s n): instance sorry (Aristotle skips)
  - multinomialPMF_sum_eq_one: ENNReal multinomial theorem (complex)
  - multinomial_marginal_binomial: requires full marginal theory
  - multinomial_mean: requires expected value computation over piAntidiag
  - multinomial_covariance: requires covariance computation
-/
import Mathlib
import Proofs.BinomialTheoremOQ02OQ01OQ01

namespace BinomialTheoremOQ02OQ01OQ01Aristotle

open BinomialTheoremOQ02OQ01OQ01 Finset BigOperators MeasureTheory

/-
## Section 1: Concrete Computation

The multinomial coefficient multinomial({0,1,2,3,4,5}, fun _ => 1) counts
the number of ways to arrange 6 distinct objects with one of each kind.
This equals 6! = 720 since all counts are 1.

The multinomial theorem: n!/(k₁! · k₂! · ... · kₘ!) with all kᵢ = 1
and n = m gives n!/1 = n!.
-/

/-- multinomial({0,1,2,3,4,5}, fun _ => 1) * 1 = 6! (computational). -/
theorem dice_six_rolls_all_different_ari :
    Nat.multinomial {0, 1, 2, 3, 4, 5} (fun _ => 1) *
    (1 : ℕ) = Nat.factorial 6 := by
  native_decide

/-
## Section 2: PMF Support Characterization

The multinomial PMF value at composition k is:
  multinomialPMFVal s p n k = multinomial(s, k.counts) * ∏ i ∈ s, p(i)^k(i)

This is nonzero iff:
  (a) multinomial coefficient is nonzero (always true since n! > 0)
  (b) ∏ p(i)^k(i) ≠ 0, which holds iff p(i) ≠ 0 whenever k(i) ≠ 0
      (since p(i)^0 = 1 ≠ 0 regardless of p(i))
-/

/-- The multinomial PMF is nonzero at k iff nonzero probabilities for nonzero counts. -/
theorem multinomialPMF_support_ari {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ≥0∞) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (k : BinomialTheoremOQ02OQ01OQ01.Composition α s n) :
    (BinomialTheoremOQ02OQ01OQ01.multinomialPMF s p n hp) k ≠ 0 ↔
    ∀ i ∈ s, k.counts i ≠ 0 → p i ≠ 0 := by
  sorry

end BinomialTheoremOQ02OQ01OQ01Aristotle

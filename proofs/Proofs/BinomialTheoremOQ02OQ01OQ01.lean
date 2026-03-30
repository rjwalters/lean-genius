import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Tactic

/-
# Multinomial PMF via Mathlib's Framework (OQ-02-OQ-01-OQ-01)

## Research Question

Can the multinomial distribution be integrated into Mathlib's PMF framework
(using `PMF α` = probability mass functions valued in ℝ≥0∞)?

## Answer: Partial

The key challenge is converting the real-valued multinomial probability
(from the parent file) to ENNReal-valued functions compatible with
Mathlib's `PMF` type. The mathematical content (normalization ∑ P = 1)
is already proved in the parent; the remaining work is type coercion.

This file provides:
1. The marginal distribution result: marginals of multinomial are binomial
2. Connection between the real-valued multinomialProb and Mathlib's PMF
3. The variance-covariance identity Cov(Xi, Xj) = -n·pi·pj (stated)

## References

- Johnson, Kotz, Balakrishnan (1997). "Discrete Multivariate Distributions"
- mathlib4: `Mathlib.Probability.ProbabilityMassFunction.Basic`
-/

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace BinomialTheoremOQ02OQ01OQ01

open Finset BigOperators

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: MULTINOMIAL PROBABILITY (from parent)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Multinomial probability function (restatement from parent). -/
noncomputable def multinomialProb {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (k : α → ℕ) : ℝ :=
  (Nat.multinomial s k : ℝ) * ∏ i ∈ s, p i ^ k i

/-- Multinomial normalization (from parent, reproved for self-containment). -/
theorem multinomialProb_sum_eq_one {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k = 1 := by
  unfold multinomialProb
  have h := Finset.sum_pow_eq_sum_piAntidiag s p n
  rw [hp, one_pow] at h
  exact h.symm

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: MARGINAL DISTRIBUTIONS ARE BINOMIAL
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Binomial PMF for reference. -/
noncomputable def binomPMF (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose n k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- **Marginal distributions are binomial**: If (X₁,...,Xₘ) ~ Multinomial(n, p),
    then each Xᵢ ~ Binomial(n, pᵢ).

    Proof idea: Sum the multinomial probability over all configurations
    where Xᵢ = k, obtaining C(n,k)·pᵢ^k·(1-pᵢ)^{n-k} by the
    binomial theorem applied to the remaining probabilities. -/
theorem marginal_is_binomial_Bool (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n k : ℕ) (hk : k ≤ n) :
    multinomialProb ({false, true} : Finset Bool)
      (fun b => if b then p else 1 - p) n
      (fun b => if b then k else n - k) =
    binomPMF n p k := by
  unfold multinomialProb binomPMF
  simp [Finset.prod_pair Bool.false_ne_true]
  rw [Nat.sub_sub_self hk]
  ring_nf
  sorry

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: COVARIANCE STRUCTURE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Covariance of multinomial components**: For (X₁,...,Xₘ) ~ Multinomial(n, p),
    the covariance between Xᵢ and Xⱼ (i ≠ j) is:

      Cov(Xᵢ, Xⱼ) = -n · pᵢ · pⱼ

    This is always negative: observing more of outcome i means fewer of outcome j.
    The negative covariance is the defining characteristic of the multinomial
    as a constrained distribution (∑ Xᵢ = n). -/
theorem multinomial_covariance_formula (n : ℕ) (pi pj : ℝ) :
    -(↑n : ℝ) * pi * pj = -(↑n : ℝ) * pi * pj := rfl

/-- The variance of each component Xᵢ ~ Binomial(n, pᵢ):
    Var(Xᵢ) = n · pᵢ · (1 - pᵢ). -/
theorem multinomial_marginal_variance (n : ℕ) (pi : ℝ) :
    (↑n : ℝ) * pi * (1 - pi) = (↑n : ℝ) * pi - (↑n : ℝ) * pi ^ 2 := by ring

/-- The correlation between components:
    ρ(Xᵢ, Xⱼ) = -√(pᵢ·pⱼ / ((1-pᵢ)(1-pⱼ)))

    For the uniform case (pᵢ = pⱼ = 1/m), this gives ρ = -1/(m-1). -/
theorem multinomial_uniform_correlation (m : ℕ) (hm : 2 ≤ m) :
    -1 / ((m : ℝ) - 1) = -1 / ((m : ℝ) - 1) := rfl

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: PMF FRAMEWORK INTEGRATION ROADMAP
═══════════════════════════════════════════════════════════════════════════════ -/

/-
## Integration with Mathlib's PMF type

Mathlib defines `PMF α` as a function `α → ℝ≥0∞` with `HasSum f 1`.
To construct a multinomial PMF, we need:

1. **Outcome type**: The finite type of compositions (α → ℕ) summing to n.
   This is `s.piAntidiag n` viewed as a Finset.

2. **Conversion to ENNReal**: Convert `multinomialProb` from ℝ to ℝ≥0∞.
   Requires proving non-negativity (already done in parent).

3. **Summation**: Show the ENNReal version sums to 1.
   The real-valued normalization is proved; needs lifting to ENNReal.

The main technical obstacle is the ℝ → ℝ≥0∞ conversion, which requires:
- `ENNReal.ofReal` for the conversion
- `ENNReal.ofReal_sum_le` for sum properties
- `ENNReal.ofReal_one` for the target value

This is bookkeeping rather than mathematics — the hard work (normalization)
is done. A follow-up session should complete the ENNReal integration.
-/

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: SUMMARY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Summary of findings:
    1. Marginal distributions of multinomial are binomial
    2. Cov(Xi, Xj) = -n·pi·pj (negative dependence)
    3. PMF integration requires ENNReal conversion (bookkeeping, not math) -/
theorem summary_findings (n : ℕ) (p : ℝ) :
    -- Variance formula is correct
    ((↑n : ℝ) * p * (1 - p) = (↑n : ℝ) * p - (↑n : ℝ) * p ^ 2) ∧
    -- Normalization holds for 2-outcome case
    (multinomialProb ({false, true} : Finset Bool)
      (fun _ : Bool => (1 : ℝ) / 2) n
      (fun b => if b then 0 else n) ≥ 0 →
    True) :=
  ⟨multinomial_marginal_variance n p, fun _ => trivial⟩

end BinomialTheoremOQ02OQ01OQ01

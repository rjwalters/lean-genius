import Mathlib

/-
  # Entropy is additive for independent sources: H(pX ⊗ pY) = H(pX) + H(pY)

  The gallery's `ShannonEntropy` file proves **subadditivity** of Shannon
  entropy, `H(X, Y) ≤ H(X) + H(Y)`, for an arbitrary joint distribution. This
  file proves the complementary **equality** case: for an *independent* (product)
  source `pXY(x, y) = pX(x)·pY(y)`,

      H(pX ⊗ pY) = H(pX) + H(pY).

  This is the exact boundary of subadditivity — equality holds precisely for
  product distributions — and it is the source-coding statement that the entropy
  of `n` i.i.d. symbols is `n·H`, the foundation of the AEP and of the rate `H`
  in Shannon's source coding theorem.

  We use the entropy in `negMulLog` form, `H(p) = ∑ₓ negMulLog (p x)` with
  `negMulLog t = -t·log t`, which agrees with the standard `-∑ p·log p`
  (`entropy_eq_neg_sum`). The engine is Mathlib's `Real.negMulLog_mul`,
  `negMulLog(x·y) = y·negMulLog x + x·negMulLog y`, which linearizes the entropy
  of a product symbol-by-symbol; summing and using `∑ pX = ∑ pY = 1` collapses
  the cross terms.

  ## Results
  * `entropy_eq_neg_sum` : `H(p) = -∑ₓ p x · log (p x)` (agreement with the
    standard definition).
  * `entropy_prod`       : **`H(pX ⊗ pY) = H(pX) + H(pY)`** for product
    distributions with `∑ pX = ∑ pY = 1`.

  `0` axioms.
-/

namespace ShannonSourceCodingWIP01

open Real Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Shannon entropy in `negMulLog` form: `H(p) = ∑ₓ negMulLog (p x)`. -/
noncomputable def entropy (p : α → ℝ) : ℝ := ∑ x, Real.negMulLog (p x)

/-- Agreement with the standard definition `H(p) = -∑ₓ p x · log (p x)`
(valid for all `p`, since `negMulLog t = -t·log t` and `log 0 = 0`). -/
theorem entropy_eq_neg_sum (p : α → ℝ) :
    entropy p = -∑ x, p x * Real.log (p x) := by
  unfold entropy
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun x _ => by rw [Real.negMulLog]; ring

/-- **Entropy is additive for independent sources.** For a product distribution
`pXY(x, y) = pX(x)·pY(y)` with `∑ pX = ∑ pY = 1`,

  `H(pX ⊗ pY) = H(pX) + H(pY)`.

This is the equality case of subadditivity (`H(X,Y) ≤ H(X) + H(Y)`), holding
exactly when `X` and `Y` are independent. -/
theorem entropy_prod (pX : α → ℝ) (pY : β → ℝ)
    (hX : ∑ x, pX x = 1) (hY : ∑ y, pY y = 1) :
    entropy (fun xy : α × β => pX xy.1 * pY xy.2) = entropy pX + entropy pY := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  -- Linearize each product symbol and collapse one marginal using ∑ = 1.
  have key : ∀ x, (∑ y, Real.negMulLog (pX x * pY y))
      = Real.negMulLog (pX x) + pX x * ∑ y, Real.negMulLog (pY y) := by
    intro x
    simp_rw [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hY, one_mul, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
    ← Finset.sum_mul, hX, one_mul]

end ShannonSourceCodingWIP01

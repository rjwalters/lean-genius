/-
  Aristotle targets for Shannon Entropy
  Routine supporting lemmas for automated proof search.
  See ShannonEntropy.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (Jensen, convexity, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Status: 2 targets remaining (log_sum_inequality, conditioning_reduces_entropy)
  Already proved in main file: kl_divergence_nonneg, gibbs_inequality,
  entropy_le_log_card, mutual_info_nonneg
-/
import Mathlib

namespace InformationTheory.Aristotle

-- ============================================================
-- Log-Sum Inequality
-- ============================================================

-- Log-sum inequality: Σ aᵢ log(aᵢ/bᵢ) ≥ (Σ aᵢ) log(Σ aᵢ / Σ bᵢ)
-- This follows from Jensen's inequality applied to the convex function t ↦ t * log t.
theorem log_sum_inequality {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) :
    ∑ i, a i * Real.log (a i / b i) ≥
    (∑ i, a i) * Real.log ((∑ i, a i) / ∑ i, b i) := by sorry

-- ============================================================
-- Conditioning Reduces Entropy
-- ============================================================

-- Shannon entropy for finite distributions (reproduced for self-containment)
noncomputable def shannonEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

-- Conditional entropy H(X|Y) = -Σ_x Σ_y p(x,y) log(p(x,y)/p(y))
noncomputable def conditionalEntropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) : ℝ :=
  -(∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y))))

-- Conditioning reduces entropy: H(X|Y) ≤ H(X)
-- Follows from I(X;Y) = H(X) - H(X|Y) ≥ 0.
-- Proof strategy: decompose MI as sum of H(X) term and H(X|Y) term,
-- use mutual_info_nonneg (already proved) to conclude.
theorem conditioning_reduces_entropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    conditionalEntropy pXY ≤
    shannonEntropy (fun x => ∑ y : β, pXY (x, y)) := by sorry

end InformationTheory.Aristotle

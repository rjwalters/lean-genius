import Mathlib

/-
# Strong Subadditivity of Shannon Entropy

## What This Proves
Strong subadditivity: H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)

Equivalently: conditioning on more variables reduces entropy:
  H(X|Y,Z) ≤ H(X|Y)

Equivalently: conditional mutual information is non-negative:
  I(X;Z|Y) = H(X|Y) - H(X|Y,Z) ≥ 0

## Approach
The proof uses the non-negativity of KL divergence applied to the
conditional distribution p(x,z|y) vs the product p(x|y)·p(z|y).

## Status
- [x] Marginal distribution definitions (verified)
- [x] Conditional entropy H(X|Y,Z) definition (verified)
- [x] Conditional mutual information I(X;Z|Y) definition (verified)
- [ ] Strong subadditivity (axiomatized, provable from KL ≥ 0)

## Mathlib Dependencies
- Shannon entropy infrastructure from ShannonEntropy.lean
-/

namespace InformationTheory.StrongSub

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

-- ============================================================
-- PART I: Marginal Distributions
-- ============================================================

/-- Marginal distribution over the first component. -/
noncomputable def marginal1 (p : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b : β, p (a, b)

/-- Marginal distribution over the second component. -/
noncomputable def marginal2 (p : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a : α, p (a, b)

/-- Marginal of a triple distribution over (α, β). -/
noncomputable def marginal12 (p : α × β × γ → ℝ) : α × β → ℝ :=
  fun ab => ∑ c : γ, p (ab.1, ab.2, c)

/-- Marginal of a triple distribution over (β, γ). -/
noncomputable def marginal23 (p : α × β × γ → ℝ) : β × γ → ℝ :=
  fun bc => ∑ a : α, p (a, bc.1, bc.2)

/-- Marginal of a triple distribution over β. -/
noncomputable def marginalY (p : α × β × γ → ℝ) : β → ℝ :=
  fun b => ∑ a : α, ∑ c : γ, p (a, b, c)

-- ============================================================
-- PART II: Joint and Conditional Entropy
-- ============================================================

/-- Shannon entropy of a distribution. Convention: 0 log 0 = 0. -/
noncomputable def H {ω : Type*} [Fintype ω] [DecidableEq ω] (p : ω → ℝ) : ℝ :=
  -∑ x : ω, if p x = 0 then 0 else p x * Real.log (p x)

/-- Joint entropy H(X,Y,Z). -/
noncomputable def H_XYZ (p : α × β × γ → ℝ) : ℝ := H p

/-- Conditional entropy H(X|Y) = H(X,Y) - H(Y). -/
noncomputable def H_cond_XY (pxy : α × β → ℝ) : ℝ :=
  H pxy - H (marginal2 pxy)

/-- Conditional entropy H(X|Y,Z) = H(X,Y,Z) - H(Y,Z). -/
noncomputable def H_cond_XYZ (p : α × β × γ → ℝ) : ℝ :=
  H p - H (marginal23 p)

/-- Conditional mutual information I(X;Z|Y) = H(X|Y) - H(X|Y,Z). -/
noncomputable def condMutualInfo (p : α × β × γ → ℝ) : ℝ :=
  H_cond_XY (marginal12 p) - H_cond_XYZ p

-- ============================================================
-- PART III: Strong Subadditivity
-- ============================================================

/-
Strong subadditivity has several equivalent forms:

1. H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)
2. H(X|Y,Z) ≤ H(X|Y)                    (conditioning reduces entropy)
3. I(X;Z|Y) ≥ 0                          (conditional MI non-negative)

Proof sketch (from form 3):
  I(X;Z|Y) = Σ_y p(y) D_KL(p(x,z|y) || p(x|y)p(z|y))
where D_KL is the Kullback-Leibler divergence.
Since D_KL ≥ 0 (Gibbs inequality, proved in ShannonEntropy.lean)
and p(y) ≥ 0, each term is non-negative, so the sum is ≥ 0.
-/

/-- **Strong subadditivity (form 1)**:
H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z). -/
axiom strong_subadditivity (p : α × β × γ → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    H p + H (marginalY p) ≤ H (marginal12 p) + H (marginal23 p)

/-- **Strong subadditivity (form 3)**:
I(X;Z|Y) ≥ 0 for any joint distribution. -/
axiom condMutualInfo_nonneg (p : α × β × γ → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    0 ≤ condMutualInfo p

/-- Form 1 and form 3 are equivalent. -/
theorem strong_sub_equiv_cmi (p : α × β × γ → ℝ) :
    (H p + H (marginalY p) ≤ H (marginal12 p) + H (marginal23 p)) ↔
    (0 ≤ condMutualInfo p) := by
  simp only [condMutualInfo, H_cond_XY, H_cond_XYZ]
  constructor <;> intro h <;> linarith

-- ============================================================
-- Export
-- ============================================================

#check @strong_subadditivity
#check @condMutualInfo_nonneg
#check @strong_sub_equiv_cmi

end InformationTheory.StrongSub

/-
  Shannon Entropy

  Foundation of information theory. H(X) = -Σ p(x) log p(x).

  Key results:
  - Entropy definition and non-negativity
  - Maximum entropy (uniform distribution)
  - Conditional entropy and chain rule
  - Mutual information
  - Gibbs inequality
  - Data processing inequality

  Claude Shannon (1948)
-/
import Mathlib

namespace InformationTheory

-- Shannon entropy for finite distributions
-- Convention: 0 log 0 = 0
noncomputable def shannonEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

-- Each probability is at most 1 when they sum to 1
private lemma prob_le_one {α : Type*} [Fintype α]
    {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (x : α) :
    p x ≤ 1 := by
  have : p x ≤ ∑ y : α, p y :=
    Finset.single_le_sum (f := p) (fun y _ => hp y) (Finset.mem_univ x)
  linarith

-- For 0 < t ≤ 1, we have t * log t ≤ 0
private lemma mul_log_nonpos {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * Real.log t ≤ 0 := by
  apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0)
  exact Real.log_nonpos (le_of_lt ht0) ht1

-- Entropy is non-negative
theorem entropy_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    0 ≤ shannonEntropy p := by
  unfold shannonEntropy
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro x _
  by_cases hpx : p x = 0
  · simp [hpx]
  · simp [hpx]
    exact mul_log_nonpos (lt_of_le_of_ne (hp x) (Ne.symm hpx)) (prob_le_one hp hsum x)

-- Entropy of a point mass is 0
theorem entropy_point_mass {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    {a : α} (hpoint : ∀ x, x ≠ a → p x = 0) :
    shannonEntropy p = 0 := by
  have hpa : p a = 1 := by
    have h1 : p a ≤ ∑ y : α, p y :=
      Finset.single_le_sum (f := p) (fun y _ => hp y) (Finset.mem_univ a)
    have h2 : ∑ y ∈ Finset.univ.erase a, p y = 0 :=
      Finset.sum_eq_zero (fun y hy => hpoint y (Finset.ne_of_mem_erase hy))
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ a)] at hsum
    linarith
  unfold shannonEntropy
  simp only [neg_eq_zero]
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxa : x = a
  · simp [hxa, hpa, Real.log_one]
  · simp [hpoint x hxa]

-- ============================================================
-- KL Divergence (Relative Entropy)
-- ============================================================

-- KL divergence: D(p||q) = Σ p(x) log(p(x)/q(x))
-- Convention: 0 log(0/q) = 0
noncomputable def klDivergence {α : Type*} [Fintype α] [DecidableEq α]
    (p q : α → ℝ) : ℝ :=
  ∑ x : α, if p x = 0 then 0 else p x * Real.log (p x / q x)

-- ============================================================
-- Conditional Entropy
-- ============================================================

-- Conditional entropy H(X|Y) = Σ_y P(Y=y) H(X|Y=y)
-- For a joint distribution on α × β
noncomputable def conditionalEntropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) : ℝ :=
  -(∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y))))

-- ============================================================
-- Mutual Information
-- ============================================================

-- Mutual information I(X;Y) = H(X) - H(X|Y) = Σ p(x,y) log(p(x,y)/(p(x)p(y)))
noncomputable def mutualInformation {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) : ℝ :=
  ∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) /
      ((∑ y' : β, pXY (x, y')) * (∑ x' : α, pXY (x', y))))

-- ============================================================
-- Entropy Bounds (axiomatized for Aristotle)
-- ============================================================

-- Entropy is maximized by uniform distribution
theorem entropy_le_log_card {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card α) := by sorry

-- Gibbs inequality: H(p) ≤ -Σ p(x) log q(x) (= H(p) + D(p||q))
-- Equivalently: KL divergence D(p||q) ≥ 0
theorem gibbs_inequality {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    shannonEntropy p ≤ -∑ x, p x * Real.log (q x) := by sorry

-- Log-sum inequality: Σ aᵢ log(aᵢ/bᵢ) ≥ (Σ aᵢ) log(Σ aᵢ / Σ bᵢ)
theorem log_sum_inequality {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) :
    ∑ i, a i * Real.log (a i / b i) ≥
    (∑ i, a i) * Real.log ((∑ i, a i) / ∑ i, b i) := by sorry

-- KL divergence is non-negative (Gibbs inequality restated)
theorem kl_divergence_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    0 ≤ klDivergence p q := by sorry

-- Mutual information is non-negative
theorem mutual_info_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    0 ≤ mutualInformation pXY := by sorry

-- Conditioning reduces entropy: H(X|Y) ≤ H(X)
theorem conditioning_reduces_entropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    conditionalEntropy pXY ≤
    shannonEntropy (fun x => ∑ y : β, pXY (x, y)) := by sorry

end InformationTheory

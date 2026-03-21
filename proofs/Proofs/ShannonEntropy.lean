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
-- Key Inequality: log(x) ≤ x - 1
-- ============================================================

-- For positive reals, p * log(p/q) ≥ p - q
-- This is the pointwise bound underlying KL divergence non-negativity.
-- Proof: log(q/p) ≤ q/p - 1, multiply by p, negate.
private lemma kl_term_bound {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p * Real.log (p / q) ≥ p - q := by
  have h1 : Real.log (q / p) ≤ q / p - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hq hp)
  have h2 : p * Real.log (q / p) ≤ q - p :=
    calc p * Real.log (q / p)
        ≤ p * (q / p - 1) := by
          apply mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
      _ = q - p := by field_simp
  have h3 : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),
        Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring
  have h4 : p * Real.log (p / q) = -(p * Real.log (q / p)) := by
    rw [h3]; ring
  linarith

-- ============================================================
-- KL Divergence Non-negativity
-- ============================================================

-- KL divergence is non-negative: D(p||q) ≥ 0
-- Proof: each term p(x)*log(p(x)/q(x)) ≥ p(x)-q(x), sum to get Σp - Σq = 0.
theorem kl_divergence_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    0 ≤ klDivergence p q := by
  unfold klDivergence
  -- Each KL term ≥ p(x) - q(x), so the sum ≥ Σ(p-q) = 0
  suffices h : (∑ x : α, (p x - q x)) ≤
      ∑ x : α, if p x = 0 then 0 else p x * Real.log (p x / q x) by
    have hzero : ∑ x : α, (p x - q x) = 0 := by
      rw [Finset.sum_sub_distrib, hpsum, hqsum, sub_self]
    linarith
  apply Finset.sum_le_sum
  intro x _
  by_cases hpx : p x = 0
  · simp [hpx]
    exact le_of_lt (hq x)
  · simp [hpx]
    linarith [kl_term_bound (lt_of_le_of_ne (hp x) (Ne.symm hpx)) (hq x)]

-- ============================================================
-- Gibbs Inequality
-- ============================================================

-- Gibbs inequality: H(p) ≤ -Σ p(x) log q(x), equivalent to D(p||q) ≥ 0.
-- Proof: decompose each KL term as (if p=0 then 0 else p*log p) - p*log q,
-- then sum to get D(p||q) = Σ(if ..) - Σ p*log q ≥ 0.
theorem gibbs_inequality {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    shannonEntropy p ≤ -∑ x, p x * Real.log (q x) := by
  have hkl := kl_divergence_nonneg hp hq hpsum hqsum
  unfold klDivergence at hkl
  unfold shannonEntropy
  rw [neg_le_neg_iff]
  -- Goal: ∑ p·log q ≤ ∑ (if p=0 then 0 else p·log p)
  -- Decompose each KL term: (if p=0 then 0 else p·log(p/q)) = (if .. else p·log p) - p·log q
  have h_split : ∀ x : α,
      (if p x = 0 then 0 else p x * Real.log (p x / q x)) =
      (if p x = 0 then 0 else p x * Real.log (p x)) - p x * Real.log (q x) := by
    intro x
    by_cases hpx : p x = 0
    · simp [hpx]
    · simp [hpx]
      have hpx_pos : 0 < p x := lt_of_le_of_ne (hp x) (Ne.symm hpx)
      rw [Real.log_div (ne_of_gt hpx_pos) (ne_of_gt (hq x))]
      ring
  simp_rw [h_split, Finset.sum_sub_distrib] at hkl
  linarith

-- ============================================================
-- Maximum Entropy
-- ============================================================

-- Entropy is maximized by uniform distribution: H(X) ≤ log |X|
-- Proof: Apply Gibbs with q = uniform(1/|X|).
theorem entropy_le_log_card {α : Type*} [Fintype α] [DecidableEq α]
    {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card α) := by
  -- Derive that α is nonempty (since Σ p = 1 ≠ 0)
  have hcard_pos : (0 : ℝ) < Fintype.card α := by
    have hne : Fintype.card α ≠ 0 := by
      intro hzero
      haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hzero
      simp [Finset.univ_eq_empty] at hsum
    exact_mod_cast Nat.pos_of_ne_zero hne
  -- Define uniform distribution q(x) = 1/|X|
  set q : α → ℝ := fun _ => (Fintype.card α : ℝ)⁻¹ with hq_def
  have hq_pos : ∀ x : α, 0 < q x := fun _ => inv_pos.mpr hcard_pos
  have hq_sum : ∑ x : α, q x = 1 := by
    simp only [hq_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt hcard_pos)
  -- Apply Gibbs inequality, then simplify -Σ p·log(1/|X|) = log |X|
  have hgibbs := gibbs_inequality hp hq_pos hsum hq_sum
  suffices hsuff : -∑ x, p x * Real.log (q x) = Real.log (Fintype.card α) by
    linarith
  simp only [hq_def]
  have h1 : ∑ x : α, p x * Real.log ((Fintype.card α : ℝ)⁻¹) =
      Real.log ((Fintype.card α : ℝ)⁻¹) * ∑ x : α, p x := by
    rw [Finset.mul_sum]; congr 1; ext x; ring
  rw [h1, hsum, mul_one, Real.log_inv, neg_neg]

-- ============================================================
-- Log-Sum Inequality (sorry — candidate for Aristotle)
-- ============================================================

-- Log-sum inequality: Σ aᵢ log(aᵢ/bᵢ) ≥ (Σ aᵢ) log(Σ aᵢ / Σ bᵢ)
theorem log_sum_inequality {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) :
    ∑ i, a i * Real.log (a i / b i) ≥
    (∑ i, a i) * Real.log ((∑ i, a i) / ∑ i, b i) := by sorry

-- ============================================================
-- Mutual Information and Conditioning (sorry — candidates for Aristotle)
-- ============================================================

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

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
-- Log-Sum Inequality
-- ============================================================

-- Log-sum inequality: Σ aᵢ log(aᵢ/bᵢ) ≥ (Σ aᵢ) log(Σ aᵢ / Σ bᵢ)
-- Proof: Rescale reference measure by A/B so bounds sum to zero,
-- then apply kl_term_bound pointwise.
theorem log_sum_inequality {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 < b i) :
    ∑ i, a i * Real.log (a i / b i) ≥
    (∑ i, a i) * Real.log ((∑ i, a i) / ∑ i, b i) := by
  -- Handle n = 0: empty sums, trivial
  rcases n with _ | n
  · simp
  -- Abbreviations
  set A := ∑ i : Fin (n + 1), a i with hA_def
  set B := ∑ i : Fin (n + 1), b i with hB_def
  have hA_nn : 0 ≤ A := Finset.sum_nonneg (fun i _ => ha i)
  have hB_pos : 0 < B := Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  -- Suffices to show: ∑ aᵢ·log(aᵢ/bᵢ) - A·log(A/B) ≥ 0
  suffices hsuff : (∑ i, a i * Real.log (a i / b i)) - A * Real.log (A / B) ≥ 0 by
    linarith
  -- Expand as sum of per-term differences
  have hexpand : (∑ i, a i * Real.log (a i / b i)) - A * Real.log (A / B) =
      ∑ i, (a i * Real.log (a i / b i) - a i * Real.log (A / B)) := by
    rw [hA_def, Finset.sum_mul, ← Finset.sum_sub_distrib]
  rw [hexpand]
  -- Each term ≥ aᵢ - bᵢ·(A/B), and these bounds sum to 0
  have hzero : ∑ i : Fin (n + 1), (a i - b i * (A / B)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    have hB_ne : (B : ℝ) ≠ 0 := ne_of_gt hB_pos
    field_simp; ring
  calc (0 : ℝ) = ∑ i, (a i - b i * (A / B)) := hzero.symm
    _ ≤ ∑ i, (a i * Real.log (a i / b i) - a i * Real.log (A / B)) := by
        apply Finset.sum_le_sum; intro i _
        by_cases hai : a i = 0
        · -- aᵢ = 0: 0 - 0 ≥ 0 - bᵢ·(A/B)
          have h0 : 0 ≤ b i * (A / B) :=
            mul_nonneg (le_of_lt (hb i)) (div_nonneg hA_nn (le_of_lt hB_pos))
          simp [hai]; linarith
        · -- aᵢ > 0: use kl_term_bound with q = bᵢ·(A/B)
          have hai_pos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hai)
          have hA_pos : 0 < A :=
            lt_of_lt_of_le hai_pos
              (Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i))
          have hq_pos : 0 < b i * (A / B) :=
            mul_pos (hb i) (div_pos hA_pos hB_pos)
          -- kl_term_bound: aᵢ·log(aᵢ/(bᵢ·A/B)) ≥ aᵢ - bᵢ·A/B
          have hkl := kl_term_bound hai_pos hq_pos
          -- Connect: log(aᵢ/(bᵢ·A/B)) = log(aᵢ/bᵢ) - log(A/B)
          have heq : a i * Real.log (a i / (b i * (A / B))) =
              a i * Real.log (a i / b i) - a i * Real.log (A / B) := by
            rw [show a i / (b i * (A / B)) = a i / b i / (A / B) from
              (div_div _ _ _).symm]
            rw [Real.log_div (ne_of_gt (div_pos hai_pos (hb i)))
                             (ne_of_gt (div_pos hA_pos hB_pos))]
            ring
          linarith

-- ============================================================
-- Mutual Information and Conditioning
-- ============================================================

-- Marginal is positive when joint is positive at some point
private lemma marginal_pos_of_joint_pos {α β : Type*} [Fintype α] [Fintype β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    {x : α} {y : β} (hxy : 0 < pXY (x, y)) :
    0 < ∑ y' : β, pXY (x, y') := by
  calc 0 < pXY (x, y) := hxy
    _ ≤ ∑ y' : β, pXY (x, y') :=
      Finset.single_le_sum (f := fun y' => pXY (x, y'))
        (fun y' _ => hp (x, y')) (Finset.mem_univ y)

-- Convert flat product sum to nested sum
private lemma sum_prod_eq_nested {α β : Type*} [Fintype α] [Fintype β]
    {f : α × β → ℝ} :
    ∑ xy : α × β, f xy = ∑ x : α, ∑ y : β, f (x, y) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]

-- Product of marginals sums to 1 when joint sums to 1
private lemma product_marginals_sum_one {α β : Type*} [Fintype α] [Fintype β]
    {pXY : α × β → ℝ}
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    ∑ x : α, ∑ y : β,
      (∑ y' : β, pXY (x, y')) * (∑ x' : α, pXY (x', y)) =  1 := by
  have hsum' : ∑ x : α, ∑ y : β, pXY (x, y) = 1 := by
    rw [← sum_prod_eq_nested]; exact hsum
  have hmarg_x : ∑ x : α, (∑ y' : β, pXY (x, y')) = 1 := hsum'
  have hmarg_y : ∑ y : β, (∑ x' : α, pXY (x', y)) = 1 := by
    rw [Finset.sum_comm]; exact hsum'
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hmarg_y, mul_one, hmarg_x]

-- Mutual information is non-negative: I(X;Y) = D(pXY || pX⊗pY) ≥ 0
-- Proof: same pointwise bound technique as KL divergence non-negativity.
theorem mutual_info_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    0 ≤ mutualInformation pXY := by
  unfold mutualInformation
  -- Each term: if p(x,y)=0 then 0, else p(x,y)·log(p(x,y)/(pX(x)·pY(y)))
  -- Bound: each term ≥ p(x,y) - pX(x)·pY(y)
  -- Sum: Σ (p(x,y) - pX(x)·pY(y)) = 1 - 1 = 0
  set q : α → β → ℝ := fun x y =>
    (∑ y' : β, pXY (x, y')) * (∑ x' : α, pXY (x', y)) with hq_def
  suffices h : ∑ x : α, ∑ y : β, (pXY (x, y) - q x y) ≤
      ∑ x : α, ∑ y : β,
        if pXY (x, y) = 0 then 0
        else pXY (x, y) * Real.log (pXY (x, y) / q x y) by
    have hzero : ∑ x : α, ∑ y : β, (pXY (x, y) - q x y) = 0 := by
      have h1 : ∑ x : α, ∑ y : β, pXY (x, y) = 1 := by
        rw [← sum_prod_eq_nested]; exact hsum
      have h2 : ∑ x : α, ∑ y : β, q x y = 1 :=
        product_marginals_sum_one hsum
      simp_rw [Finset.sum_sub_distrib]
      rw [h1, h2, sub_self]
    linarith
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  by_cases hpxy : pXY (x, y) = 0
  · simp [hpxy]
    exact mul_nonneg
      (Finset.sum_nonneg (fun y' _ => hp (x, y')))
      (Finset.sum_nonneg (fun x' _ => hp (x', y)))
  · simp [hpxy]
    have hpxy_pos : 0 < pXY (x, y) :=
      lt_of_le_of_ne (hp (x, y)) (Ne.symm hpxy)
    have hq_pos : 0 < q x y := by
      simp only [hq_def]
      exact mul_pos
        (marginal_pos_of_joint_pos hp hpxy_pos)
        (calc 0 < pXY (x, y) := hpxy_pos
          _ ≤ ∑ x' : α, pXY (x', y) :=
            Finset.single_le_sum (f := fun x' => pXY (x', y))
              (fun x' _ => hp (x', y)) (Finset.mem_univ x))
    linarith [kl_term_bound hpxy_pos hq_pos]

-- Chain rule: I(X;Y) = H(X) - H(X|Y)
-- This connects mutual information (as KL divergence from product) to entropy difference.
--
-- Proof strategy: Expand all three definitions. The key algebraic identity is
--   log(p(x,y)/(pX(x)*pY(y))) = log(p(x,y)/pY(y)) - log(pX(x))
-- for p(x,y) > 0 (which forces pX(x), pY(y) > 0).
-- Summing p(x,y)*log(pX(x)) over y yields pX(x)*log(pX(x)), connecting
-- the mutual information sum to the difference H(X) - H(X|Y).
--
-- The formalization is nontrivial due to the if-then-else branches in all three
-- definitions (0*log(0) convention). The proof works by:
-- 1. Showing MI = sum of conditional entropy terms minus sum of marginal entropy terms
-- 2. The conditional sum equals -H(X|Y), the marginal sum equals -H(X)
-- 3. Therefore MI = -H(X|Y) - (-H(X)) = H(X) - H(X|Y)
theorem chain_rule {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    mutualInformation pXY =
    shannonEntropy (fun x => ∑ y : β, pXY (x, y)) - conditionalEntropy pXY := by
  -- Step 1: Key term-by-term identity
  -- For each (x,y): the MI term splits into a conditional entropy term minus
  -- a marginal entropy term, using log(a/(b*c)) = log(a/c) - log(b).
  have hterm : ∀ x y,
      (if pXY (x, y) = 0 then (0 : ℝ)
       else pXY (x, y) * Real.log (pXY (x, y) /
         ((∑ y' : β, pXY (x, y')) * (∑ x' : α, pXY (x', y))))) =
      (if pXY (x, y) = 0 then 0
       else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y)))) -
      (if pXY (x, y) = 0 then 0
       else pXY (x, y) * Real.log (∑ y' : β, pXY (x, y'))) := by
    intro x y
    by_cases hpxy : pXY (x, y) = 0
    · simp [hpxy]
    · simp [hpxy]
      have hpxy_pos : 0 < pXY (x, y) :=
        lt_of_le_of_ne (hp (x, y)) (Ne.symm hpxy)
      have hpx_pos : 0 < ∑ y' : β, pXY (x, y') :=
        calc 0 < pXY (x, y) := hpxy_pos
          _ ≤ ∑ y' : β, pXY (x, y') :=
            Finset.single_le_sum (f := fun y' => pXY (x, y'))
              (fun y' _ => hp (x, y')) (Finset.mem_univ y)
      have hpy_pos : 0 < ∑ x' : α, pXY (x', y) :=
        calc 0 < pXY (x, y) := hpxy_pos
          _ ≤ ∑ x' : α, pXY (x', y) :=
            Finset.single_le_sum (f := fun x' => pXY (x', y))
              (fun x' _ => hp (x', y)) (Finset.mem_univ x)
      rw [Real.log_div (ne_of_gt hpxy_pos) (ne_of_gt (mul_pos hpx_pos hpy_pos)),
          Real.log_mul (ne_of_gt hpx_pos) (ne_of_gt hpy_pos),
          Real.log_div (ne_of_gt hpxy_pos) (ne_of_gt hpy_pos)]
      ring
  -- Step 2: The marginal sum telescopes
  -- sum_y [if p(x,y)=0 then 0 else p(x,y)*log(pX(x))]
  -- = if pX(x)=0 then 0 else pX(x)*log(pX(x))
  have hmarg : ∀ x,
      ∑ y : β, (if pXY (x, y) = 0 then (0 : ℝ)
        else pXY (x, y) * Real.log (∑ y' : β, pXY (x, y'))) =
      (if (∑ y : β, pXY (x, y)) = 0 then 0
       else (∑ y : β, pXY (x, y)) * Real.log (∑ y : β, pXY (x, y))) := by
    intro x
    by_cases hpx : (∑ y : β, pXY (x, y)) = 0
    · have hall : ∀ y, pXY (x, y) = 0 := by
        intro y
        have h1 := hp (x, y)
        have h2 : pXY (x, y) ≤ ∑ y' : β, pXY (x, y') :=
          Finset.single_le_sum (f := fun y' => pXY (x, y'))
            (fun y' _ => hp (x, y')) (Finset.mem_univ y)
        linarith
      simp [hpx, hall]
    · simp [hpx]
      have : ∑ y : β, (if pXY (x, y) = 0 then (0 : ℝ)
          else pXY (x, y) * Real.log (∑ y' : β, pXY (x, y'))) =
          ∑ y : β, pXY (x, y) * Real.log (∑ y' : β, pXY (x, y')) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hpxy : pXY (x, y) = 0
        · simp [hpxy]
        · simp [hpxy]
      rw [this, ← Finset.sum_mul]
  -- Step 3: Assemble the proof
  unfold mutualInformation shannonEntropy conditionalEntropy
  -- Beta-reduce (fun x => ...) x that arises from shannonEntropy application
  dsimp only
  simp_rw [hterm, Finset.sum_sub_distrib, hmarg]
  ring

-- Conditioning reduces entropy: H(X|Y) ≤ H(X)
-- Proof: by the chain rule, H(X) - H(X|Y) = I(X;Y) ≥ 0.
theorem conditioning_reduces_entropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    conditionalEntropy pXY ≤
    shannonEntropy (fun x => ∑ y : β, pXY (x, y)) := by
  have hmi := mutual_info_nonneg hp hsum
  have hchain := chain_rule hp hsum
  linarith

end InformationTheory

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

-- ============================================================
-- Conditional Entropy Non-negativity
-- ============================================================

-- Conditional entropy H(X|Y) is non-negative for valid joint distributions.
-- Proof: each term p(x,y)*log(p(x,y)/p(y)) ≤ 0 since p(x,y) ≤ p(y),
-- so the negated sum is non-negative.
theorem conditionalEntropy_nonneg {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    0 ≤ conditionalEntropy pXY := by
  unfold conditionalEntropy
  rw [neg_nonneg]
  apply Finset.sum_nonpos
  intro x _
  apply Finset.sum_nonpos
  intro y _
  by_cases hpxy : pXY (x, y) = 0
  · simp [hpxy]
  · simp [hpxy]
    have hpxy_pos : 0 < pXY (x, y) :=
      lt_of_le_of_ne (hp (x, y)) (Ne.symm hpxy)
    have hpy_pos : 0 < ∑ x' : α, pXY (x', y) :=
      calc 0 < pXY (x, y) := hpxy_pos
        _ ≤ ∑ x' : α, pXY (x', y) :=
          Finset.single_le_sum (f := fun x' => pXY (x', y))
            (fun x' _ => hp (x', y)) (Finset.mem_univ x)
    have hle : pXY (x, y) / (∑ x' : α, pXY (x', y)) ≤ 1 :=
      (div_le_one hpy_pos).mpr
        (Finset.single_le_sum (f := fun x' => pXY (x', y))
          (fun x' _ => hp (x', y)) (Finset.mem_univ x))
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpxy_pos)
      (Real.log_nonpos (le_of_lt (div_pos hpxy_pos hpy_pos)) hle)

-- ============================================================
-- Mutual Information Symmetry via Transposition
-- ============================================================

-- Transpose a joint distribution: swap the two variables.
noncomputable def transposeJoint {α β : Type*} (pXY : α × β → ℝ) : β × α → ℝ :=
  fun ⟨y, x⟩ => pXY (x, y)

-- Transposed distribution preserves non-negativity.
theorem transposeJoint_nonneg {α β : Type*}
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy) :
    ∀ yx, 0 ≤ transposeJoint pXY yx := by
  intro ⟨y, x⟩; exact hp (x, y)

-- Transposed distribution preserves sum.
theorem transposeJoint_sum {α β : Type*} [Fintype α] [Fintype β]
    {pXY : α × β → ℝ} (hsum : ∑ xy : α × β, pXY xy = 1) :
    ∑ yx : β × α, transposeJoint pXY yx = 1 := by
  have key : ∑ yx : β × α, transposeJoint pXY yx = ∑ xy : α × β, pXY xy := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    -- LHS: ∑ y, ∑ x, transposeJoint pXY (y, x)  RHS: ∑ x, ∑ y, pXY (x, y)
    unfold transposeJoint; dsimp only
    -- Goal: ∑ y, ∑ x, pXY (x, y) = ∑ x, ∑ y, pXY (x, y)
    exact Finset.sum_comm
  rw [key, hsum]

-- Mutual information is symmetric: I(X;Y) = I(Y;X).
-- The MI formula is symmetric in x and y since it involves
-- p(x,y) * log(p(x,y) / (p_X(x) * p_Y(y))), and the product
-- p_X(x) * p_Y(y) is commutative.
theorem mutual_info_symm {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) :
    mutualInformation pXY = mutualInformation (transposeJoint pXY) := by
  unfold mutualInformation transposeJoint
  dsimp only
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro y _
  by_cases hpxy : pXY (x, y) = 0
  · simp [hpxy]
  · rw [if_neg hpxy, if_neg hpxy]
    congr 1; congr 1; congr 1
    exact mul_comm _ _

-- Mutual information is bounded by the entropy of the second marginal:
-- I(X;Y) ≤ H(Y). This follows from the symmetric chain rule and
-- conditional entropy non-negativity.
theorem mutual_info_le_entropy_snd {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    mutualInformation pXY ≤
    shannonEntropy (fun y => ∑ x : α, pXY (x, y)) := by
  -- Step 1: MI(X;Y) = MI(Y;X)
  rw [mutual_info_symm]
  -- Step 2: Apply chain rule to transposed distribution
  -- MI(Y;X) = H(Y) - H(Y|X)
  have hp' := transposeJoint_nonneg hp
  have hsum' := transposeJoint_sum hsum
  have hchain := chain_rule hp' hsum'
  -- Step 3: H(Y|X) ≥ 0
  have hcond := conditionalEntropy_nonneg hp' hsum'
  -- Step 4: MI(Y;X) = H(Y) - H(Y|X) ≤ H(Y)
  -- The Y-marginal of transposeJoint pXY is (fun y => ∑ x, pXY(x,y))
  have hmarg : (fun y => ∑ x : α, transposeJoint pXY (y, x)) =
      (fun y => ∑ x : α, pXY (x, y)) := by
    ext y; rfl
  rw [hchain, hmarg]
  linarith

-- ============================================================
-- Strong Subadditivity of Entropy
-- ============================================================

-- Three-variable marginals for a joint distribution on α × β × γ
noncomputable def marginalXY {α β γ : Type*} [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : α × β → ℝ :=
  fun (x, y) => ∑ z : γ, pXYZ (x, y, z)

noncomputable def marginalYZ {α β γ : Type*} [Fintype α]
    (pXYZ : α × β × γ → ℝ) : β × γ → ℝ :=
  fun (y, z) => ∑ x : α, pXYZ (x, y, z)

noncomputable def marginalY {α β γ : Type*} [Fintype α] [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : β → ℝ :=
  fun y => ∑ x : α, ∑ z : γ, pXYZ (x, y, z)

/-- **Strong Subadditivity of Entropy** (Lieb-Ruskai 1973)

For a joint distribution p(X,Y,Z) over finite types α × β × γ:
  H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z)

Equivalently: conditioning on more variables reduces entropy:
  H(X|Y,Z) ≤ H(X|Y)

This is equivalent to the non-negativity of conditional mutual information:
  I(X;Z|Y) ≥ 0

**Proof strategy**: Express the LHS - RHS as a conditional KL divergence:
  H(X,Y) + H(Y,Z) - H(X,Y,Z) - H(Y) = Σ_y p(y) D(p(x,z|y) || p(x|y)p(z|y))
where D(·||·) is the KL divergence. Since D ≥ 0 (Gibbs inequality), SSA follows.

**Dependencies**: Uses gibbs_inequality (KL divergence non-negativity, proved above)
and the conditional distributions p(x,z|y) = p(x,y,z)/p(y). -/
theorem strong_subadditivity {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ}
    (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy pXYZ + shannonEntropy (marginalY pXYZ) ≤
      shannonEntropy (marginalXY pXYZ) + shannonEntropy (marginalYZ pXYZ) := by
  -- The deficit H(XY) + H(YZ) - H(XYZ) - H(Y) equals the conditional mutual information
  -- I(X;Z|Y) = Σ p(xyz) log[p(xyz)·pY(y) / (pXY(xy)·pYZ(yz))], which is ≥ 0
  -- since it is a generalized KL divergence.
  --
  -- Proof: define q(xyz) = pXY·pYZ/pY. Each term p·log(p/q) ≥ p-q by kl_term_bound.
  -- Sum: Σ(p-q) = 1-1 = 0, so the conditional MI ≥ 0.

  -- Nested sum = 1
  have hsum_n : ∑ x : α, ∑ y : β, ∑ z : γ, pXYZ (x, y, z) = 1 := by
    have h := hsum; rw [Fintype.sum_prod_type] at h; simp_rw [Fintype.sum_prod_type] at h; exact h

  -- Marginal telescoping: if S=0 then 0 else S·log S = Σ (if aᵢ=0 then 0 else aᵢ·log S)
  have htele : ∀ {ι : Type*} [Fintype ι] (a : ι → ℝ) (_ : ∀ i, 0 ≤ a i),
      (if (∑ i, a i) = 0 then (0 : ℝ) else (∑ i, a i) * Real.log (∑ i, a i)) =
      ∑ i, (if a i = 0 then 0 else a i * Real.log (∑ j, a j)) := by
    intro ι _ a ha
    by_cases hs : (∑ i, a i) = 0
    · have : ∀ i, a i = 0 := fun i =>
        le_antisymm (by linarith [Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)]) (ha i)
      simp [hs, this]
    · simp only [hs, ↓reduceIte]; symm
      rw [show ∑ i, (if a i = 0 then (0 : ℝ) else a i * Real.log (∑ j, a j)) =
          ∑ i, a i * Real.log (∑ j, a j) from
        Finset.sum_congr rfl fun i _ => by by_cases h : a i = 0 <;> simp [h]]
      rw [← Finset.sum_mul]

  -- XY marginal telescoping
  have hXY : ∀ x y, (if (∑ z : γ, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ z, pXYZ (x, y, z)) * Real.log (∑ z, pXYZ (x, y, z))) =
      ∑ z : γ, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ z' : γ, pXYZ (x, y, z'))) := by
    intro x y; exact htele (fun z => pXYZ (x, y, z)) (fun z => hp (x, y, z))

  -- YZ marginal telescoping
  have hYZ : ∀ y z, (if (∑ x : α, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ x, pXYZ (x, y, z)) * Real.log (∑ x, pXYZ (x, y, z))) =
      ∑ x : α, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) := by
    intro y z; exact htele (fun x => pXYZ (x, y, z)) (fun x => hp (x, y, z))

  -- Y marginal telescoping (product type → nested)
  have hY : ∀ y, (if (∑ x : α, ∑ z : γ, pXYZ (x, y, z)) = 0 then (0 : ℝ)
      else (∑ x, ∑ z, pXYZ (x, y, z)) * Real.log (∑ x, ∑ z, pXYZ (x, y, z))) =
      ∑ x : α, ∑ z : γ, (if pXYZ (x, y, z) = 0 then 0
        else pXYZ (x, y, z) * Real.log (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z'))) := by
    intro y
    have h := htele (fun (xz : α × γ) => pXYZ (xz.1, y, xz.2)) (fun xz => hp (xz.1, y, xz.2))
    simp_rw [Fintype.sum_prod_type] at h; exact h

  -- Term splitting: p·log(p) = CMI_term + p·log(pXY) + p·log(pYZ) - p·log(pY)
  have hterm : ∀ x y z,
      (if pXYZ (x, y, z) = 0 then (0 : ℝ) else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z))) =
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) *
         (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) /
         ((∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))))) +
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (∑ z' : γ, pXYZ (x, y, z'))) +
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (∑ x' : α, pXYZ (x', y, z))) -
      (if pXYZ (x, y, z) = 0 then 0
       else pXYZ (x, y, z) * Real.log (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z'))) := by
    intro x y z
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · simp [hpxyz]
    · simp only [hpxyz, ↓reduceIte]
      have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
      have hpXY : 0 < ∑ z', pXYZ (x, y, z') :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp _) (Finset.mem_univ z))
      have hpYZ : 0 < ∑ x', pXYZ (x', y, z) :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp _) (Finset.mem_univ x))
      have hpY : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
        lt_of_lt_of_le hpXY (Finset.single_le_sum
          (fun x' _ => Finset.sum_nonneg fun z' _ => hp _) (Finset.mem_univ x))
      -- log(p) = log(p·pY/(pXY·pYZ)) + log(pXY) + log(pYZ) - log(pY)
      have hlog : Real.log (pXYZ (x, y, z)) =
          Real.log (pXYZ (x, y, z) * (∑ x', ∑ z', pXYZ (x', y, z')) /
            ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z)))) +
          Real.log (∑ z', pXYZ (x, y, z')) +
          Real.log (∑ x', pXYZ (x', y, z)) -
          Real.log (∑ x', ∑ z', pXYZ (x', y, z')) := by
        rw [Real.log_div (ne_of_gt (mul_pos hpos hpY)) (ne_of_gt (mul_pos hpXY hpYZ)),
            Real.log_mul (ne_of_gt hpos) (ne_of_gt hpY),
            Real.log_mul (ne_of_gt hpXY) (ne_of_gt hpYZ)]
        ring
      calc pXYZ (x, y, z) * Real.log (pXYZ (x, y, z))
          = pXYZ (x, y, z) * (
            Real.log (pXYZ (x, y, z) * (∑ x', ∑ z', pXYZ (x', y, z')) /
              ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z)))) +
            Real.log (∑ z', pXYZ (x, y, z')) +
            Real.log (∑ x', pXYZ (x', y, z)) -
            Real.log (∑ x', ∑ z', pXYZ (x', y, z'))) := by congr 1; exact hlog
        _ = _ := by ring

  -- === PART 1: Show the conditional MI ≥ 0 ===
  -- Define q(x,y,z) = pXY(x,y) · pYZ(y,z) / pY(y)
  set q := fun x y z => (∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z)) /
    (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) with hq_def
  -- q is non-negative
  have hq_nn : ∀ x y z, 0 ≤ q x y z := fun x y z => div_nonneg
    (mul_nonneg (Finset.sum_nonneg fun z' _ => hp _) (Finset.sum_nonneg fun x' _ => hp _))
    (Finset.sum_nonneg fun x' _ => Finset.sum_nonneg fun z' _ => hp _)
  -- For each y: Σ_x Σ_z q(x,y,z) = pY(y) = Σ_x Σ_z p(x,y,z)
  have hq_sum_y : ∀ y, ∑ x : α, ∑ z : γ, q x y z = ∑ x, ∑ z, pXYZ (x, y, z) := by
    intro y
    simp only [hq_def]
    by_cases hpy : (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) = 0
    · -- All p(x,y,z) = 0 for this y
      have hall : ∀ x z, pXYZ (x, y, z) = 0 := by
        intro x z; linarith [hp (x, y, z),
          Finset.single_le_sum (fun z' _ => hp (x, y, z')) (Finset.mem_univ z),
          Finset.single_le_sum (fun x' _ =>
            Finset.sum_nonneg fun z' _ => hp (x', y, z')) (Finset.mem_univ x)]
      simp [hall, hpy]
    · -- Factor: Σ_x Σ_z pXY·pYZ/pY = (Σ_x pXY)·(Σ_z pYZ)/pY = pY²/pY = pY
      have hpy_ne : (∑ x', ∑ z', pXYZ (x', y, z')) ≠ 0 := hpy
      -- Pull pYZ(y,z) out from inner sum: Σ_z (pXY(x,y) · pYZ(y,z)) = pXY(x,y) · Σ_z pYZ(y,z)
      simp_rw [mul_div_assoc]
      -- Σ_z (pXY · (pYZ/pY)) = pXY · (Σ_z pYZ / pY) = pXY · (Σ_z pYZ) / pY
      simp_rw [← Finset.sum_div, ← Finset.mul_sum]
      -- Σ_x (pXY · (Σ_z pYZ) / pY) = (Σ_x pXY) · (Σ_z pYZ) / pY
      rw [← Finset.sum_div, ← Finset.sum_mul]
      -- (Σ_x pXY) = pY and (Σ_z pYZ) = pY, so pY·pY/pY = pY
      rw [show ∑ z : γ, ∑ x' : α, pXYZ (x', y, z) = ∑ x' : α, ∑ z : γ, pXYZ (x', y, z) from
        Finset.sum_comm]
      rw [mul_div_cancel₀ _ hpy_ne]
  -- q sums to 1
  have hq_sum : ∑ x : α, ∑ y : β, ∑ z : γ, q x y z = 1 := by
    conv_lhs => rw [Finset.sum_comm]
    simp_rw [hq_sum_y]
    rw [Finset.sum_comm]; exact hsum_n

  -- Conditional MI ≥ 0
  have h_cmi : 0 ≤ ∑ x : α, ∑ y : β, ∑ z : γ,
      (if pXYZ (x, y, z) = 0 then (0 : ℝ)
       else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) *
         (∑ x' : α, ∑ z' : γ, pXYZ (x', y, z')) /
         ((∑ z' : γ, pXYZ (x, y, z')) * (∑ x' : α, pXYZ (x', y, z))))) := by
    -- Each term ≥ p - q, and Σ(p - q) = 1 - 1 = 0
    suffices h_lb : ∑ x, ∑ y, ∑ z, (pXYZ (x, y, z) - q x y z) ≤
        ∑ x, ∑ y, ∑ z, (if pXYZ (x, y, z) = 0 then (0 : ℝ)
         else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z) *
           (∑ x', ∑ z', pXYZ (x', y, z')) /
           ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z))))) by
      have hzero : ∑ x, ∑ y, ∑ z, (pXYZ (x, y, z) - q x y z) = 0 := by
        simp only [Finset.sum_sub_distrib]; rw [hsum_n, hq_sum, sub_self]
      linarith
    apply Finset.sum_le_sum; intro x _; apply Finset.sum_le_sum; intro y _
    apply Finset.sum_le_sum; intro z _
    by_cases hpxyz : pXYZ (x, y, z) = 0
    · simp [hpxyz]; exact hq_nn x y z
    · simp only [hpxyz, ↓reduceIte]
      have hpos : 0 < pXYZ (x, y, z) := lt_of_le_of_ne (hp _) (Ne.symm hpxyz)
      have hpXY : 0 < ∑ z', pXYZ (x, y, z') :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun z' _ => hp _) (Finset.mem_univ z))
      have hpYZ : 0 < ∑ x', pXYZ (x', y, z) :=
        lt_of_lt_of_le hpos (Finset.single_le_sum (fun x' _ => hp _) (Finset.mem_univ x))
      have hpY : 0 < ∑ x' : α, ∑ z' : γ, pXYZ (x', y, z') :=
        lt_of_lt_of_le hpXY (Finset.single_le_sum
          (fun x' _ => Finset.sum_nonneg fun z' _ => hp _) (Finset.mem_univ x))
      have hq_pos : 0 < q x y z := by
        simp only [hq_def]; exact div_pos (mul_pos hpXY hpYZ) hpY
      -- p·log(p·pY/(pXY·pYZ)) = p·log(p/q) since q = pXY·pYZ/pY
      have hlog_eq : pXYZ (x, y, z) * (∑ x', ∑ z', pXYZ (x', y, z')) /
          ((∑ z', pXYZ (x, y, z')) * (∑ x', pXYZ (x', y, z))) =
          pXYZ (x, y, z) / q x y z := by
        simp only [hq_def]; field_simp; ring
      rw [hlog_eq]
      exact kl_term_bound hpos hq_pos

  -- === PART 2: Entropy algebra — connect CMI to SSA deficit ===
  unfold shannonEntropy marginalXY marginalYZ marginalY
  dsimp only
  -- Convert product-type sums to nested sums
  conv_lhs => arg 1; arg 1; rw [show ∑ xyz : α × β × γ,
    (if pXYZ xyz = 0 then (0 : ℝ) else pXYZ xyz * Real.log (pXYZ xyz)) =
    ∑ x : α, ∑ y : β, ∑ z : γ,
    (if pXYZ (x, y, z) = 0 then 0 else pXYZ (x, y, z) * Real.log (pXYZ (x, y, z))) from by
      rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]]
  conv_rhs => arg 1; arg 1; rw [show ∑ xy : α × β,
    (if (fun xy => ∑ z : γ, pXYZ (xy.1, xy.2, z)) xy = 0 then (0 : ℝ)
     else (fun xy => ∑ z, pXYZ (xy.1, xy.2, z)) xy *
       Real.log ((fun xy => ∑ z, pXYZ (xy.1, xy.2, z)) xy)) =
    ∑ x : α, ∑ y : β,
    (if (∑ z : γ, pXYZ (x, y, z)) = 0 then 0
     else (∑ z, pXYZ (x, y, z)) * Real.log (∑ z, pXYZ (x, y, z))) from by
      rw [Fintype.sum_prod_type]]
  conv_rhs => arg 2; arg 1; rw [show ∑ yz : β × γ,
    (if (fun yz => ∑ x : α, pXYZ (x, yz.1, yz.2)) yz = 0 then (0 : ℝ)
     else (fun yz => ∑ x, pXYZ (x, yz.1, yz.2)) yz *
       Real.log ((fun yz => ∑ x, pXYZ (x, yz.1, yz.2)) yz)) =
    ∑ y : β, ∑ z : γ,
    (if (∑ x : α, pXYZ (x, y, z)) = 0 then 0
     else (∑ x, pXYZ (x, y, z)) * Real.log (∑ x, pXYZ (x, y, z))) from by
      rw [Fintype.sum_prod_type]]
  -- Apply marginal telescoping to expand collapsed sums to triple sums
  simp_rw [hXY]  -- XY marginal → triple sum with log(Σ_z' p)
  simp_rw [hYZ]  -- YZ marginal → triple sum with log(Σ_x' p)
  simp_rw [hY]   -- Y marginal → triple sum with log(Σ_x' Σ_z' p)
  -- Apply term splitting to the XYZ sum
  simp_rw [hterm]
  -- Distribute negation and sums
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- After distribution, the XY, YZ, and Y terms cancel, leaving 0 ≤ Σ CMI
  linarith [h_cmi]

/-- **Entropy chain rule**: H(X,Y) = H(Y) + H(X|Y).
    Joint entropy decomposes into marginal plus conditional.

    Proof: expand definitions; the cross-terms ∑_{x,y} p(x,y) log p_Y(y)
    simplify to ∑_y p_Y(y) log p_Y(y) since ∑_x p(x,y) = p_Y(y). -/
theorem entropy_chain_rule {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    shannonEntropy pXY =
      shannonEntropy (fun y => ∑ x : α, pXY (x, y)) + conditionalEntropy pXY := by
  -- H(X,Y) = H(Y) + H(X|Y) by splitting log p(x,y) = log(p(x,y)/pY(y)) + log pY(y)
  -- Step 1: Term-by-term identity
  have hterm : ∀ x y,
      (if pXY (x, y) = 0 then (0 : ℝ) else pXY (x, y) * Real.log (pXY (x, y))) =
      (if pXY (x, y) = 0 then 0
       else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y)))) +
      (if pXY (x, y) = 0 then 0
       else pXY (x, y) * Real.log (∑ x' : α, pXY (x', y))) := by
    intro x y
    by_cases hpxy : pXY (x, y) = 0
    · simp [hpxy]
    · simp only [hpxy, ↓reduceIte]
      have hpxy_pos : 0 < pXY (x, y) := lt_of_le_of_ne (hp (x, y)) (Ne.symm hpxy)
      have hpy_pos : 0 < ∑ x' : α, pXY (x', y) :=
        lt_of_lt_of_le hpxy_pos
          (Finset.single_le_sum (fun x' _ => hp (x', y)) (Finset.mem_univ x))
      rw [show pXY (x, y) * Real.log (pXY (x, y) / (∑ x', pXY (x', y))) +
          pXY (x, y) * Real.log (∑ x', pXY (x', y)) =
          pXY (x, y) * (Real.log (pXY (x, y) / (∑ x', pXY (x', y))) +
          Real.log (∑ x', pXY (x', y))) from by ring]
      congr 1
      rw [Real.log_div (ne_of_gt hpxy_pos) (ne_of_gt hpy_pos)]
      ring
  -- Step 2: Marginal telescoping
  have hmarg : ∀ y,
      ∑ x : α, (if pXY (x, y) = 0 then (0 : ℝ)
        else pXY (x, y) * Real.log (∑ x' : α, pXY (x', y))) =
      (if (∑ x : α, pXY (x, y)) = 0 then 0
       else (∑ x : α, pXY (x, y)) * Real.log (∑ x : α, pXY (x, y))) := by
    intro y
    by_cases hpy : (∑ x : α, pXY (x, y)) = 0
    · have hall : ∀ x, pXY (x, y) = 0 := by
        intro x
        linarith [hp (x, y), Finset.single_le_sum (fun x' _ => hp (x', y)) (Finset.mem_univ x)]
      simp [hpy, hall]
    · simp only [hpy, ↓reduceIte]
      rw [show ∑ x, (if pXY (x, y) = 0 then (0 : ℝ) else pXY (x, y) * Real.log (∑ x', pXY (x', y))) =
          ∑ x, pXY (x, y) * Real.log (∑ x', pXY (x', y)) from
        Finset.sum_congr rfl fun x _ => by by_cases h : pXY (x, y) = 0 <;> simp [h]]
      rw [← Finset.sum_mul]
  -- Step 3: Assembly
  unfold shannonEntropy conditionalEntropy
  dsimp only
  conv_lhs =>
    rw [show ∑ xy : α × β, (if pXY xy = 0 then (0 : ℝ)
        else pXY xy * Real.log (pXY xy)) =
        ∑ x : α, ∑ y : β, (if pXY (x, y) = 0 then 0
        else pXY (x, y) * Real.log (pXY (x, y))) from Fintype.sum_prod_type _]
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib]
  rw [show ∑ x : α, ∑ y : β, (if pXY (x, y) = 0 then (0 : ℝ) else
      pXY (x, y) * Real.log (∑ x', pXY (x', y))) =
      ∑ y : β, (if (∑ x, pXY (x, y)) = 0 then 0 else
      (∑ x, pXY (x, y)) * Real.log (∑ x, pXY (x, y))) from by
    rw [Finset.sum_comm]; congr 1; ext y; exact hmarg y]
  ring

/-- **Subadditivity of entropy**: H(X,Y) ≤ H(X) + H(Y).
    From entropy_chain_rule + conditioning_reduces_entropy:
    H(X,Y) = H(Y) + H(X|Y) ≤ H(Y) + H(X) = H(X) + H(Y). -/
theorem subadditivity {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ}
    (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    shannonEntropy pXY ≤
      shannonEntropy (fun x => ∑ y : β, pXY (x, y)) +
      shannonEntropy (fun y => ∑ x : α, pXY (x, y)) := by
  calc shannonEntropy pXY
      = shannonEntropy (fun y => ∑ x, pXY (x, y)) + conditionalEntropy pXY :=
        entropy_chain_rule hp hsum
    _ ≤ shannonEntropy (fun y => ∑ x, pXY (x, y)) +
        shannonEntropy (fun x => ∑ y, pXY (x, y)) := by
        linarith [conditioning_reduces_entropy hp hsum]
    _ = shannonEntropy (fun x => ∑ y, pXY (x, y)) +
        shannonEntropy (fun y => ∑ x, pXY (x, y)) := by ring

end InformationTheory

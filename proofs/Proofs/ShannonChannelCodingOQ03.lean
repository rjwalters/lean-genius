/-
  Fano's Inequality

  Formal proof of: H(X|Y) ≤ h(P_e) + P_e · log(|X| - 1)

  This file proves Fano's inequality, replacing the axiom `fano_inequality`
  in `ShannonChannelCoding.lean`.

  The "formula P_e" used in the gallery equals:
    P_e^{formula} = 1 - ∑_y ∑_x P(X=x,Y=y)² / P(Y=y)
  This satisfies P_e^{MAP} ≤ P_e^{formula}, where P_e^{MAP} is the minimum
  achievable error probability (under the MAP decoder). With monotonicity of
  h(p) + p·log(n-1), this gives the stated bound.

  This file is self-contained: it does not import Proofs.ShannonEntropy
  (which has a pre-existing build issue in strong_subadditivity).

  Proof structure:
  1. [PROVED]  sum_sq_le_max         — ∑q(x)² ≤ max q(x) for any prob. dist.
  2. [PROVED]  slice_sq_le_max       — per-slice ∑pXY²/P(y) ≤ max pXY
  3. [PROVED]  formula_pe_ge_map_pe  — P_e^{MAP} ≤ P_e^{formula}
  4. [PROVED]  gibbs_inequality      — H(p) ≤ -∑ p·log q (KL divergence ≥ 0)
  5. [SORRY]   fano_per_element      — per-y Fano via Gibbs inequality
  6. [SORRY]   fano_map_bound        — H(X|Y) ≤ h(P_e^{MAP}) + P_e^{MAP}·log(n-1)
  7. [SORRY]   fano_func_mono        — monotonicity of h(p) + p·log(c)
  8. Main:     fano_theorem

  Claude Shannon (1948) — Fano (1952)
  Sorries: 4
-/
import Mathlib
import Proofs.ShannonChannelCodingOQ04

open Real Finset InformationTheory.BinaryEntropy

namespace FanoInequality

-- ============================================================
-- Section 1: Information-Theoretic Definitions (Self-Contained)
-- ============================================================

/-- Shannon entropy for a finite distribution.
    Convention: 0 · log 0 = 0. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

/-- Conditional entropy H(X|Y) for a joint distribution pXY on α × β.
    H(X|Y) = -∑_{x,y} pXY(x,y) · log(pXY(x,y) / P(Y=y)). -/
noncomputable def conditionalEntropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) : ℝ :=
  -(∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y))))

-- ============================================================
-- Section 1b: KL Divergence Helper (inline from OQ04)
-- ============================================================

/-- KL divergence term: p·log(p/q) ≥ p - q for p > 0, q > 0.
    Inline copy of kl_term_bound from OQ04 (private there). -/
private lemma kl_term_bound' {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p - q ≤ p * Real.log (p / q) := by
  have h1 : Real.log (q / p) ≤ q / p - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hq hp)
  have h2 : p * Real.log (q / p) ≤ q - p :=
    calc p * Real.log (q / p)
        ≤ p * (q / p - 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hp)
      _ = q - p := by field_simp
  have h3 : Real.log (p / q) = -Real.log (q / p) := by
    rw [Real.log_div (ne_of_gt hp) (ne_of_gt hq),
        Real.log_div (ne_of_gt hq) (ne_of_gt hp)]
    ring
  linarith [show p * Real.log (p / q) = -(p * Real.log (q / p)) by rw [h3]; ring]

-- ============================================================
-- Section 2: Gibbs Inequality (PROVED)
-- ============================================================

/-- **[PROVED] Gibbs inequality**: H(p) ≤ -∑ p(x)·log q(x) for any distributions p, q.
    Equivalently, KL divergence D(p||q) = ∑ p·log(p/q) ≥ 0.

    Proof: For each x with p(x) > 0: p(x)·log(p(x)/q(x)) ≥ p(x) - q(x).
    Summing: ∑ p·log(p/q) ≥ ∑(p-q) = 1-1 = 0. -/
lemma gibbs_inequality {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    shannonEntropy p ≤ -∑ x, p x * Real.log (q x) := by
  simp only [shannonEntropy]
  -- The if-guard is redundant: when p x = 0, p x * log(p x) = 0
  have h_if : ∀ x : α,
      (if p x = 0 then (0:ℝ) else p x * Real.log (p x)) = p x * Real.log (p x) := by
    intro x
    split_ifs with h
    · simp [h]
    · rfl
  simp_rw [h_if]
  -- Goal: -∑ p*log p ≤ -∑ p*log q, i.e., ∑ p*log q ≤ ∑ p*log p
  rw [neg_le_neg_iff]
  -- Key: 0 ≤ KL divergence = ∑ p * log(p/q)
  have h_kl_nn : 0 ≤ ∑ x : α, p x * Real.log (p x / q x) := by
    have hkl : ∀ x : α, p x - q x ≤ p x * Real.log (p x / q x) := by
      intro x
      rcases eq_or_lt_of_le (hp x) with h0 | hpx
      · simp [show p x = 0 from h0.symm]; linarith [hq x]
      · exact kl_term_bound' hpx (hq x)
    have h1 : ∑ x : α, (p x - q x) ≤ ∑ x : α, p x * Real.log (p x / q x) :=
      Finset.sum_le_sum (fun x _ => hkl x)
    have h2 : ∑ x : α, (p x - q x) = 0 := by
      simp [Finset.sum_sub_distrib, hpsum, hqsum]
    linarith
  -- Expand: ∑ p*log(p/q) = ∑ p*log p - ∑ p*log q
  have h_expand : ∑ x : α, p x * Real.log (p x / q x) =
      ∑ x : α, p x * Real.log (p x) - ∑ x : α, p x * Real.log (q x) := by
    rw [← Finset.sum_sub_distrib]
    congr 1; ext x
    rcases eq_or_lt_of_le (hp x) with h0 | hpx
    · simp [← h0]
    · rw [Real.log_div (ne_of_gt hpx) (ne_of_gt (hq x)), mul_sub]
  rw [h_expand] at h_kl_nn
  linarith

-- ============================================================
-- Section 3: MAP Error Probability
-- ============================================================

/-- The maximum probability in a distribution on a finite nonempty type. -/
noncomputable def maxProb {α : Type*} [Fintype α] [Nonempty α] (q : α → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty q

/-- The MAP error probability: 1 - (sum of MAP-correct probabilities).
    P_e^{MAP} = 1 - ∑_y max_x pXY(x,y) -/
noncomputable def mapErrorProb {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (pXY : α × β → ℝ) : ℝ :=
  1 - ∑ y : β, maxProb (fun x => pXY (x, y))

-- ============================================================
-- Section 4: Core Algebraic Lemma (PROVED)
-- ============================================================

/-- **[PROVED] Core inequality**: For any probability distribution q on a
    nonempty finite type, ∑_x q(x)² ≤ max_x q(x). -/
theorem sum_sq_le_max {α : Type*} [Fintype α] [Nonempty α]
    {q : α → ℝ} (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1) :
    ∑ x, q x ^ 2 ≤ maxProb q := by
  unfold maxProb
  have hle : ∀ x : α, q x ≤ Finset.sup' Finset.univ Finset.univ_nonempty q :=
    fun x => Finset.le_sup' _ (Finset.mem_univ x)
  calc ∑ x : α, q x ^ 2
      ≤ ∑ x : α, Finset.sup' Finset.univ Finset.univ_nonempty q * q x := by
        apply Finset.sum_le_sum
        intro x _
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hle x) (hq x)
    _ = Finset.sup' Finset.univ Finset.univ_nonempty q * ∑ x : α, q x := by
        rw [← Finset.mul_sum]
    _ = Finset.sup' Finset.univ Finset.univ_nonempty q := by
        rw [hqsum, mul_one]

-- ============================================================
-- Section 5: Slice-wise Bound (PROVED)
-- ============================================================

/-- **[PROVED] Per-slice inequality**: For each y,
    ∑_x pXY(x,y)² / P(Y=y) ≤ max_x pXY(x,y)

    Proof:
    - When P(Y=y) = 0: all pXY(x,y) = 0, both sides are 0.
    - When P(Y=y) > 0: factor out P, bound each pXY²≤maxProb·pXY, sum. -/
lemma slice_sq_le_max {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    {pXY : α × β → ℝ} (hp : ∀ x, 0 ≤ pXY x) (y : β) :
    ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y)) ≤
      maxProb (fun x => pXY (x, y)) := by
  set P := ∑ x' : α, pXY (x', y)
  set M := maxProb (fun x => pXY (x, y))
  -- M ≥ each element
  have hM_le : ∀ x : α, pXY (x, y) ≤ M := by
    intro x; show pXY (x, y) ≤ maxProb (fun x => pXY (x, y))
    unfold maxProb
    exact Finset.le_sup' (fun x => pXY (x, y)) (Finset.mem_univ x)
  -- M ≥ 0
  obtain ⟨x0⟩ := (inferInstance : Nonempty α)
  have hM_nn : 0 ≤ M := le_trans (hp (x0, y)) (hM_le x0)
  by_cases hP : P = 0
  · -- P = 0: all pXY(x,y) = 0
    have hall : ∀ x : α, pXY (x, y) = 0 := by
      intro x
      have hge := hp (x, y)
      have hle : pXY (x, y) ≤ P := by
        apply Finset.single_le_sum (f := fun x' => pXY (x', y))
        · intro x' _; exact hp (x', y)
        · exact Finset.mem_univ x
      linarith [hP ▸ hle]
    -- LHS = ∑ 0²/0 = 0
    have : ∑ x : α, pXY (x, y) ^ 2 / P = 0 := by
      apply Finset.sum_eq_zero
      intro x _; simp [hall x, hP]
    rw [this]; exact hM_nn
  · -- P > 0
    have hP_pos : 0 < P :=
      lt_of_le_of_ne (Finset.sum_nonneg fun x _ => hp (x, y)) (Ne.symm hP)
    have hle : ∑ x : α, pXY (x, y) ^ 2 ≤ M * P :=
      calc ∑ x : α, pXY (x, y) ^ 2
          ≤ ∑ x : α, M * pXY (x, y) :=
            Finset.sum_le_sum fun x _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (hM_le x) (hp (x, y))
        _ = M * P := by rw [← Finset.mul_sum]
    calc ∑ x : α, pXY (x, y) ^ 2 / P
        = (∑ x : α, pXY (x, y) ^ 2) / P := by rw [← Finset.sum_div]
      _ ≤ M * P / P := by gcongr
      _ = M := by field_simp [ne_of_gt hP_pos]

-- ============================================================
-- Section 6: Formula P_e ≥ MAP P_e (PROVED)
-- ============================================================

/-- **[PROVED] The formula P_e upper-bounds the MAP P_e.** -/
theorem formula_pe_ge_map_pe {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    {pXY : α × β → ℝ} (hp : ∀ x, 0 ≤ pXY x) :
    mapErrorProb pXY ≤
      1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y)) := by
  unfold mapErrorProb
  linarith [Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => slice_sq_le_max hp y)]

-- ============================================================
-- Section 7: Per-Element Fano Bound (SORRY)
-- ============================================================

/-- **[SORRY] Per-element Fano bound**: For any probability distribution q on α
    with |α| ≥ 2:
      H(q) ≤ h(1 - max q) + (1 - max q) · log(|α| - 1)

    Proof sketch: Apply gibbs_inequality with bimodal reference Q:
      Q(x*) = maxProb q, Q(x) = (1-maxProb q)/(|α|-1) for x ≠ x*.
    Then compute -∑ q·log Q = h(maxProb q) + (1-maxProb q)·log(|α|-1)
                             = h(1-maxProb q) + (1-maxProb q)·log(|α|-1). -/
lemma fano_per_element {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (hn : 1 < Fintype.card α)
    {q : α → ℝ} (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1) :
    shannonEntropy q ≤
      h (1 - maxProb q) + (1 - maxProb q) * Real.log ((Fintype.card α : ℝ) - 1) := by
  sorry

-- ============================================================
-- Section 8: Conditional Entropy Fano Bound — MAP Version (SORRY)
-- ============================================================

/-- **[SORRY] Fano's inequality for the MAP decoder**:
      H(X|Y) ≤ h(P_e^{MAP}) + P_e^{MAP} · log(|X| - 1)

    Proof: Decompose H(X|Y) = ∑_y P(Y=y)·H(X|Y=y), apply fano_per_element
    per slice, use Jensen (h_concaveOn from OQ04) to aggregate. -/
lemma fano_map_bound {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hn : 1 < Fintype.card α)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    conditionalEntropy pXY ≤
      h (mapErrorProb pXY) +
      mapErrorProb pXY * Real.log ((Fintype.card α : ℝ) - 1) := by
  sorry

-- ============================================================
-- Section 9: Monotonicity of h(p) + p·log(c) (SORRY)
-- ============================================================

/-- **[SORRY] Fano bound function is monotone on [0, c/(1+c)]**:
    For c ≥ 1, f(p) = h(p) + p·log c is non-decreasing on [0, c/(1+c)].

    Proof: f'(p) = log(c(1-p)/p) ≥ 0 for p ≤ c/(1+c). -/
lemma fano_func_mono {c : ℝ} (hc : 1 ≤ c) {p₁ p₂ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : p₂ ≤ c / (1 + c)) (hpp : p₁ ≤ p₂) :
    h p₁ + p₁ * Real.log c ≤ h p₂ + p₂ * Real.log c := by
  sorry

-- ============================================================
-- Section 10: Main Theorem
-- ============================================================

/-- **[PROVED] MAP error probability is non-negative**.
    Follows from max_x pXY(x,y) ≤ ∑_x pXY(x,y), summed over y. -/
private lemma mapErrorProb_nonneg {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    {pXY : α × β → ℝ} (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    0 ≤ mapErrorProb pXY := by
  unfold mapErrorProb
  linarith [show ∑ y : β, maxProb (fun x => pXY (x, y)) ≤ 1 from by
    -- Each max ≤ column sum; sum of column sums = 1
    have hmax_le : ∀ y : β, maxProb (fun x => pXY (x, y)) ≤ ∑ x : α, pXY (x, y) := by
      intro y
      show Finset.sup' Finset.univ Finset.univ_nonempty (fun x => pXY (x, y)) ≤
           ∑ x : α, pXY (x, y)
      apply Finset.sup'_le
      intro x _
      show pXY (x, y) ≤ ∑ x' : α, pXY (x', y)
      apply Finset.single_le_sum (f := fun x' => pXY (x', y))
      · intro x' _; exact hp (x', y)
      · exact Finset.mem_univ x
    calc ∑ y : β, maxProb (fun x => pXY (x, y))
        ≤ ∑ y : β, ∑ x : α, pXY (x, y) :=
          Finset.sum_le_sum (fun y _ => hmax_le y)
      _ = ∑ p : α × β, pXY p := by
          rw [Finset.sum_comm]
          rw [← Fintype.sum_prod_type]
      _ = 1 := hsum]

/-- **Fano's Inequality** (main theorem):
    For a joint distribution pXY on finite α × β with |α| ≥ 2:
      H(X|Y) ≤ h(P_e) + P_e · log(|X| - 1)
    where P_e = 1 - ∑_y ∑_x P(X=x,Y=y)² / P(Y=y). -/
theorem fano_theorem {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hn : 1 < Fintype.card α)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    conditionalEntropy pXY ≤
      h P_e + P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  intro P_e
  -- n - 1 ≥ 1 since |X| ≥ 2
  have hc : (1 : ℝ) ≤ (Fintype.card α : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hn
    linarith
  -- MAP P_e ≥ 0
  have hmap_nn : 0 ≤ mapErrorProb pXY := mapErrorProb_nonneg hp hsum
  -- MAP P_e ≤ formula P_e
  have hpe_ineq : mapErrorProb pXY ≤ P_e := formula_pe_ge_map_pe hp
  -- Formula P_e ≤ (n-1)/n (sorry: Cauchy-Schwarz bound)
  have hpe_bound : P_e ≤ ((Fintype.card α : ℝ) - 1) / (1 + ((Fintype.card α : ℝ) - 1)) := by
    sorry
  -- Fano bound with MAP P_e
  have hmap_fano := fano_map_bound hn pXY hp hsum
  -- Monotonicity extends to formula P_e
  have hmono := fano_func_mono hc hmap_nn hpe_bound hpe_ineq
  linarith

end FanoInequality

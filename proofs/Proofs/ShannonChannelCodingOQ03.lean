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
  2. [PROVED]  slice_sq_le_max       — per-slice ∑ pXY²/P(Y) ≤ max pXY
  3. [PROVED]  formula_pe_ge_map_pe  — P_e^{MAP} ≤ P_e^{formula}
  4. [PROVED]  gibbs_inequality      — H(p) ≤ -∑ p·log q (KL divergence ≥ 0)
  5. [PROVED]  fano_per_element      — per-y Fano via Gibbs with bimodal reference
  6. [SORRY]   fano_map_bound        — H(X|Y) ≤ h(P_e^{MAP}) + P_e^{MAP}·log(n-1)
  7. [SORRY]   fano_func_mono        — monotonicity of h(p) + p·log(c)
  8. Main:     fano_theorem

  Claude Shannon (1948) — Fano (1952)
  Sorries: 3
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

/-- Gibbs inequality: H(p) ≤ -∑ p(x)·log q(x) for any distribution q.
    Proof: KL divergence non-negativity via log x ≤ x - 1. -/
lemma gibbs_inequality {α : Type*} [Fintype α] [DecidableEq α]
    {p q : α → ℝ} (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 < q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) :
    shannonEntropy p ≤ -∑ x, p x * Real.log (q x) := by
  -- shannonEntropy p = -∑ p·log p (since 0·log 0 = 0 in Lean)
  have hse : shannonEntropy p = -∑ x : α, p x * Real.log (p x) := by
    unfold shannonEntropy
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · simp [h]
    · rfl
  rw [hse]
  -- KL(p||q) = ∑ p·log(p/q) = ∑ p·log p - ∑ p·log q ≥ 0
  have hkl_eq : ∑ x : α, p x * Real.log (p x / q x) =
      ∑ x : α, p x * Real.log (p x) - ∑ x : α, p x * Real.log (q x) := by
    simp only [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rcases (hp x).eq_or_lt with h | hpx
    · simp [h.symm]
    · rw [Real.log_div (ne_of_gt hpx) (ne_of_gt (hq x))]; ring
  have hkl_nn : 0 ≤ ∑ x : α, p x * Real.log (p x / q x) := by
    have hterm : ∀ x : α, p x - q x ≤ p x * Real.log (p x / q x) := by
      intro x
      rcases (hp x).eq_or_lt with h | hpx
      · simp [h.symm]; linarith [hq x]
      · have hqx := hq x
        have hlogqp : Real.log (q x / p x) ≤ q x / p x - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hqx hpx)
        have hlogpq : Real.log (p x / q x) = -Real.log (q x / p x) := by
          rw [Real.log_div (ne_of_gt hpx) (ne_of_gt hqx),
              Real.log_div (ne_of_gt hqx) (ne_of_gt hpx)]; ring
        rw [hlogpq]
        have hfield : p x * (q x / p x - 1) = q x - p x := by field_simp
        nlinarith [mul_le_mul_of_nonneg_left hlogqp (le_of_lt hpx)]
    calc (0 : ℝ) = ∑ x : α, (p x - q x) := by
          simp [Finset.sum_sub_distrib, hpsum, hqsum]
      _ ≤ ∑ x : α, p x * Real.log (p x / q x) :=
          Finset.sum_le_sum (fun x _ => hterm x)
  linarith [hkl_eq]

-- ============================================================
-- Section 2: MAP Error Probability
-- ============================================================

/-- The maximum probability in a distribution on a finite nonempty type. -/
noncomputable abbrev maxProb {α : Type*} [Fintype α] [Nonempty α] (q : α → ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty q

/-- The MAP error probability: 1 - (sum of MAP-correct probabilities).
    P_e^{MAP} = 1 - ∑_y max_x pXY(x,y) -/
noncomputable def mapErrorProb {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (pXY : α × β → ℝ) : ℝ :=
  1 - ∑ y : β, maxProb (fun x => pXY (x, y))

-- ============================================================
-- Section 3: Core Algebraic Lemma (PROVED)
-- ============================================================

/-- **[PROVED]**: For any probability distribution q, ∑_x q(x)² ≤ max_x q(x). -/
theorem sum_sq_le_max {α : Type*} [Fintype α] [Nonempty α]
    {q : α → ℝ} (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1) :
    ∑ x, q x ^ 2 ≤ maxProb q := by
  unfold maxProb
  have hle : ∀ x : α, q x ≤ Finset.sup' Finset.univ Finset.univ_nonempty q :=
    fun x => Finset.le_sup' _ (Finset.mem_univ x)
  calc ∑ x : α, q x ^ 2
      ≤ ∑ x : α, Finset.sup' Finset.univ Finset.univ_nonempty q * q x := by
        apply Finset.sum_le_sum; intro x _
        rw [sq]; exact mul_le_mul_of_nonneg_right (hle x) (hq x)
    _ = Finset.sup' Finset.univ Finset.univ_nonempty q * ∑ x : α, q x := by
        rw [← Finset.mul_sum]
    _ = Finset.sup' Finset.univ Finset.univ_nonempty q := by
        rw [hqsum, mul_one]

-- ============================================================
-- Section 4: Slice-wise Bound (PROVED)
-- ============================================================

/-- **[PROVED]**: For each y, ∑_x pXY(x,y)² / P(Y=y) ≤ max_x pXY(x,y) -/
lemma slice_sq_le_max {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    {pXY : α × β → ℝ} (hp : ∀ x, 0 ≤ pXY x) (y : β) :
    ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y)) ≤
      maxProb (fun x => pXY (x, y)) := by
  set s := ∑ x' : α, pXY (x', y) with hs_def
  have hs_nn : 0 ≤ s := Finset.sum_nonneg (fun x _ => hp (x, y))
  have hM_le : ∀ x : α, pXY (x, y) ≤ maxProb (fun x => pXY (x, y)) := by
    intro x
    show pXY (x, y) ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun x' => pXY (x', y))
    exact Finset.le_sup' (fun x' => pXY (x', y)) (Finset.mem_univ x)
  -- Core: ∑ pXY² ≤ M * s
  have hcore : ∑ x : α, pXY (x, y) ^ 2 ≤ maxProb (fun x => pXY (x, y)) * s := by
    calc ∑ x : α, pXY (x, y) ^ 2
        ≤ ∑ x : α, maxProb (fun x => pXY (x, y)) * pXY (x, y) := by
          apply Finset.sum_le_sum; intro x _
          rw [sq]; exact mul_le_mul_of_nonneg_right (hM_le x) (hp (x, y))
      _ = maxProb (fun x => pXY (x, y)) * s := by rw [← Finset.mul_sum]
  -- Rewrite sum of quotients as quotient of sum
  rw [← Finset.sum_div]
  rcases lt_or_eq_of_le hs_nn with hs_pos | hs_zero
  · -- Prove a/s ≤ M from a ≤ M*s via a/s = a*s⁻¹ ≤ M*s*s⁻¹ = M
    have hinv : 0 < s⁻¹ := inv_pos.mpr hs_pos
    rw [div_eq_mul_inv]
    calc (∑ x : α, pXY (x, y) ^ 2) * s⁻¹
        ≤ maxProb (fun x => pXY (x, y)) * s * s⁻¹ :=
          mul_le_mul_of_nonneg_right hcore (le_of_lt hinv)
      _ = maxProb (fun x => pXY (x, y)) := by
          rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hs_pos), mul_one]
  · -- s = 0: all pXY(x,y) = 0, both sides are 0
    have hs_eq : s = 0 := hs_zero.symm
    have hzero : ∀ x : α, pXY (x, y) = 0 :=
      fun x => (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hp (x, y))).mp hs_eq
        x (Finset.mem_univ x)
    have hRHS : maxProb (fun x => pXY (x, y)) = 0 :=
      le_antisymm (Finset.sup'_le _ _ (fun x _ => le_of_eq (hzero x)))
                  (le_trans (hp (Classical.arbitrary α, y))
                  (Finset.le_sup' (fun x => pXY (x, y)) (Finset.mem_univ (Classical.arbitrary α))))
    simp [hzero, hRHS]

-- ============================================================
-- Section 5: Formula P_e ≥ MAP P_e (PROVED)
-- ============================================================

/-- **[PROVED]**: mapErrorProb pXY ≤ 1 - ∑_y ∑_x pXY(x,y)² / P(Y=y) -/
theorem formula_pe_ge_map_pe {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    {pXY : α × β → ℝ} (hp : ∀ x, 0 ≤ pXY x) :
    mapErrorProb pXY ≤
      1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y)) := by
  unfold mapErrorProb
  linarith [Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => slice_sq_le_max hp y)]

-- ============================================================
-- Section 6: Per-Element Fano Bound (PROVED)
-- ============================================================

/-- **[PROVED]**: For any probability distribution q on α with |α| ≥ 2:
      H(q) ≤ h(1 - max q) + (1 - max q) · log(|α| - 1)

    Case 1 (max q = 1): q is degenerate, H(q) = 0.
    Case 2 (max q < 1): apply Gibbs with bimodal reference
      Q(x*) = max q,  Q(x) = (1-max q)/(n-1) for x ≠ x*. -/
lemma fano_per_element {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (hn : 1 < Fintype.card α)
    {q : α → ℝ} (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1) :
    shannonEntropy q ≤
      h (1 - maxProb q) + (1 - maxProb q) * Real.log ((Fintype.card α : ℝ) - 1) := by
  set p_star := maxProb q with hp_star_def
  set n := Fintype.card α with hn_def
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpstar_le1 : p_star ≤ 1 := by
    show Finset.sup' Finset.univ Finset.univ_nonempty q ≤ 1
    exact (Finset.sup'_le _ _ (fun x _ =>
      Finset.single_le_sum (fun x _ => hq x) (Finset.mem_univ x))).trans_eq hqsum
  have hpstar_nn : 0 ≤ p_star := by
    show 0 ≤ Finset.sup' Finset.univ Finset.univ_nonempty q
    exact le_trans (hq (Classical.arbitrary α)) (Finset.le_sup' q (Finset.mem_univ _))
  obtain ⟨xstar, _, hxstar_max⟩ :=
    Finset.exists_max_image Finset.univ q Finset.univ_nonempty
  have hxstar_eq : q xstar = p_star := by
    show q xstar = Finset.sup' Finset.univ Finset.univ_nonempty q
    apply le_antisymm
    · exact Finset.le_sup' q (Finset.mem_univ xstar)
    · exact Finset.sup'_le _ _ (fun y hy => hxstar_max y hy)
  have hsum_erase : ∑ x ∈ Finset.univ.erase xstar, q x = 1 - p_star := by
    have key := Finset.add_sum_erase Finset.univ q (Finset.mem_univ xstar)
    rw [hxstar_eq] at key; linarith [hqsum]
  -- Case split: degenerate vs proper
  rcases lt_or_eq_of_le hpstar_le1 with hpstar_lt1 | h1
  swap
  · -- p* = 1: H(q) = 0
    rw [← h1, sub_self, h_zero, zero_mul, add_zero]
    have hne_sum : ∑ y ∈ Finset.univ.erase xstar, q y = 0 := by
      have : 1 - p_star = 0 := by rw [h1]; ring
      linarith [hsum_erase]
    have hothers : ∀ x : α, x ≠ xstar → q x = 0 := fun x hne =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hq y)).mp hne_sum x
        (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ x⟩)
    have hse_zero : shannonEntropy q = 0 := by
      unfold shannonEntropy; simp only [neg_eq_zero]
      apply Finset.sum_eq_zero; intro x _
      by_cases hxeq : x = xstar
      · rw [hxeq]
        have : q xstar = 1 := hxstar_eq.trans h1
        simp [this, Real.log_one]
      · simp [hothers x hxeq]
    linarith [hse_zero]
  · -- p* < 1: apply Gibbs with bimodal reference Q
    have hpstar_pos : 0 < p_star := by
      by_contra hlt; push_neg at hlt
      have hzeq : p_star = 0 := le_antisymm hlt hpstar_nn
      have hall_zero : ∀ x : α, q x = 0 := fun x =>
        le_antisymm (hzeq ▸ Finset.le_sup' q (Finset.mem_univ x)) (hq x)
      have : ∑ x : α, q x = 0 := Finset.sum_eq_zero (fun x _ => hall_zero x)
      linarith [hqsum]
    let Q : α → ℝ := fun x =>
      if x = xstar then p_star else (1 - p_star) / ((n : ℝ) - 1)
    have hQ_pos : ∀ x : α, 0 < Q x := by
      intro x
      show 0 < if x = xstar then p_star else (1 - p_star) / ((n : ℝ) - 1)
      split_ifs
      · exact hpstar_pos
      · exact div_pos (by linarith) hn1_pos
    have hQ_sum : ∑ x : α, Q x = 1 := by
      have hn1_ne : (n : ℝ) - 1 ≠ 0 := ne_of_gt hn1_pos
      have hxstar_val : Q xstar = p_star := if_pos rfl
      -- Sum over the erase
      have hQ_erase_sum : ∑ x ∈ Finset.univ.erase xstar, Q x = 1 - p_star := by
        have hconst : ∀ x ∈ Finset.univ.erase xstar,
            Q x = (1 - p_star) / ((n : ℝ) - 1) :=
          fun x hx => if_neg (Finset.mem_erase.mp hx).1
        have hcard : ((Finset.univ.erase xstar).card : ℝ) = (n : ℝ) - 1 := by
          have hn1 : 1 ≤ n := le_of_lt hn
          have hc : (Finset.univ.erase xstar).card = n - 1 := by
            have h1 : (Finset.univ : Finset α).card = n := hn_def.symm
            have h2 := Finset.card_erase_of_mem (Finset.mem_univ xstar)
            omega
          rw [hc, Nat.cast_sub hn1, Nat.cast_one]
        calc ∑ x ∈ Finset.univ.erase xstar, Q x
            = ∑ x ∈ Finset.univ.erase xstar, (1 - p_star) / ((n : ℝ) - 1) :=
              Finset.sum_congr rfl hconst
          _ = ((Finset.univ.erase xstar).card : ℝ) * ((1 - p_star) / ((n : ℝ) - 1)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = ((n : ℝ) - 1) * ((1 - p_star) / ((n : ℝ) - 1)) := by rw [hcard]
          _ = 1 - p_star := by field_simp [hn1_ne]
      -- Combine
      have key := Finset.add_sum_erase Finset.univ Q (Finset.mem_univ xstar)
      simp only [hxstar_val, hQ_erase_sum] at key; linarith
    -- Gibbs: H(q) ≤ -∑ q·log Q
    have hgibbs := gibbs_inequality hq hQ_pos hqsum hQ_sum
    -- Compute: -∑ q·log Q = h(1-p*) + (1-p*)·log(n-1)
    have hcross : -∑ x : α, q x * Real.log (Q x) =
        h (1 - p_star) + (1 - p_star) * Real.log (↑n - 1) := by
      have hQ_xstar : Q xstar = p_star := if_pos rfl
      have hQ_erase : ∀ x ∈ Finset.univ.erase xstar, Q x = (1 - p_star) / ((n : ℝ) - 1) :=
        fun x hx => if_neg (Finset.mem_erase.mp hx).1
      have hsum_split : ∑ x : α, q x * Real.log (Q x) =
          p_star * Real.log p_star +
          (1 - p_star) * Real.log ((1 - p_star) / ((n : ℝ) - 1)) := by
        rw [← Finset.add_sum_erase Finset.univ (fun x => q x * Real.log (Q x))
              (Finset.mem_univ xstar)]
        simp only [hQ_xstar, hxstar_eq]
        congr 1
        calc ∑ x ∈ Finset.univ.erase xstar, q x * Real.log (Q x)
            = ∑ x ∈ Finset.univ.erase xstar, q x * Real.log ((1-p_star)/((n:ℝ)-1)) :=
              Finset.sum_congr rfl (fun x hx => by rw [hQ_erase x hx])
          _ = (∑ x ∈ Finset.univ.erase xstar, q x) * Real.log ((1-p_star)/((n:ℝ)-1)) := by
              rw [← Finset.sum_mul]
          _ = (1 - p_star) * Real.log ((1-p_star)/((n:ℝ)-1)) := by rw [hsum_erase]
      rw [hsum_split, Real.log_div (ne_of_gt (by linarith)) (ne_of_gt hn1_pos)]
      simp only [h, sub_sub_cancel]; ring
    rw [← hcross]; exact hgibbs

-- ============================================================
-- Section 7: Conditional Entropy Fano Bound — MAP Version (SORRY)
-- ============================================================

/-- **[SORRY]**: H(X|Y) ≤ h(P_e^{MAP}) + P_e^{MAP} · log(|X| - 1)

    Proof sketch: Decompose H(X|Y) = ∑_y P(Y=y)·H(X|Y=y), apply
    fano_per_element per slice, then Jensen for concave h. -/
lemma fano_map_bound {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hn : 1 < Fintype.card α)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    conditionalEntropy pXY ≤
      h (mapErrorProb pXY) +
      mapErrorProb pXY * Real.log ((Fintype.card α : ℝ) - 1) := by
  sorry

-- ============================================================
-- Section 8: Monotonicity of h(p) + p·log(c) (SORRY)
-- ============================================================

/-- **[SORRY]**: For c ≥ 1, f(p) = h(p) + p·log c is non-decreasing on [0, c/(1+c)]. -/
lemma fano_func_mono {c : ℝ} (hc : 1 ≤ c) {p₁ p₂ : ℝ}
    (hp₁ : 0 ≤ p₁) (hp₂ : p₂ ≤ c / (1 + c)) (hpp : p₁ ≤ p₂) :
    h p₁ + p₁ * Real.log c ≤ h p₂ + p₂ * Real.log c := by
  sorry

-- ============================================================
-- Section 9: Main Theorem
-- ============================================================

/-- **Fano's Inequality**: H(X|Y) ≤ h(P_e) + P_e · log(|X| - 1)
    where P_e = 1 - ∑_y ∑_x P(X=x,Y=y)² / P(Y=y). -/
theorem fano_theorem {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [Nonempty α]
    (hn : 1 < Fintype.card α)
    (pXY : α × β → ℝ) (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    let P_e := 1 - ∑ y : β, ∑ x : α, pXY (x, y) ^ 2 / (∑ x' : α, pXY (x', y))
    conditionalEntropy pXY ≤
      h P_e + P_e * Real.log ((Fintype.card α : ℝ) - 1) := by
  intro P_e
  have hc : (1 : ℝ) ≤ (Fintype.card α : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hn
    linarith
  -- MAP P_e ≥ 0: max ≤ sum for each slice, then Fubini
  have hmap_nn : 0 ≤ mapErrorProb pXY := by
    unfold mapErrorProb
    have hle : ∀ y : β, maxProb (fun x => pXY (x, y)) ≤ ∑ x : α, pXY (x, y) :=
      fun y => Finset.sup'_le _ _ (fun x _ =>
        Finset.single_le_sum (fun x _ => hp (x, y)) (Finset.mem_univ x))
    have hfub : ∑ y : β, ∑ x : α, pXY (x, y) = 1 := by
      have h := hsum
      rw [Fintype.sum_prod_type] at h
      rwa [← Finset.sum_comm] at h
    have hbound : ∑ y : β, maxProb (fun x => pXY (x, y)) ≤ 1 :=
      (Finset.sum_le_sum (fun y _ => hle y)).trans_eq hfub
    linarith
  have hpe_ineq : mapErrorProb pXY ≤ P_e := formula_pe_ge_map_pe hp
  have hpe_bound : P_e ≤ ((Fintype.card α : ℝ) - 1) / (1 + ((Fintype.card α : ℝ) - 1)) := by
    sorry
  have hmap_fano := fano_map_bound hn pXY hp hsum
  have hmono := fano_func_mono hc hmap_nn hpe_bound hpe_ineq
  linarith

end FanoInequality

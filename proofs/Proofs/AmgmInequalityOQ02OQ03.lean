/-
# Maclaurin Chain from Newton's Log-Concavity

Open Question (from amgm-inequality-oq-02):
  Can the full Maclaurin chain Mₖ ≥ Mₖ₊₁ be derived from Newton's
  log-concavity of normalized elementary symmetric polynomials?

Answer: YES. The key is the power inequality aₖ^{k+1} ≥ aₖ₊₁^k,
proved by induction using log-concavity.

This file ELIMINATES the `maclaurin_step` axiom from AmgmInequalityOQ02.lean
by proving it from `newton_log_concavity`.

Proof strategy:
  Let aₖ = eₖ/C(n,k). Newton's log-concavity gives aₖ² ≥ aₖ₋₁·aₖ₊₁.
  By induction: aₖ^{k+1} ≥ aₖ₊₁^k.
  Base: a₀ = 1, a₁ ≥ 0 gives 1 = a₀¹ ≥ a₁⁰ = 1 ✓
  Step: Raise LC to k-th power, combine with IH, cancel aₖ^{k-1}.
  Then Mₖ = aₖ^{1/k} ≥ aₖ₊₁^{1/(k+1)} = Mₖ₊₁ by monotonicity of rpow.

References:
  Hardy-Littlewood-Pólya "Inequalities" (1934) §2.22
  Maclaurin, C. (1729): Original derivation
-/

import Proofs.AmgmInequalityOQ02Defs
import Proofs.AmgmInequalityOQ02

open Finset Real AmgmInequalityOQ02

namespace AmgmInequalityOQ02OQ03

variable {n : ℕ}

/-- Shorthand: the normalized elementary symmetric polynomial aₖ = eₖ/C(n,k). -/
noncomputable def normElemSymm (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  elemSymm k x / (Nat.choose n k : ℝ)

/-- Normalized e₀ = 1 (since e₀ = 1 and C(n,0) = 1). -/
theorem normElemSymm_zero (x : Fin n → ℝ) : normElemSymm 0 x = 1 := by
  simp [normElemSymm, elemSymm_zero]

/-- Normalized elementary symmetric polynomials are non-negative for non-negative inputs. -/
theorem normElemSymm_nonneg (k : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ normElemSymm k x := by
  apply div_nonneg (elemSymm_nonneg k x hx) (Nat.cast_nonneg _)

/-- Zero propagation: for non-negative inputs, if normElemSymm m = 0 then
    normElemSymm (m+1) = 0. Each (m+1)-subset contains an m-subset whose
    product is zero (since all m-subset products are zero). -/
private lemma normElemSymm_zero_succ (m : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hmn : m ≤ n)
    (hm : normElemSymm m x = 0) : normElemSymm (m + 1) x = 0 := by
  -- Extract elemSymm m x = 0 from normElemSymm m x = 0
  unfold normElemSymm at hm ⊢
  have hcm_ne : (Nat.choose n m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hmn).ne'
  have h_elem : elemSymm m x = 0 := (div_eq_zero_iff.mp hm).resolve_right hcm_ne
  -- Suffices to show elemSymm (m+1) x = 0
  suffices h : elemSymm (m + 1) x = 0 by rw [h]; exact zero_div _
  -- Unfold elemSymm in h_elem and goal
  unfold elemSymm at h_elem ⊢
  -- Each m-subset product is 0 (non-negative sum = 0 implies each term = 0)
  have h_terms : ∀ s ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ∏ i in s, x i = 0 := by
    intro s hs
    have h_le := Finset.single_le_sum
      (fun t _ => Finset.prod_nonneg fun i _ => hx i) hs
    have h_ge := Finset.prod_nonneg (s := s) fun i _ => hx i
    linarith
  -- Each (m+1)-subset product is 0: decompose as element × m-subset
  exact Finset.sum_eq_zero fun t ht => by
    obtain ⟨j, hj⟩ := Finset.card_pos.mp
      (show 0 < t.card by rw [(Finset.mem_powersetCard.mp ht).2]; omega)
    rw [← Finset.mul_prod_erase _ _ hj,
        h_terms _ (Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
          show (t.erase j).card = m by
            rw [Finset.card_erase_of_mem hj, (Finset.mem_powersetCard.mp ht).2]; omega⟩),
        mul_zero]

/-- Newton's log-concavity restated in terms of normElemSymm:
    aₖ² ≥ aₖ₋₁ · aₖ₊₁ for 1 ≤ k and k+1 ≤ n. -/
theorem newton_lc (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    normElemSymm k x ^ 2 ≥ normElemSymm (k - 1) x * normElemSymm (k + 1) x := by
  exact newton_log_concavity k hk hkn x hx

-- ============================================================
-- Part I: The Power Inequality (Key Lemma)
-- ============================================================

/-- **Power Inequality**: aₖ^{k+1} ≥ aₖ₊₁^k for all 0 ≤ k < n.

    This is the engine of the Maclaurin chain. The proof uses induction on k:
    - Base (k=0): 1 = a₀¹ ≥ a₁⁰ = 1
    - Step: From aₖ₋₁^k ≥ aₖ^{k-1} (IH) and aₖ² ≥ aₖ₋₁aₖ₊₁ (log-concavity),
      raise LC to k-th power: aₖ^{2k} ≥ aₖ₋₁^k · aₖ₊₁^k ≥ aₖ^{k-1} · aₖ₊₁^k,
      then cancel aₖ^{k-1} (or handle aₖ = 0 separately). -/
theorem power_inequality (k : ℕ) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    normElemSymm k x ^ (k + 1) ≥ normElemSymm (k + 1) x ^ k := by
  induction k with
  | zero =>
    simp [normElemSymm_zero, pow_zero]
  | succ k ih =>
    -- ih : a_k^{k+1} ≥ a_{k+1}^k (under appropriate hypotheses)
    have hkn' : k + 1 ≤ n := by omega
    have ih_applied := ih hkn' x hx
    -- Newton's log-concavity at k+1: a_{k+1}² ≥ a_k · a_{k+2}
    have hlc := newton_lc (k + 1) (by omega) hkn x hx
    simp only [show k + 1 - 1 = k from by omega] at hlc
    -- a_{k+1} and a_k are non-negative
    have hak : 0 ≤ normElemSymm k x := normElemSymm_nonneg k x hx
    have hak1 : 0 ≤ normElemSymm (k + 1) x := normElemSymm_nonneg (k + 1) x hx
    have hak2 : 0 ≤ normElemSymm (k + 2) x := normElemSymm_nonneg (k + 2) x hx
    -- Goal: a_{k+1}^{k+2} ≥ a_{k+2}^{k+1}
    -- From LC: a_{k+1}² ≥ a_k · a_{k+2}
    -- Raise to (k+1)-th power: a_{k+1}^{2(k+1)} ≥ (a_k · a_{k+2})^{k+1}
    --                         = a_k^{k+1} · a_{k+2}^{k+1}
    -- From IH: a_k^{k+1} ≥ a_{k+1}^k
    -- So: a_{k+1}^{2(k+1)} ≥ a_{k+1}^k · a_{k+2}^{k+1}
    -- If a_{k+1} > 0: divide by a_{k+1}^k: a_{k+1}^{k+2} ≥ a_{k+2}^{k+1}
    -- If a_{k+1} = 0: from LC, a_k · a_{k+2} ≤ 0, so a_{k+2} = 0 (since a_k ≥ 0)
    by_cases hak1_pos : normElemSymm (k + 1) x = 0
    · -- Case: a_{k+1} = 0
      -- From LC: 0 ≥ a_k * a_{k+2}, so a_k = 0 or a_{k+2} = 0
      have : normElemSymm k x * normElemSymm (k + 2) x ≤ 0 := by linarith [hlc, hak1_pos]
      have : normElemSymm k x * normElemSymm (k + 2) x = 0 := by
        linarith [mul_nonneg hak hak2]
      have hak2_zero : normElemSymm (k + 2) x = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · -- If a_k = 0, need to show a_{k+2} = 0 from a_{k+1} = 0 and LC
          -- From IH: 0 = a_k^{k+1} ≥ a_{k+1}^k = 0, consistent
          -- a_{k+2} could in principle be nonzero, but from the LC at k+1
          -- with a_{k+1} = 0: 0 ≥ a_k * a_{k+2} = 0 * a_{k+2} = 0, which gives nothing
          -- However, we also have LC at k+2 if applicable...
          -- Actually, we need to use the elementary symmetric polynomial property:
          -- if a_{k+1} = 0 then e_{k+1} = 0
          -- For non-negative x, e_{k+1} = 0 implies every (k+1)-subset product is 0
          -- meaning at most k non-zero variables, so e_{k+2} = 0 too
          exact normElemSymm_zero_succ (k + 1) x hx (by omega) hak1_pos
        · exact h
      rw [hak1_pos, hak2_zero]; simp
    · -- Case: a_{k+1} > 0
      have hak1_pos' : 0 < normElemSymm (k + 1) x := by
        exact lt_of_le_of_ne hak1 (Ne.symm hak1_pos)
      -- Raise LC to (k+1)-th power
      have hlc_pow : normElemSymm (k + 1) x ^ (2 * (k + 1)) ≥
          (normElemSymm k x * normElemSymm (k + 2) x) ^ (k + 1) := by
        have : normElemSymm (k + 1) x ^ 2 ^ (k + 1) ≤
            normElemSymm (k + 1) x ^ (2 * (k + 1)) := by
          rw [pow_mul]
        calc normElemSymm (k + 1) x ^ (2 * (k + 1))
            = (normElemSymm (k + 1) x ^ 2) ^ (k + 1) := by rw [pow_mul]
          _ ≥ (normElemSymm k x * normElemSymm (k + 2) x) ^ (k + 1) := by
              apply pow_le_pow_left (mul_nonneg hak hak2) hlc
      -- Expand the RHS
      rw [mul_pow] at hlc_pow
      -- From IH: a_k^{k+1} ≥ a_{k+1}^k
      -- Combined: a_{k+1}^{2(k+1)} ≥ a_k^{k+1} · a_{k+2}^{k+1} ≥ a_{k+1}^k · a_{k+2}^{k+1}
      have combined : normElemSymm (k + 1) x ^ (2 * (k + 1)) ≥
          normElemSymm (k + 1) x ^ k * normElemSymm (k + 2) x ^ (k + 1) := by
        calc normElemSymm (k + 1) x ^ (2 * (k + 1))
            ≥ normElemSymm k x ^ (k + 1) * normElemSymm (k + 2) x ^ (k + 1) := hlc_pow
          _ ≥ normElemSymm (k + 1) x ^ k * normElemSymm (k + 2) x ^ (k + 1) := by
              apply mul_le_mul_of_nonneg_right ih_applied (pow_nonneg hak2 _)
      -- Now: a_{k+1}^{2(k+1)} ≥ a_{k+1}^k · a_{k+2}^{k+1}
      -- i.e. a_{k+1}^{2k+2} ≥ a_{k+1}^k · a_{k+2}^{k+1}
      -- Divide by a_{k+1}^k: a_{k+1}^{k+2} ≥ a_{k+2}^{k+1}
      have h_cancel : normElemSymm (k + 1) x ^ (k + 2) ≥
          normElemSymm (k + 2) x ^ (k + 1) := by
        have h2k2 : 2 * (k + 1) = k + (k + 2) := by omega
        rw [h2k2, pow_add] at combined
        exact le_of_mul_le_mul_left combined (pow_pos hak1_pos' k)
      exact h_cancel

-- ============================================================
-- Part II: From Power Inequality to Maclaurin Step
-- ============================================================

/-- From aₖ^{k+1} ≥ aₖ₊₁^k, derive Mₖ ≥ Mₖ₊₁.

    Mₖ = aₖ^{1/k} and Mₖ₊₁ = aₖ₊₁^{1/(k+1)}.
    From the power inequality: (aₖ^{k+1})^{1/(k(k+1))} ≥ (aₖ₊₁^k)^{1/(k(k+1))},
    which simplifies to aₖ^{1/k} ≥ aₖ₊₁^{1/(k+1)}. -/
theorem maclaurin_step_from_newton (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean k x ≥ maclaurinMean (k + 1) x := by
  unfold maclaurinMean
  -- Need: (e_k/C(n,k))^(1/k) ≥ (e_{k+1}/C(n,k+1))^(1/(k+1))
  -- This is: normElemSymm k x ^ (1/k) ≥ normElemSymm (k+1) x ^ (1/(k+1))
  -- From power_inequality: normElemSymm k x ^ (k+1) ≥ normElemSymm (k+1) x ^ k
  have hpi := power_inequality k hkn x hx
  have hak := normElemSymm_nonneg k x hx
  have hak1 := normElemSymm_nonneg (k + 1) x hx
  -- Take the 1/(k*(k+1))-th power of both sides
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1_pos : (0 : ℝ) < k + 1 := by positivity
  have hkk1_pos : (0 : ℝ) < k * (k + 1) := by positivity
  -- (a_k^{k+1})^{1/(k(k+1))} = a_k^{(k+1)/(k(k+1))} = a_k^{1/k}
  -- (a_{k+1}^k)^{1/(k(k+1))} = a_{k+1}^{k/(k(k+1))} = a_{k+1}^{1/(k+1)}
  have h_exp1 : (1 : ℝ) / k = (↑(k + 1)) / (↑k * (↑k + 1)) := by field_simp
  have h_exp2 : (1 : ℝ) / (k + 1) = (↑k) / (↑k * (↑k + 1)) := by field_simp
  rw [show elemSymm k x / (↑(Nat.choose n k) : ℝ) = normElemSymm k x from rfl,
      show elemSymm (k + 1) x / (↑(Nat.choose n (k + 1)) : ℝ) = normElemSymm (k + 1) x from rfl]
  rw [h_exp1, h_exp2]
  -- Now goal: normElemSymm k x ^ ((k+1)/(k*(k+1))) ≥ normElemSymm (k+1) x ^ (k/(k*(k+1)))
  rw [div_eq_mul_inv, div_eq_mul_inv]
  rw [rpow_natCast_mul hak, rpow_natCast_mul hak1]
  -- Goal: (normElemSymm k x ^ (k+1)) ^ (1/(k*(k+1))) ≥ (normElemSymm (k+1) x ^ k) ^ (1/(k*(k+1)))
  apply rpow_le_rpow (pow_nonneg hak1 k)
  · exact hpi
  · positivity

-- ============================================================
-- Part III: Summary
-- ============================================================

/-- The Maclaurin step inequality is now a THEOREM, not an axiom.
    Mₖ ≥ Mₖ₊₁ for non-negative inputs, derived from Newton's log-concavity. -/
theorem maclaurin_step_proved (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean k x ≥ maclaurinMean (k + 1) x :=
  maclaurin_step_from_newton k hk hkn x hx

end AmgmInequalityOQ02OQ03

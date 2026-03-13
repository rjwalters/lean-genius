/-
  Newton Log-Concavity: Deriving Maclaurin Step
  Research: amgm-inequality-oq-02-oq-02

  Goal: Prove that the `maclaurin_step` axiom follows from `newton_log_concavity`,
  reducing the axiom count in AmgmInequalityOQ02.lean from 2 to 1.

  Main result: `maclaurin_step_derived`
    For non-negative reals x₁, ..., xₙ and 0 < k with k+1 ≤ n:
    Mₖ ≥ Mₖ₊₁ where Mⱼ = (eⱼ/C(n,j))^(1/j)

  Proof strategy:
  1. Log-concavity (aⱼ² ≥ aⱼ₋₁·aⱼ₊₁) implies the power inequality
     aₖ^(k+1) ≥ aₖ₊₁^k (by induction on k)
  2. The power inequality implies the rpow inequality
     aₖ^(1/k) ≥ aₖ₊₁^(1/(k+1)) (by monotonicity of rpow)

  The inductive step uses a division-free argument:
    (aₖ₊₁²)^(k+1) ≥ (aₖ·aₖ₊₂)^(k+1)  [Newton, pow monotone]
    = aₖ^(k+1)·aₖ₊₂^(k+1)              [mul_pow]
    ≥ aₖ₊₁^k·aₖ₊₂^(k+1)               [IH]
    Then cancel aₖ₊₁^k to get aₖ₊₁^(k+2) ≥ aₖ₊₂^(k+1).

  References:
  - Hardy-Littlewood-Pólya "Inequalities" (1934) §2.22
  - AmgmInequalityOQ02.lean (parent formalization)
-/

import Proofs.AmgmInequalityOQ02

open Finset Real

namespace NewtonLogConcavity

/-
## Part I: Structural Properties of Elementary Symmetric Polynomials
-/

/-- For non-negative inputs, if eⱼ(x) = 0, then eₖ(x) = 0 for all k ≥ j.
    This is because eⱼ = 0 means every j-element subset contains a zero xᵢ,
    so fewer than j inputs are non-zero, hence every k-element subset (k ≥ j)
    also contains a zero. -/
theorem elemSymm_zero_implies_higher_zero {n : ℕ} (j : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hj : elemSymm j x = 0) (k : ℕ) (hjk : j ≤ k) :
    elemSymm k x = 0 := by
  simp only [elemSymm] at hj ⊢
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_powersetCard] at ht
  have h_all_zero : ∀ s ∈ (univ : Finset (Fin n)).powersetCard j, ∏ i ∈ s, x i = 0 :=
    Finset.sum_eq_zero_iff_of_nonneg
      (fun s _ => Finset.prod_nonneg fun i _ => hx i) |>.mp hj
  by_contra h_ne
  have h_pos : ∀ i ∈ t, 0 < x i := by
    intro i hi
    rcases lt_or_eq_of_le (hx i) with h | h
    · exact h
    · exact absurd (Finset.prod_eq_zero hi (by linarith)) h_ne
  -- t has k ≥ j elements, so it has a j-element subset
  have hjk' : j ≤ t.card := by omega
  have h_pc_pos : 0 < (t.powersetCard j).card := by
    rw [Finset.card_powersetCard]; exact Nat.choose_pos hjk'
  obtain ⟨s, hs_pc⟩ := Finset.card_pos.mp h_pc_pos
  rw [Finset.mem_powersetCard] at hs_pc
  have hs_sub := hs_pc.1
  have hs_card := hs_pc.2
  have hs_mem : s ∈ (univ : Finset (Fin n)).powersetCard j :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hs_card⟩
  have h_zero := h_all_zero s hs_mem
  have h_prod_pos : 0 < ∏ i ∈ s, x i :=
    Finset.prod_pos fun i hi => h_pos i (hs_sub hi)
  linarith

/-- The normalized elementary symmetric polynomial aⱼ = eⱼ/C(n,j) -/
noncomputable def normESym {n : ℕ} (j : ℕ) (x : Fin n → ℝ) : ℝ :=
  elemSymm j x / (Nat.choose n j : ℝ)

@[simp] lemma normESym_zero {n : ℕ} (x : Fin n → ℝ) : normESym 0 x = 1 := by
  simp [normESym, elemSymm_zero, Nat.choose_zero_right]

lemma normESym_nonneg {n : ℕ} (j : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ normESym j x :=
  div_nonneg (elemSymm_nonneg j x hx) (Nat.cast_nonneg _)

lemma normESym_eq_zero_iff {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    normESym k x = 0 ↔ elemSymm k x = 0 := by
  simp only [normESym]
  constructor
  · intro h
    have hC : (0 : ℝ) < (Nat.choose n k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hk)
    exact div_eq_zero_iff.mp h |>.elim id (fun h => absurd h hC.ne')
  · intro h; simp [h]

lemma normESym_zero_implies_higher_zero {n : ℕ} (j k : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hj : j ≤ n) (hk : k ≤ n) (hjk : j ≤ k)
    (h : normESym j x = 0) : normESym k x = 0 := by
  rw [normESym_eq_zero_iff k hk]
  exact elemSymm_zero_implies_higher_zero j x hx
    ((normESym_eq_zero_iff j hj x).mp h) k hjk

/-
## Part II: Power Inequality from Log-Concavity
-/

lemma normESym_log_concave {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    normESym k x ^ 2 ≥ normESym (k - 1) x * normESym (k + 1) x :=
  newton_log_concavity k hk hkn x hx

/-- Key lemma: log-concavity implies the power inequality aₖ^(k+1) ≥ aₖ₊₁^k.
    Proved by induction on k using a division-free argument. -/
theorem power_ineq_of_log_concave {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    normESym k x ^ (k + 1) ≥ normESym (k + 1) x ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    -- k = m + 1: need normESym (m+1) x ^ (m+2) ≥ normESym (m+2) x ^ (m+1)
    -- Case 1: normESym (m+1) = 0
    by_cases ha_zero : normESym (m + 1) x = 0
    · have hb_zero : normESym (m + 2) x = 0 :=
        normESym_zero_implies_higher_zero (m + 1) (m + 2) x hx
          (by omega) (by omega) (by omega) ha_zero
      simp [ha_zero, hb_zero]
    · -- Case 2: normESym (m+1) > 0
      have ha_nn : 0 ≤ normESym (m + 1) x := normESym_nonneg _ x hx
      have hb_nn : 0 ≤ normESym (m + 2) x := normESym_nonneg _ x hx
      have ha_pos : 0 < normESym (m + 1) x := lt_of_le_of_ne ha_nn (Ne.symm ha_zero)
      cases m with
      | zero =>
        -- k = 1: need normESym 1 x ^ 2 ≥ normESym 2 x ^ 1
        -- From Newton at k=1: normESym 1 x ^ 2 ≥ normESym 0 x * normESym 2 x = normESym 2 x
        have h_newton := normESym_log_concave 1 le_rfl hkn x hx
        simp only [show (1 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
                   normESym_zero] at h_newton
        -- h_newton : normESym 1 x ^ 2 ≥ 1 * normESym 2 x
        simp only [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 = 2 from rfl]
        linarith
      | succ p =>
        -- k = p + 2
        -- a = normESym (p+2) x, b = normESym (p+3) x, a_prev = normESym (p+1) x
        have ha_prev_nn : 0 ≤ normESym (p + 1) x := normESym_nonneg _ x hx
        -- Newton at k = p+2: normESym (p+2) ^ 2 ≥ normESym (p+1) * normESym (p+3)
        have h_newton : normESym (p + 2) x ^ 2 ≥
            normESym (p + 1) x * normESym (p + 3) x := by
          have := normESym_log_concave (p + 2) (by omega) (by omega : p + 2 + 1 ≤ n) x hx
          simp only [show p + 2 - 1 = p + 1 from by omega,
                     show p + 2 + 1 = p + 3 from by omega] at this
          exact this
        -- IH: normESym (p+1) ^ (p+2) ≥ normESym (p+2) ^ (p+1)
        have h_ih : normESym (p + 1) x ^ (p + 2) ≥ normESym (p + 2) x ^ (p + 1) := by
          have := ih (by omega : 1 ≤ p + 1) (by omega : p + 1 + 1 ≤ n)
          simp only [show p + 1 + 1 = p + 2 from by omega] at this
          exact this
        -- Goal after simplification: normESym (p+2) ^ (p+3) ≥ normESym (p+3) ^ (p+2)
        -- The simp normalizes m+1 = p+1+1 = p+2, m+2 = p+3, etc.
        simp only [show p + 1 + 1 = p + 2 from by omega,
                   show p + 1 + 2 = p + 3 from by omega]
        -- Division-free argument:
        -- Step 1: (normESym (p+2))^(2(p+2)) ≥ (normESym (p+1) * normESym (p+3))^(p+2)
        have h1 : (normESym (p + 2) x ^ 2) ^ (p + 2) ≥
            (normESym (p + 1) x * normESym (p + 3) x) ^ (p + 2) :=
          pow_le_pow_left₀ (mul_nonneg ha_prev_nn (normESym_nonneg _ x hx)) h_newton (p + 2)
        rw [← pow_mul, mul_pow] at h1
        -- h1: normESym (p+2) ^ (2*(p+2)) ≥ normESym (p+1) ^ (p+2) * normESym (p+3) ^ (p+2)
        -- Step 2: Combine with IH
        have h2 : normESym (p + 2) x ^ (2 * (p + 2)) ≥
            normESym (p + 2) x ^ (p + 1) * normESym (p + 3) x ^ (p + 2) :=
          calc normESym (p + 2) x ^ (2 * (p + 2))
              ≥ normESym (p + 1) x ^ (p + 2) * normESym (p + 3) x ^ (p + 2) := h1
            _ ≥ normESym (p + 2) x ^ (p + 1) * normESym (p + 3) x ^ (p + 2) :=
                mul_le_mul_of_nonneg_right h_ih (pow_nonneg (normESym_nonneg _ x hx) _)
        -- Step 3: Rewrite 2*(p+2) = (p+1) + (p+3)
        have h_split : 2 * (p + 2) = (p + 1) + (p + 3) := by omega
        rw [h_split, pow_add] at h2
        -- h2: normESym (p+2) ^ (p+1) * normESym (p+2) ^ (p+3) ≥
        --     normESym (p+2) ^ (p+1) * normESym (p+3) ^ (p+2)
        -- Step 4: Cancel normESym (p+2) ^ (p+1) (positive)
        have ha_pow_pos : 0 < normESym (p + 2) x ^ (p + 1) := pow_pos ha_pos _
        exact le_of_mul_le_mul_left (by linarith) ha_pow_pos

/-
## Part III: From Power Inequality to RPow Inequality
-/

/-- If 0 ≤ a, 0 ≤ b, 0 < k, and a^(k+1) ≥ b^k, then a^(1/k) ≥ b^(1/(k+1)).
    Uses the identity a^(1/k) = (a^(k+1))^(1/(k(k+1))) and monotonicity of rpow. -/
theorem rpow_ineq_of_pow_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℕ) (hk : 0 < k) (h : a ^ (k + 1) ≥ b ^ k) :
    a ^ ((1 : ℝ) / k) ≥ b ^ ((1 : ℝ) / (↑k + 1)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1_pos : (0 : ℝ) < ↑k + 1 := by positivity
  have hkk1_pos : (0 : ℝ) < ↑k * (↑k + 1) := by positivity
  -- a^(1/k) = (a^(k+1))^(1/(k*(k+1)))
  have h_a_rw : a ^ ((1 : ℝ) / k) = (a ^ (k + 1 : ℕ)) ^ ((1 : ℝ) / (↑k * (↑k + 1))) := by
    rw [← Real.rpow_natCast a (k + 1), ← Real.rpow_mul ha]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  -- b^(1/(k+1)) = (b^k)^(1/(k*(k+1)))
  have h_b_rw : b ^ ((1 : ℝ) / (↑k + 1)) = (b ^ (k : ℕ)) ^ ((1 : ℝ) / (↑k * (↑k + 1))) := by
    rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb]
    congr 1
    field_simp
  rw [ge_iff_le, h_b_rw, h_a_rw]
  exact Real.rpow_le_rpow (pow_nonneg hb _) h (by positivity)

/-
## Part IV: Main Result
-/

/-- Maclaurin step derived as a theorem from Newton's log-concavity.
    This shows the `maclaurin_step` axiom is redundant given `newton_log_concavity`. -/
theorem maclaurin_step_derived {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean k x ≥ maclaurinMean (k + 1) x := by
  unfold maclaurinMean
  have h_pow := power_ineq_of_log_concave k hk hkn x hx
  -- Apply the rpow conversion
  have h_rpow := rpow_ineq_of_pow_ineq
    (normESym k x) (normESym (k + 1) x)
    (normESym_nonneg k x hx) (normESym_nonneg (k + 1) x hx)
    k hk h_pow
  -- h_rpow uses normESym = elemSymm / C(n,k), same as the goal
  simp only [normESym, ge_iff_le] at h_rpow ⊢
  convert h_rpow using 2 <;> simp [one_div, Nat.cast_add, Nat.cast_one]

/-
## Summary

### Proved (no sorry):
1. `elemSymm_zero_implies_higher_zero` — zero tail property of elem sym polys
2. `normESym_zero_implies_higher_zero` — same for normalized version
3. `power_ineq_of_log_concave` — aₖ^(k+1) ≥ aₖ₊₁^k (key algebraic lemma)
4. `rpow_ineq_of_pow_ineq` — conversion from nat pow to rpow inequality
5. `maclaurin_step_derived` — Mₖ ≥ Mₖ₊₁ as THEOREM (not axiom)

### Significance:
The `maclaurin_step` axiom in AmgmInequalityOQ02.lean is now redundant.
The file's axiom count can be reduced from 2 to 1 (only `newton_log_concavity` remains).

### Remaining axiom:
`newton_log_concavity` — this is a deep classical result requiring
polarization + induction on n (Hardy-Littlewood-Pólya §2.22).
A full formalization would be a major Mathlib contribution.
-/

end NewtonLogConcavity

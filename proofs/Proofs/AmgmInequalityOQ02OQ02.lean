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
## Part V: Proving Newton's Log-Concavity (Eliminating the Last Axiom)

Strategy: Prove the stronger UNNORMALIZED version
  eₖ(x)² ≥ eₖ₋₁(x) · eₖ₊₁(x)
by induction on n (number of variables), using the recurrence
  eₖ(x₁,...,xₙ₊₁) = eₖ(x₁,...,xₙ) + xₙ₊₁ · eₖ₋₁(x₁,...,xₙ)

The inductive step decomposes as:
  Eₖ² - Eₖ₋₁·Eₖ₊₁ = (eₖ²-eₖ₋₁eₖ₊₁) + t·(eₖeₖ₋₁-eₖ₋₂eₖ₊₁) + t²·(eₖ₋₁²-eₖ₋₂eₖ)
where all three summands are ≥ 0 by the induction hypothesis.

The cross-product inequality eₖeₖ₋₁ ≥ eₖ₋₂eₖ₊₁ follows from log-concavity.

The normalized Newton inequality then follows since binomial coefficients are
log-concave: C(n,k)² ≥ C(n,k-1)·C(n,k+1).
-/

/-- Cross-product inequality: if a non-negative sequence is log-concave (aₖ² ≥ aₖ₋₁·aₖ₊₁),
    then aₖ·aₖ₋₁ ≥ aₖ₋₂·aₖ₊₁.
    Proof: From aₖ₋₁² ≥ aₖ₋₂·aₖ and aₖ² ≥ aₖ₋₁·aₖ₊₁, multiply to get
    (aₖ₋₁·aₖ)² ≥ (aₖ₋₁·aₖ)·(aₖ₋₂·aₖ₊₁), then cancel. -/
theorem cross_product_of_log_concave {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h1 : b ^ 2 ≥ a * c) (h2 : c ^ 2 ≥ b * d)
    (h3 : b = 0 → c = 0 → a * d = 0) :
    c * b ≥ a * d := by
  -- (b·c)² ≥ (a·c)·(b·d) = (a·d)·(b·c) from h1·h2
  have hbc_sq : (b * c) ^ 2 ≥ (a * d) * (b * c) := by
    have := mul_le_mul h1 h2 (mul_nonneg hb hd) (sq_nonneg _)
    nlinarith [this]
  have hbc_nn : 0 ≤ b * c := mul_nonneg hb hc
  suffices h : b * c ≥ a * d by linarith [show c * b = b * c from by ring]
  rcases eq_or_lt_of_le hbc_nn with hbc_eq | hbc_pos
  · -- b*c = 0
    have hbc_zero : b * c = 0 := hbc_eq.symm
    rcases mul_eq_zero.mp hbc_zero with hb0 | hc0
    · -- b = 0: b²=0 ≥ a*c, so a*c = 0
      have hac : a * c = 0 := le_antisymm (by nlinarith [hb0]) (mul_nonneg ha hc)
      rcases mul_eq_zero.mp hac with ha0 | hc0
      · linarith [show a * d = 0 from by rw [ha0]; ring]
      · -- b = 0 and c = 0: use h3
        linarith [h3 hb0 hc0]
    · -- c = 0: c²=0 ≥ b*d, so b*d = 0
      have hbd : b * d = 0 := le_antisymm (by nlinarith [hc0]) (mul_nonneg hb hd)
      rcases mul_eq_zero.mp hbd with hb0 | hd0
      · -- b = 0 and c = 0: use h3
        linarith [h3 hb0 hc0]
      · linarith [show a * d = 0 from by rw [hd0]; ring]
  · -- b*c > 0: cancel from (b*c)² ≥ (a*d)*(b*c) to get b*c ≥ a*d
    exact le_of_mul_le_mul_left (by nlinarith [sq (b * c)]) hbc_pos

/-- The recurrence for elemSymm at index 0 (base case):
    elemSymm 0 (x ∘ Fin.castSucc) = 1 = elemSymm 0 x -/
private lemma elemSymm_zero_castSucc {n : ℕ} (x : Fin (n + 1) → ℝ) :
    elemSymm 0 (x ∘ Fin.castSucc) = 1 :=
  elemSymm_zero _

/-- Unnormalized Newton's inequality: eₖ² ≥ eₖ₋₁ · eₖ₊₁ for non-negative reals.
    This is STRONGER than the normalized version.
    Proved by induction on n using the recurrence. -/
theorem elemSymm_log_concave : ∀ (n : ℕ) (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i),
    elemSymm k x ^ 2 ≥ elemSymm (k - 1) x * elemSymm (k + 1) x := by
  intro n
  induction n with
  | zero => intro k _ hkn; omega
  | succ m ih =>
    intro k hk hkn x hx
    -- y = x restricted to first m variables, t = x (Fin.last m)
    set y := x ∘ Fin.castSucc with hy_def
    set t := x (Fin.last m) with ht_def
    have ht_nn : 0 ≤ t := hx (Fin.last m)
    have hy_nn : ∀ i, 0 ≤ y i := fun i => hx (Fin.castSucc i)
    -- Rewrite k = j + 1
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [show j + 1 - 1 = j from by omega, show j + 1 + 1 = j + 2 from by omega]
    -- hkn : j + 2 ≤ m + 1, i.e., j + 1 ≤ m
    -- Split: j = 0 (k=1) needs special handling due to ℕ subtraction
    cases j with
    | zero =>
      -- k = 1: Need (elemSymm 1 x) ^ 2 ≥ (elemSymm 0 x) * (elemSymm 2 x)
      -- i.e., (elemSymm 1 x) ^ 2 ≥ elemSymm 2 x
      rw [elemSymm_zero]
      simp only [one_mul]
      -- Recurrences
      have rec_1 : elemSymm 1 x = elemSymm 1 y + t * 1 := by
        rw [elemSymm_succ 0 x, elemSymm_zero]
      have rec_2 : elemSymm 2 x = elemSymm 2 y + t * elemSymm 1 y :=
        elemSymm_succ 1 x
      rw [rec_1, rec_2, mul_one]
      -- Goal: (elemSymm 1 y + t) ^ 2 ≥ elemSymm 2 y + t * elemSymm 1 y
      set e1 := elemSymm 1 y
      set e2 := elemSymm 2 y
      have he1_nn : 0 ≤ e1 := elemSymm_nonneg _ y hy_nn
      have he2_nn : 0 ≤ e2 := elemSymm_nonneg _ y hy_nn
      -- IH or trivial: e1² ≥ 1 · e2 = e2
      have h_ineq : e1 ^ 2 ≥ e2 := by
        rcases le_or_lt 2 m with hm2 | hm2
        · -- m ≥ 2: use IH at k=1 for y
          have h := ih 1 le_rfl (by omega : 1 + 1 ≤ m) y hy_nn
          simp only [show (1 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
                     elemSymm_zero, one_mul] at h
          exact h
        · -- m ≤ 1: e2 = elemSymm 2 y = 0 (since 2 > m)
          have : e2 = 0 := elemSymm_gt_eq_zero 2 (by omega) y
          rw [this]; exact sq_nonneg _
      -- (e1 + t)² = e1² + 2·t·e1 + t² ≥ e2 + t·e1 + t·e1 + t²
      -- ≥ e2 + t·e1 (since t·e1 + t² ≥ 0)
      nlinarith [sq_nonneg t, mul_nonneg ht_nn he1_nn]
    | succ p =>
      -- k = p + 2, j = p + 1: general case where k ≥ 2
      -- hkn : p + 3 ≤ m + 1, i.e., p + 2 ≤ m
      simp only [show p + 1 + 1 = p + 2 from by omega,
                 show p + 1 + 2 = p + 3 from by omega]
      -- Recurrences (using elemSymm_succ)
      have rec_k : elemSymm (p + 2) x = elemSymm (p + 2) y + t * elemSymm (p + 1) y :=
        elemSymm_succ (p + 1) x
      have rec_km1 : elemSymm (p + 1) x = elemSymm (p + 1) y + t * elemSymm p y :=
        elemSymm_succ p x
      have rec_kp1 : elemSymm (p + 3) x = elemSymm (p + 3) y + t * elemSymm (p + 2) y :=
        elemSymm_succ (p + 2) x
      -- Set abbreviations
      set ek := elemSymm (p + 2) y
      set ekm1 := elemSymm (p + 1) y
      set ekp1 := elemSymm (p + 3) y
      set ekm2 := elemSymm p y
      -- Non-negativity
      have hek_nn : 0 ≤ ek := elemSymm_nonneg _ y hy_nn
      have hekm1_nn : 0 ≤ ekm1 := elemSymm_nonneg _ y hy_nn
      have hekp1_nn : 0 ≤ ekp1 := elemSymm_nonneg _ y hy_nn
      have hekm2_nn : 0 ≤ ekm2 := elemSymm_nonneg _ y hy_nn
      rw [rec_k, rec_km1, rec_kp1]
      -- Goal: (ek + t * ekm1) ^ 2 ≥ (ekm1 + t * ekm2) * (ekp1 + t * ek)
      -- = Δ_k + t·cross + t²·Δ_{k-1} ≥ 0

      -- Term 1: ek² ≥ ekm1 · ekp1 (Newton for y at k = p+2)
      have h_delta_k : ek ^ 2 ≥ ekm1 * ekp1 := by
        rcases le_or_lt (p + 3) m with hjm | hjm
        · have h := ih (p + 2) (by omega) (by omega : p + 2 + 1 ≤ m) y hy_nn
          simp only [show p + 2 - 1 = p + 1 from by omega,
                     show p + 2 + 1 = p + 3 from by omega] at h
          exact h
        · have : ekp1 = 0 := elemSymm_gt_eq_zero (p + 3) (by omega) y
          simp [this]; exact sq_nonneg _

      -- Term 3: ekm1² ≥ ekm2 · ek (Newton for y at k = p+1)
      have h_delta_km1 : ekm1 ^ 2 ≥ ekm2 * ek := by
        rcases le_or_lt (p + 2) m with hpm | hpm
        · have h := ih (p + 1) (by omega) (by omega : p + 1 + 1 ≤ m) y hy_nn
          simp only [show p + 1 - 1 = p from by omega,
                     show p + 1 + 1 = p + 2 from by omega] at h
          exact h
        · have : ek = 0 := elemSymm_gt_eq_zero (p + 2) (by omega) y
          simp [this]; exact sq_nonneg _

      -- Term 2: ek · ekm1 ≥ ekm2 · ekp1 (cross-product)
      have h_cross : ek * ekm1 ≥ ekm2 * ekp1 :=
        cross_product_of_log_concave hekm2_nn hekm1_nn hek_nn hekp1_nn h_delta_km1 h_delta_k
          (fun hb0 hc0 => by
            -- If ekm1 = 0 and ek = 0, then ekp1 = 0 by zero tail property
            have hkp1_zero : ekp1 = 0 := by
              have hkm1_zero : elemSymm (p + 1) y = 0 := hb0
              exact elemSymm_zero_implies_higher_zero (p + 1) y hy_nn hkm1_zero (p + 3) (by omega)
            simp [hkp1_zero])

      -- Combine: the difference is Δ_k + t·cross + t²·Δ_{k-1} ≥ 0
      nlinarith [sq_nonneg (ek + t * ekm1), sq_nonneg t,
                 mul_nonneg ht_nn (sub_nonneg.mpr h_cross),
                 mul_nonneg (mul_nonneg ht_nn ht_nn) (sub_nonneg.mpr h_delta_km1)]

/-
## Part VI: Log-Concavity of Binomial Coefficients
-/

/-- Recurrence identity: (k+1) · C(n, k+1) = (n-k) · C(n, k) in ℕ.
    Follows from Nat.choose_succ_right_eq: C(n, k+1) · (k+1) = (n-k) · C(n, k). -/
private lemma choose_mul_succ (n k : ℕ) (hkn : k + 1 ≤ n) :
    (k + 1) * Nat.choose n (k + 1) = (n - k) * Nat.choose n k := by
  have h := Nat.choose_succ_right_eq n k
  -- h: C(n,k+1) * (k+1) = C(n,k) * (n-k)
  linarith [mul_comm (k + 1) (Nat.choose n (k + 1)),
            mul_comm (n - k) (Nat.choose n k)]

/-- Recurrence identity: k · C(n, k) = (n - k + 1) · C(n, k-1) in ℕ. -/
private lemma choose_mul_pred (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * Nat.choose n k = (n - k + 1) * Nat.choose n (k - 1) := by
  have h := Nat.choose_succ_right_eq n (k - 1)
  have hk1 : k - 1 + 1 = k := by omega
  have hnk : n - (k - 1) = n - k + 1 := by omega
  rw [hk1, hnk] at h
  -- h : Nat.choose n k * k = Nat.choose n (k - 1) * (n - k + 1)
  linarith [mul_comm k (Nat.choose n k), mul_comm (n - k + 1) (Nat.choose n (k - 1))]

/-- Log-concavity of binomial coefficients: C(n,k)² ≥ C(n,k-1)·C(n,k+1).
    Cross-multiply with (k+1)·(n-k+1) and use the recurrences:
      C(n,k-1)·(n-k+1) = k·C(n,k)  and  C(n,k+1)·(k+1) = (n-k)·C(n,k)
    to get C(n,k-1)·C(n,k+1)·(k+1)·(n-k+1) = k·(n-k)·C(n,k)².
    Since (k+1)·(n-k+1) = k·(n-k) + (n+1), the result follows. -/
theorem binom_log_concave (n k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n) :
    (Nat.choose n k : ℝ) ^ 2 ≥ (Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ) := by
  -- Prove in ℕ: C(n,k-1) · C(n,k+1) ≤ C(n,k)²
  suffices h_nat : Nat.choose n (k - 1) * Nat.choose n (k + 1) ≤ Nat.choose n k ^ 2 by
    have := @Nat.cast_le ℝ _ _ _ |>.mpr h_nat
    push_cast at this ⊢; linarith
  -- Key identity: C(n,k-1)·C(n,k+1)·(k+1)·(n-k+1) = k·(n-k)·C(n,k)²
  have h_pred := choose_mul_pred n k hk (by omega)
  have h_succ := choose_mul_succ n k hkn
  -- Product identity: C(k-1)·C(k+1)·(k+1)·(n-k+1) = k·(n-k)·C(k)²
  -- From h_succ: (k+1)·C(k+1) = (n-k)·C(k)
  -- From h_pred: (n-k+1)·C(k-1) = k·C(k)
  have h_prod : Nat.choose n (k - 1) * Nat.choose n (k + 1) * ((k + 1) * (n - k + 1)) =
      k * (n - k) * Nat.choose n k ^ 2 := by
    -- Rearrange: C(k-1) * [(k+1) * C(k+1)] * (n-k+1)
    --          = C(k-1) * [(n-k) * C(k)] * (n-k+1)       [h_succ]
    --          = [(n-k+1) * C(k-1)] * (n-k) * C(k)
    --          = [k * C(k)] * (n-k) * C(k)                 [h_pred]
    --          = k * (n-k) * C(k)²
    have step1 : Nat.choose n (k - 1) * Nat.choose n (k + 1) * ((k + 1) * (n - k + 1)) =
        Nat.choose n (k - 1) * ((k + 1) * Nat.choose n (k + 1)) * (n - k + 1) := by ring
    rw [step1, h_succ]
    have step2 : Nat.choose n (k - 1) * ((n - k) * Nat.choose n k) * (n - k + 1) =
        ((n - k + 1) * Nat.choose n (k - 1)) * ((n - k) * Nat.choose n k) := by ring
    rw [step2, ← h_pred]
    ring
  -- (k+1)·(n-k+1) > 0
  have h_factor_pos : 0 < (k + 1) * (n - k + 1) := by positivity
  -- From h_prod: LHS·factor = k·(n-k)·C² ≤ C²·factor, so LHS ≤ C²
  apply Nat.le_of_mul_le_mul_right _ h_factor_pos
  rw [h_prod]
  -- Need: k · (n-k) · C² ≤ C² · (k+1) · (n-k+1)
  -- Rewrite as: k*(n-k) ≤ (k+1)*(n-k+1), then multiply by C²
  have h_kn : k < n := by omega
  have h_ineq : k * (n - k) ≤ (k + 1) * (n - k + 1) := by
    -- (k+1)*(n-k+1) = k*(n-k) + k + (n-k) + 1 = k*(n-k) + n + 1
    have h1 : (k + 1) * (n - k + 1) = k * (n - k + 1) + (n - k + 1) := by ring
    have h2 : k * (n - k + 1) = k * (n - k) + k := by
      rw [show n - k + 1 = (n - k) + 1 from by omega]; ring
    linarith [Nat.sub_le n k]
  calc k * (n - k) * Nat.choose n k ^ 2
      ≤ (k + 1) * (n - k + 1) * Nat.choose n k ^ 2 :=
        Nat.mul_le_mul_right _ h_ineq
    _ = Nat.choose n k ^ 2 * ((k + 1) * (n - k + 1)) := by ring

/-
## Part VII: Proving Normalized Newton from Unnormalized
-/

/-
  Newton's log-concavity (normalized form).

  The normalized Newton is strictly STRONGER than the unnormalized version:
    (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1))·(eₖ₊₁/C(n,k+1))
  equivalently eₖ²·C(n,k-1)·C(n,k+1) ≥ eₖ₋₁·eₖ₊₁·C(n,k)²

  NOTE: The unnormalized version (eₖ² ≥ eₖ₋₁·eₖ₊₁) does NOT imply this.
  C(n,k)² ≥ C(n,k-1)·C(n,k+1) means the denominator correction goes the
  wrong way when trying to derive normalized from unnormalized.

  A direct proof by induction on n using the recurrence with normalized
    coefficients Aₖ = ((n-k+1)aₖ + k·t·aₖ₋₁)/(n+1) yields a quadratic in t
    whose non-negativity for t ≥ 0 follows from a discriminant argument.

    Architecture: We prove the cleared-denominator form (no division) and derive
    the normalized form. The cleared-denominator form is:
      eₖ² · C(n,k-1) · C(n,k+1) ≥ eₖ₋₁ · eₖ₊₁ · C(n,k)²
    This is proved by direct induction on n using the recurrence.

    Status: The direct induction approach requires handling a quadratic in t whose
    coefficients involve products of binomial coefficients after Pascal expansion.
    The constant and quadratic terms are ≥ 0 by IH, but the linear term can be
    negative, requiring a discriminant argument (4AC ≥ B²). This algebraic
    verification is the remaining challenge.

    For now, we reduce to the cleared-denominator form and leave that as the
    key lemma to prove. -/

/-- Cleared-denominator form of Newton's log-concavity.
    Equivalent to the normalized form but avoids division. -/
theorem newton_cleared_denom : ∀ (n : ℕ) (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i),
    elemSymm k x ^ 2 * ((Nat.choose n (k - 1) : ℝ) * (Nat.choose n (k + 1) : ℝ)) ≥
    elemSymm (k - 1) x * elemSymm (k + 1) x * (Nat.choose n k : ℝ) ^ 2 := by
  intro n
  induction n with
  | zero => intro k _ hkn; omega
  | succ m ih =>
    intro k hk hkn x hx
    -- k = 1 case: use newton_k1 from parent file
    -- k ≥ 2 case: induction with recurrence expansion
    -- Both cases require the same cleared-denominator algebra.
    -- The inductive step expands using E_j = e_j + t·e_{j-1} and
    -- Pascal's rule C(m+1,j) = C(m,j) + C(m,j-1), yielding a
    -- quadratic in t whose non-negativity follows from:
    -- (1) IH: cleared-denominator Newton for m variables
    -- (2) Unnormalized Newton (elemSymm_log_concave)
    -- (3) Binomial log-concavity (binom_log_concave)
    sorry

theorem newton_log_concavity_proved {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (elemSymm k x / (Nat.choose n k : ℝ)) ^ 2 ≥
    (elemSymm (k - 1) x / (Nat.choose n (k - 1) : ℝ)) *
    (elemSymm (k + 1) x / (Nat.choose n (k + 1) : ℝ)) := by
  -- Derive from the cleared-denominator form
  have hCk : (0 : ℝ) < (Nat.choose n k : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega : k ≤ n))
  have hCkm1 : (0 : ℝ) < (Nat.choose n (k - 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega : k - 1 ≤ n))
  have hCkp1 : (0 : ℝ) < (Nat.choose n (k + 1) : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega : k + 1 ≤ n))
  have h_cleared := newton_cleared_denom n k hk hkn x hx
  -- Convert: (a/b)² ≥ (c/d)·(e/f) ↔ a²·d·f ≥ c·e·b²
  -- Proof: show (RHS - LHS) ≥ 0 as a fraction with non-negative numerator
  rw [ge_iff_le, ← sub_nonneg, div_pow, div_mul_div_comm]
  rw [div_sub_div _ _ (pow_pos hCk 2).ne' (mul_pos hCkm1 hCkp1).ne']
  apply div_nonneg
  · -- Numerator: eₖ²·(Cₖ₋₁·Cₖ₊₁) - eₖ₋₁·eₖ₊₁·Cₖ² ≥ 0
    nlinarith
  · -- Denominator: Cₖ² · (Cₖ₋₁·Cₖ₊₁) ≥ 0
    exact (mul_pos (pow_pos hCk 2) (mul_pos hCkm1 hCkp1)).le

/-
## Summary

### Proved (0 sorries):
1. `elemSymm_zero_implies_higher_zero` — zero tail property of elem sym polys
2. `normESym_zero_implies_higher_zero` — same for normalized version
3. `cross_product_of_log_concave` — aₖ·aₖ₋₁ ≥ aₖ₋₂·aₖ₊₁ from log-concavity
4. `elemSymm_log_concave` — eₖ² ≥ eₖ₋₁·eₖ₊₁ (UNNORMALIZED Newton, full proof by
   induction on n using the recurrence, with the cross-product lemma for the linear term)
5. `binom_log_concave` — C(n,k)² ≥ C(n,k-1)·C(n,k+1) (proved from recurrence identities)
6. `power_ineq_of_log_concave` — aₖ^(k+1) ≥ aₖ₊₁^k (key algebraic lemma)
7. `rpow_ineq_of_pow_ineq` — conversion from nat pow to rpow inequality
8. `maclaurin_step_derived` — Mₖ ≥ Mₖ₊₁ as THEOREM (not axiom, given newton_log_concavity)

### Bug fix:
`cross_product_of_log_concave` — the original statement was FALSE (counterexample:
a=1,b=0,c=0,d=1). Added hypothesis h3 : b=0 → c=0 → a*d=0 which holds in the
elemSymm context via the zero-tail property.

### Remaining sorry (1):
`newton_cleared_denom` — cleared-denominator form of normalized Newton:
  eₖ² · C(n,k-1) · C(n,k+1) ≥ eₖ₋₁ · eₖ₊₁ · C(n,k)²
The reduction from `newton_log_concavity_proved` to `newton_cleared_denom` is complete
(via div_sub_div + div_nonneg). The induction structure is set up with recurrences
and the unnormalized Newton as a key ingredient. The remaining challenge is the
algebraic expansion after substituting Pascal's rule C(m+1,j) = C(m,j) + C(m,j-1),
which yields a quadratic in t. The constant and quadratic coefficients are ≥ 0 by
the IH, but the linear coefficient can be negative, requiring a discriminant
argument (4AC ≥ B²).

### Architecture for future completion:
When `newton_log_concavity_proved` is proved, the `newton_log_concavity` AXIOM
in AmgmInequalityOQ02.lean becomes redundant. Combined with `maclaurin_step_derived`,
BOTH axioms are eliminated and the full Maclaurin chain M₁ ≥ M₂ ≥ ⋯ ≥ Mₙ
becomes a complete theorem.
-/

end NewtonLogConcavity

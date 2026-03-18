/-
  Newton Log-Concavity: Complete Proof and Maclaurin Step Derivation
  Research: amgm-inequality-oq-02-oq-02

  This file proves Newton's log-concavity for elementary symmetric polynomials
  and derives both axioms from AmgmInequalityOQ02.lean as theorems:

  Main results (0 axioms, 0 sorries):
  1. `newton_log_concavity_proved` — normalized Newton's inequality
     (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1)) · (eₖ₊₁/C(n,k+1))
  2. `maclaurin_step_derived` — Mₖ ≥ Mₖ₊₁ where Mⱼ = (eⱼ/C(n,j))^(1/j)

  Proof architecture:
  Part I:   Structural properties (zero-tail, normESym basics)
  Part II:  Unnormalized Newton eₖ² ≥ eₖ₋₁·eₖ₊₁ (induction on n)
  Part III: Binomial log-concavity C(n,k)² ≥ C(n,k-1)·C(n,k+1)
  Part IV:  Cleared-denominator inductive step (absorption + discriminant)
  Part V:   Cleared-denominator main induction
  Part VI:  Normalized Newton (derived from cleared-denom form)
  Part VII: Power inequality aₖ^(k+1) ≥ aₖ₊₁^k
  Part VIII: Maclaurin step Mₖ ≥ Mₖ₊₁

  References:
  - Hardy-Littlewood-Pólya "Inequalities" (1934) §2.22
  - Newton (1707), Maclaurin (1729)
  - AmgmInequalityOQ02.lean (parent formalization)
-/

import Proofs.AmgmInequalityOQ02
import Proofs.NewtonInductiveStep

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
## Part II: Unnormalized Newton's Inequality

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
## Part III: Log-Concavity of Binomial Coefficients
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
## Part IV: Cleared-Denominator Inductive Step
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

set_option maxHeartbeats 3200000 in
/-- The inductive step of the normalized Newton inequality (cleared-denominator form).
    After substituting the recurrence E_k = e_k + t·e_{k-1}, this reduces to a
    polynomial inequality in 9 variables whose proof requires a sum-of-squares
    certificate, the real-rootedness approach, or a total positivity argument.

    This is a well-known true result: it follows from the fact that ∏(1 + xᵢz)
    has all real roots when xᵢ ≥ 0, and polynomials with real roots have
    ultra-log-concave normalized coefficients.

    **Proof strategy**: After Pascal's identity C(m+1,j) = C(m,j) + C(m,j-1),
    expand LHS - RHS as a quadratic in t: A + B·t + C·t² where:
    - A ≥ 0 from IH at k
    - C ≥ 0 from IH at k-1
    - 4·A·C ≥ B² from combining IH instances with cross-product inequality
    Then A + B·t + C·t² ≥ 0 for all t ≥ 0 follows from discriminant analysis. -/
theorem newton_cleared_denom_inductive_step (m k : ℕ) (hk : 2 ≤ k) (hm_eq : k + 1 ≤ m)
    (ek ekm1 ekp1 ekm2 t : ℝ)
    (ht_nn : 0 ≤ t)
    (hek_nn : 0 ≤ ek) (hekm1_nn : 0 ≤ ekm1)
    (hekp1_nn : 0 ≤ ekp1) (hekm2_nn : 0 ≤ ekm2)
    (h_unn_k : ek ^ 2 ≥ ekm1 * ekp1)
    (h_unn_km1 : ekm1 ^ 2 ≥ ekm2 * ek)
    (h_cross : ek * ekm1 ≥ ekm2 * ekp1)
    (h_ih_k : ek ^ 2 * ((Nat.choose m (k - 1) : ℝ) * (Nat.choose m (k + 1) : ℝ)) ≥
        ekm1 * ekp1 * (Nat.choose m k : ℝ) ^ 2)
    (h_ih_km1 : ekm1 ^ 2 * ((Nat.choose m (k - 2) : ℝ) * (Nat.choose m k : ℝ)) ≥
        ekm2 * ek * (Nat.choose m (k - 1) : ℝ) ^ 2) :
    (ek + t * ekm1) ^ 2 * ((Nat.choose (m + 1) (k - 1) : ℝ) * (Nat.choose (m + 1) (k + 1) : ℝ)) ≥
    (ekm1 + t * ekm2) * (ekp1 + t * ek) * (Nat.choose (m + 1) k : ℝ) ^ 2 := by
  -- Abbreviate binomial coefficients for readability
  set a := (Nat.choose m (k - 2) : ℝ) with ha_def
  set b := (Nat.choose m (k - 1) : ℝ) with hb_def
  set c := (Nat.choose m k : ℝ) with hc_def
  set d := (Nat.choose m (k + 1) : ℝ) with hd_def
  -- Pascal's identity: C(m+1, j) = C(m, j) + C(m, j-1)
  have hk2 : k - 2 + 1 = k - 1 := by omega
  have hk1 : k - 1 + 1 = k := by omega
  have pascal_km1 : (Nat.choose (m + 1) (k - 1) : ℝ) = b + a := by
    have h1 : Nat.choose (m + 1) (k - 1) = Nat.choose m (k - 2) + Nat.choose m (k - 1) := by
      rw [← hk2]; exact Nat.choose_succ_succ m (k - 2)
    push_cast [h1]; ring
  have pascal_k : (Nat.choose (m + 1) k : ℝ) = c + b := by
    have h1 : Nat.choose (m + 1) k = Nat.choose m (k - 1) + Nat.choose m k := by
      rw [← hk1]; exact Nat.choose_succ_succ m (k - 1)
    push_cast [h1]; ring
  have pascal_kp1 : (Nat.choose (m + 1) (k + 1) : ℝ) = d + c := by
    push_cast [Nat.choose_succ_succ m k]; ring
  rw [pascal_km1, pascal_k, pascal_kp1]
  -- Non-negativity of binomial coefficients
  have ha_nn : 0 ≤ a := Nat.cast_nonneg _
  have hb_nn : 0 ≤ b := Nat.cast_nonneg _
  have hc_nn : 0 ≤ c := Nat.cast_nonneg _
  have hd_nn : 0 ≤ d := Nat.cast_nonneg _
  -- === PROOF via quadratic_nonneg + absorption identities ===
  -- LHS - RHS = α·t² + β·t + γ where:
  --   γ = ek²·AD - ekm1·ekp1·B2 ≥ 0  (from IH at k + binom_ineq)
  --   α = ekm1²·AD - ekm2·ek·B2 ≥ 0  (from IH at k-1 + dual binom)
  --   4αγ ≥ β²                        (from combined IH + cross products)
  -- Then quadratic_nonneg gives α·t²+β·t+γ ≥ 0 for t ≥ 0.
  --
  -- Step 1: Binom inequality and its dual
  have h_binom := binom_ineq m k hk hm_eq
  set AD := (b + a) * (d + c) with hAD_def
  set B2 := (c + b) ^ 2 with hB2_def
  have hAD_nn : 0 ≤ AD := by
    unfold_let AD; nlinarith [mul_nonneg ha_nn hd_nn, mul_nonneg hb_nn hc_nn]
  -- binom_ineq ↔ c²·AD ≥ bd·B2
  have h_c2AD_ge_bdB2 : c ^ 2 * AD ≥ b * d * B2 := by nlinarith [h_binom]
  -- Algebraic identity gives dual: b²·AD ≥ ac·B2
  have h_binom_symm : (c ^ 2 - b ^ 2) * AD = (b * d - a * c) * B2 := by
    unfold_let AD B2; ring
  have h_b2AD_ge_acB2 : b ^ 2 * AD ≥ a * c * B2 := by
    nlinarith [h_c2AD_ge_bdB2, h_binom_symm]
  -- Positivity of binomial coefficients
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast Nat.choose_pos (show k - 1 ≤ m by omega)
  have hc_pos : (0 : ℝ) < c := by exact_mod_cast Nat.choose_pos (show k ≤ m by omega)
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast Nat.choose_pos (show k + 1 ≤ m by omega)
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast Nat.choose_pos (show k - 2 ≤ m by omega)
  --
  -- Step 2: γ ≥ 0
  have hγ : ek ^ 2 * AD ≥ ekm1 * ekp1 * B2 := by
    -- bd·γ = (ek²bd - ekm1ekp1c²)·AD + ekm1ekp1·(c²AD - bdB2) ≥ 0
    have t1 : 0 ≤ (ek ^ 2 * (b * d) - ekm1 * ekp1 * c ^ 2) * AD :=
      mul_nonneg (by nlinarith [h_ih_k]) hAD_nn
    have t2 : 0 ≤ ekm1 * ekp1 * (c ^ 2 * AD - b * d * B2) :=
      mul_nonneg (mul_nonneg hekm1_nn hekp1_nn) (by nlinarith [h_c2AD_ge_bdB2])
    have h_sum : (ek ^ 2 * (b * d) - ekm1 * ekp1 * c ^ 2) * AD +
        ekm1 * ekp1 * (c ^ 2 * AD - b * d * B2) =
        b * d * (ek ^ 2 * AD - ekm1 * ekp1 * B2) := by unfold_let AD B2; ring
    by_contra h_neg; push_neg at h_neg
    linarith [mul_neg_of_pos_of_neg (mul_pos hb_pos hd_pos) (by linarith :
      ek ^ 2 * AD - ekm1 * ekp1 * B2 < 0)]
  --
  -- Step 3: α ≥ 0
  have hα : ekm1 ^ 2 * AD ≥ ekm2 * ek * B2 := by
    have t1 : 0 ≤ (ekm1 ^ 2 * (a * c) - ekm2 * ek * b ^ 2) * AD :=
      mul_nonneg (by nlinarith [h_ih_km1]) hAD_nn
    have t2 : 0 ≤ ekm2 * ek * (b ^ 2 * AD - a * c * B2) :=
      mul_nonneg (mul_nonneg hekm2_nn hek_nn) (by nlinarith [h_b2AD_ge_acB2])
    have h_sum : (ekm1 ^ 2 * (a * c) - ekm2 * ek * b ^ 2) * AD +
        ekm2 * ek * (b ^ 2 * AD - a * c * B2) =
        a * c * (ekm1 ^ 2 * AD - ekm2 * ek * B2) := by unfold_let AD B2; ring
    by_contra h_neg; push_neg at h_neg
    linarith [mul_neg_of_pos_of_neg (mul_pos ha_pos hc_pos) (by linarith :
      ekm1 ^ 2 * AD - ekm2 * ek * B2 < 0)]
  --
  -- Step 4: Discriminant 4αγ ≥ β²
  have hdisc : 4 * (ekm1 ^ 2 * AD - ekm2 * ek * B2) *
      (ek ^ 2 * AD - ekm1 * ekp1 * B2) ≥
      (2 * ek * ekm1 * AD - (ek * ekm1 + ekm2 * ekp1) * B2) ^ 2 := by
    -- Non-negative excess terms from IH and log-concavity
    have δ₁ : 0 ≤ ek ^ 2 * (b * d) - ekm1 * ekp1 * c ^ 2 := by nlinarith [h_ih_k]
    have δ₂ : 0 ≤ ekm1 ^ 2 * (a * c) - ekm2 * ek * b ^ 2 := by nlinarith [h_ih_km1]
    have hU : 0 ≤ ek ^ 2 - ekm1 * ekp1 := by nlinarith [h_unn_k]
    have hV : 0 ≤ ekm1 ^ 2 - ekm2 * ek := by nlinarith [h_unn_km1]
    have hW : 0 ≤ ek * ekm1 - ekm2 * ekp1 := by nlinarith [h_cross]
    -- Products of excess terms (all non-negative)
    nlinarith [mul_nonneg δ₁ hV, mul_nonneg δ₂ hU, mul_nonneg δ₁ δ₂,
               mul_nonneg (mul_nonneg hW hekm2_nn) hekp1_nn,
               sq_nonneg (ek * ekm1 - ekm2 * ekp1),
               sq_nonneg ((ek ^ 2 - ekm1 * ekp1) * ekm2 * ekp1),
               sq_nonneg (ek * ekm1 * c - ekm2 * ekp1 * b),
               sq_nonneg (ek * ekm1 * d - ekm2 * ekp1 * c),
               mul_nonneg (by nlinarith [h_c2AD_ge_bdB2] : 0 ≤ c ^ 2 * AD - b * d * B2) hU,
               mul_nonneg (by nlinarith [h_b2AD_ge_acB2] : 0 ≤ b ^ 2 * AD - a * c * B2) hV,
               mul_nonneg hek_nn hekm1_nn, mul_nonneg hekm2_nn hekp1_nn,
               mul_nonneg (mul_nonneg hek_nn hekm1_nn) (mul_nonneg hekm2_nn hekp1_nn)]
  --
  -- Step 5: Apply quadratic_nonneg and connect to goal
  have h_quad := quadratic_nonneg
    (ekm1 ^ 2 * AD - ekm2 * ek * B2)
    (2 * ek * ekm1 * AD - (ek * ekm1 + ekm2 * ekp1) * B2)
    (ek ^ 2 * AD - ekm1 * ekp1 * B2)
    t ht_nn (by linarith [hα]) (by linarith [hγ]) hdisc
  -- Ring identity: LHS - RHS = α·t² + β·t + γ
  have h_ring : (ek + t * ekm1) ^ 2 * AD - (ekm1 + t * ekm2) * (ekp1 + t * ek) * B2 =
      (ekm1 ^ 2 * AD - ekm2 * ek * B2) * t ^ 2 +
      (2 * ek * ekm1 * AD - (ek * ekm1 + ekm2 * ekp1) * B2) * t +
      (ek ^ 2 * AD - ekm1 * ekp1 * B2) := by ring
  linarith [h_quad, h_ring]

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
    by_cases hk1 : k = 1
    · -- k = 1: reduce to maclaurin_sq_m1_ge_m2_general
      subst hk1
      simp only [show (1 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
                 elemSymm_zero, Nat.choose_zero_right]
      simp only [Nat.cast_one, one_mul, Nat.choose_one_right]
      rw [ge_iff_le, elemSymm_one]
      have h := maclaurin_sq_m1_ge_m2_general (by omega : 2 ≤ m + 1) x
      rw [ge_iff_le] at h
      push_cast at h ⊢
      linarith [mul_comm (elemSymm 2 x) ((↑m + 1) ^ 2),
                mul_comm ((Nat.choose (m + 1) 2 : ℝ)) ((∑ i, x i) ^ 2)]
    · -- k ≥ 2: induction on n using recurrence
      have hk2 : 2 ≤ k := by omega
      -- Set up variables
      set y := x ∘ Fin.castSucc with hy_def
      set t := x (Fin.last m) with ht_def
      have ht_nn : 0 ≤ t := hx (Fin.last m)
      have hy_nn : ∀ i, 0 ≤ y i := fun i => hx (Fin.castSucc i)
      -- Recurrences: E_j = e_j + t · e_{j-1}
      have rec_k : elemSymm k x = elemSymm k y + t * elemSymm (k - 1) y := by
        have h := elemSymm_succ (k - 1) x; rwa [show k - 1 + 1 = k from by omega] at h
      have rec_km1 : elemSymm (k - 1) x = elemSymm (k - 1) y + t * elemSymm (k - 2) y := by
        have h := elemSymm_succ (k - 2) x; rwa [show k - 2 + 1 = k - 1 from by omega] at h
      have rec_kp1 : elemSymm (k + 1) x = elemSymm (k + 1) y + t * elemSymm k y :=
        elemSymm_succ k x
      -- Abbreviations for elemSymm of y
      set ek := elemSymm k y
      set ekm1 := elemSymm (k - 1) y
      set ekp1 := elemSymm (k + 1) y
      set ekm2 := elemSymm (k - 2) y
      -- Non-negativity
      have hek_nn : 0 ≤ ek := elemSymm_nonneg _ y hy_nn
      have hekm1_nn : 0 ≤ ekm1 := elemSymm_nonneg _ y hy_nn
      have hekp1_nn : 0 ≤ ekp1 := elemSymm_nonneg _ y hy_nn
      have hekm2_nn : 0 ≤ ekm2 := elemSymm_nonneg _ y hy_nn
      -- Unnormalized Newton for y (already proved)
      have h_unn_k : ek ^ 2 ≥ ekm1 * ekp1 := by
        rcases le_or_lt (k + 1) m with hkm | hkm
        · exact elemSymm_log_concave m k hk hkm y hy_nn
        · have : ekp1 = 0 := elemSymm_gt_eq_zero (k + 1) (by omega) y
          simp [this]; exact sq_nonneg _
      have h_unn_km1 : ekm1 ^ 2 ≥ ekm2 * ek := by
        rcases le_or_lt k m with hkm | hkm
        · have h := elemSymm_log_concave m (k - 1) (by omega) (by omega : k - 1 + 1 ≤ m) y hy_nn
          rwa [show k - 1 - 1 = k - 2 from by omega, show k - 1 + 1 = k from by omega] at h
        · have : ek = 0 := elemSymm_gt_eq_zero k (by omega) y
          simp [this]; exact sq_nonneg _
      -- Cross-product for y (unnormalized)
      have h_cross : ek * ekm1 ≥ ekm2 * ekp1 :=
        cross_product_of_log_concave hekm2_nn hekm1_nn hek_nn hekp1_nn h_unn_km1 h_unn_k
          (fun hb0 hc0 => by
            have : ekp1 = 0 := elemSymm_zero_implies_higher_zero (k - 1) y hy_nn hb0 (k + 1) (by omega)
            simp [this])
      -- Rewrite goal using recurrences
      rw [rec_k, rec_km1, rec_kp1]
      -- The goal is now a polynomial inequality in ek, ekm1, ekp1, ekm2, t, and binomial coefficients.
      -- It's a quadratic in t: P + Q·t + R·t² ≥ 0 for t ≥ 0
      -- where P, Q, R involve the e's and binomial coefficients.
      --
      -- For the general case, we use the IH (newton_cleared_denom for m variables)
      -- combined with the unnormalized Newton inequalities.
      --
      -- IH for m variables at k (if applicable)
      have h_ih_k : k + 1 ≤ m →
          ek ^ 2 * ((Nat.choose m (k - 1) : ℝ) * (Nat.choose m (k + 1) : ℝ)) ≥
          ekm1 * ekp1 * (Nat.choose m k : ℝ) ^ 2 :=
        fun hkm => ih k hk hkm y hy_nn
      -- IH for m variables at k-1 (if applicable)
      have h_ih_km1 : k ≤ m →
          ekm1 ^ 2 * ((Nat.choose m (k - 2) : ℝ) * (Nat.choose m k : ℝ)) ≥
          ekm2 * ek * (Nat.choose m (k - 1) : ℝ) ^ 2 :=
        fun hkm => by
          have h := ih (k - 1) (by omega) (by omega : k - 1 + 1 ≤ m) y hy_nn
          rwa [show k - 1 - 1 = k - 2 from by omega, show k - 1 + 1 = k from by omega] at h
      -- Split: base case (m = k) vs inductive step (m > k)
      by_cases hm_eq : k + 1 ≤ m
      · -- INDUCTIVE STEP: k + 1 ≤ m, both IHs available
        -- After Pascal expansion C(m+1,j) = C(m,j) + C(m,j-1), the goal becomes
        -- a polynomial inequality in 9 variables: ek, ekm1, ekp1, ekm2, t and
        -- 4 binomial coefficients C(m,k-2), C(m,k-1), C(m,k), C(m,k+1).
        --
        -- Available hypotheses:
        -- IH at k: ek²·C(m,k-1)·C(m,k+1) ≥ ekm1·ekp1·C(m,k)²
        -- IH at k-1: ekm1²·C(m,k-2)·C(m,k) ≥ ekm2·ek·C(m,k-1)²
        -- Newton: ek² ≥ ekm1·ekp1, ekm1² ≥ ekm2·ek
        -- Cross-product: ek·ekm1 ≥ ekm2·ekp1
        -- Binomial: C(m,k)² ≥ C(m,k-1)·C(m,k+1), C(m,k-1)² ≥ C(m,k-2)·C(m,k)
        --
        -- The difference LHS-RHS is a quadratic in t: A + Bt + Ct²
        -- with A ≥ 0 (from IH at k), C ≥ 0 (from IH at k-1),
        -- and 4AC ≥ B² (from combined IHs via Cauchy-Schwarz).
        -- The algebraic verification involves degree-6 polynomials in 9 variables,
        -- beyond nlinarith's search capacity. A formal proof would require either:
        -- (1) A custom SOS (sum-of-squares) decomposition certificate
        -- (2) The real-rootedness approach via ∏(1+xᵢz) having all real roots
        -- (3) A total positivity / Cauchy-Binet argument
        exact newton_cleared_denom_inductive_step m k (by omega) hm_eq
          ek ekm1 ekp1 ekm2 t ht_nn
          hek_nn hekm1_nn hekp1_nn hekm2_nn
          h_unn_k h_unn_km1 h_cross
          (h_ih_k hm_eq) (h_ih_km1 (by omega : k ≤ m))
      · -- BASE CASE: m < k+1, so m = k (since hkn gives k+1 ≤ m+1)
        -- ekp1 = 0 since k+1 > m
        have hekp1_zero : ekp1 = 0 := elemSymm_gt_eq_zero (k + 1) (by omega) y
        rw [hekp1_zero]
        simp only [zero_add]
        -- Goal: (ek + t*ekm1)^2 * (C(m+1,k-1) * C(m+1,k+1)) ≥
        --       (ekm1 + t*ekm2) * (t*ek) * C(m+1,k)^2
        -- Since m = k: C(m+1,k+1) = C(k+1,k+1) = 1
        have hm_k : m = k := by omega
        -- Use IH at k-1 for m variables (k ≤ m since m = k)
        have h_ih := h_ih_km1 (by omega : k ≤ m)
        -- Key: multiply by 2k (positive) and use SOS decomposition
        -- 2k * ((ek+t*ekm1)^2 * C(m+1,k-1)*C(m+1,k+1) - (ekm1+t*ekm2)*t*ek*C(m+1,k)^2)
        -- = (k*ek-ekm1*t)^2 * 2*C(m+1,k-1)*C(m+1,k+1)
        --   + (k+1)*t^2*((k-1)*ekm1^2 - 2k*ek*ekm2) * ... (non-negative by IH)
        -- For the base case, use direct nlinarith with targeted hints.
        -- The unnormalized Newton and IH provide enough.
        -- Compute binomial coefficients (m = k)
        -- C(m+1, k+1) = C(k+1, k+1) = 1
        have hCkp1 : Nat.choose (m + 1) (k + 1) = 1 := by rw [hm_k]; exact Nat.choose_self _
        -- k * C(m+1, k) = 2 * C(m+1, k-1) (from choose_mul_pred)
        have h_rel : (k : ℝ) * (Nat.choose (m + 1) k : ℝ) =
            2 * (Nat.choose (m + 1) (k - 1) : ℝ) := by
          have h := choose_mul_pred (m + 1) k (by omega) (by omega)
          rw [show m + 1 - k + 1 = 2 from by omega] at h
          exact_mod_cast h
        -- C(m, k) = C(k, k) = 1
        have hCmk : (Nat.choose m k : ℝ) = 1 := by
          rw [hm_k]; simp [Nat.choose_self]
        -- C(m, k-1) = C(k, k-1) = k
        have hCmkm1 : (Nat.choose m (k - 1) : ℝ) = (k : ℝ) := by
          rw [hm_k]
          have : Nat.choose k (k - 1) = k := by
            cases k with
            | zero => omega
            | succ n => simp [Nat.succ_sub_one]
          exact_mod_cast this
        -- (k-1)*C(m,k-1) = 2*C(m,k-2) in ℕ
        have h_rel2_nat := choose_mul_pred m (k - 1) (by omega) (by omega : k - 1 ≤ m)
        rw [show k - 1 - 1 = k - 2 from by omega,
            show m - (k - 1) + 1 = 2 from by omega] at h_rel2_nat
        -- h_rel2_nat : (k-1) * C(m,k-1) = 2 * C(m,k-2)  in ℕ
        -- Cast to ℝ
        have h_rel2 : ((k : ℝ) - 1) * (Nat.choose m (k - 1) : ℝ) = 2 * (Nat.choose m (k - 2) : ℝ) := by
          have h_cast := congr_arg (Nat.cast : ℕ → ℝ) h_rel2_nat
          push_cast [Nat.cast_sub (show 1 ≤ k by omega)] at h_cast
          linarith
        -- Now use hCmkm1 to get (k-1)*k = 2*C(m,k-2) in ℝ
        rw [hCmkm1] at h_rel2
        -- h_rel2 : (k-1)*k = 2*C(m,k-2) in ℝ
        -- IH at k-1: ekm1^2 * (C(m,k-2) * C(m,k)) ≥ ekm2 * ek * C(m,k-1)^2
        -- With hCmk (=1): ekm1^2 * C(m,k-2) ≥ ekm2 * ek * k^2
        -- With h_rel2: C(m,k-2) = (k-1)*k/2
        -- So IH gives: ekm1^2 * (k-1)*k/2 ≥ ekm2 * ek * k^2
        -- i.e., (k-1)*ekm1^2 ≥ 2*k*ek*ekm2
        -- This is exactly what we need for the SOS proof.
        -- Extract: (k-1)*ekm1^2 ≥ 2*k*ek*ekm2
        have h_sos_coeff : ((k : ℝ) - 1) * ekm1 ^ 2 ≥ 2 * (k : ℝ) * ek * ekm2 := by
          -- From h_ih: ekm1^2 * (C(m,k-2) * C(m,k)) ≥ ekm2 * ek * C(m,k-1)^2
          rw [hCmk] at h_ih
          -- h_ih: ekm1^2 * (C(m,k-2) * 1) ≥ ekm2 * ek * C(m,k-1)^2
          rw [hCmkm1] at h_ih
          -- h_ih: ekm1^2 * (C(m,k-2) * 1) ≥ ekm2 * ek * k^2
          have hk_pos : (0 : ℝ) < k := by positivity
          -- From h_rel2: (k-1)*k = 2*C(m,k-2), so C(m,k-2) = (k-1)*k/2
          -- Multiply h_ih: ekm1^2 * C(m,k-2) ≥ ekm2 * ek * k^2
          -- Substitute C(m,k-2) = (k-1)*k/2:
          -- ekm1^2 * (k-1)*k/2 ≥ ekm2 * ek * k^2
          -- Divide by k/2 (positive): (k-1)*ekm1^2 ≥ 2*k*ek*ekm2
          nlinarith [h_rel2, mul_one (Nat.choose m (k - 2) : ℝ)]
        -- Now the goal is:
        -- (ek + t*ekm1)^2 * (C(m+1,k-1) * 1) ≥ (ekm1 + t*ekm2) * (t*ek) * C(m+1,k)^2
        -- Substitute hCkp1: C(m+1,k+1) = 1
        rw [show (Nat.choose (m + 1) (k + 1) : ℝ) = 1 from by exact_mod_cast hCkp1]
        simp only [mul_one]
        -- Use h_rel to express C(m+1,k-1) in terms of C(m+1,k):
        -- k * C(m+1,k) = 2 * C(m+1,k-1)
        -- C(m+1,k-1) = k * C(m+1,k) / 2
        -- The goal becomes a polynomial in ek, ekm1, ekm2, t, C(m+1,k)
        -- (ek+t*ekm1)^2 * C(m+1,k-1) ≥ (ekm1+t*ekm2)*t*ek * C(m+1,k)^2
        -- Set C = C(m+1,k). Then C(m+1,k-1) = k*C/2.
        -- (ek+t*ekm1)^2 * k*C/2 ≥ (ekm1+t*ekm2)*t*ek * C^2
        -- Divide by C/2 (positive): k*(ek+t*ekm1)^2 ≥ 2*(ekm1+t*ekm2)*t*ek*C
        -- But C = C(m+1,k) = C(k+1,k) = k+1
        -- So: k*(ek+t*ekm1)^2 ≥ 2*(k+1)*(ekm1+t*ekm2)*t*ek
        -- Expand LHS: k*(ek^2 + 2*ek*t*ekm1 + t^2*ekm1^2)
        --           = k*ek^2 + 2k*ek*t*ekm1 + k*t^2*ekm1^2
        -- RHS: 2(k+1)*t*(ekm1*ek + t*ekm2*ek)
        --     = 2(k+1)*t*ekm1*ek + 2(k+1)*t^2*ekm2*ek
        -- Diff: k*ek^2 + (2k-2(k+1))*t*ekm1*ek + (k*ekm1^2 - 2(k+1)*ekm2*ek)*t^2
        --      = k*ek^2 - 2*t*ekm1*ek + (k*ekm1^2 - 2(k+1)*ekm2*ek)*t^2
        -- Need: k*ek^2 - 2*t*ekm1*ek + (k*ekm1^2 - 2(k+1)*ekm2*ek)*t^2 ≥ 0
        -- Hmm, this doesn't match the SOS decomposition exactly. Let me compute C(k+1,k).
        have hCmp1k : (Nat.choose (m + 1) k : ℝ) = ((k : ℝ) + 1) := by
          rw [hm_k]
          have : Nat.choose (k + 1) k = k + 1 := by simp
          exact_mod_cast this
        -- C(m+1,k-1) = k*(k+1)/2 from h_rel
        have hCmp1km1 : (Nat.choose (m + 1) (k - 1) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
          have := h_rel; rw [hCmp1k] at this
          linarith
        -- Goal: (ek+t*ekm1)^2 * (k*(k+1)/2) ≥ (ekm1+t*ekm2)*t*ek*(k+1)^2
        -- Multiply by 2/(k+1) (positive):
        -- (ek+t*ekm1)^2 * k ≥ 2*(ekm1+t*ekm2)*t*ek*(k+1)
        -- This is the key inequality.
        -- SOS: k*(ek+t*ekm1)^2 - 2*(k+1)*t*ek*(ekm1+t*ekm2)
        --    = k*ek^2 + 2k*t*ek*ekm1 + k*t^2*ekm1^2
        --      - 2(k+1)*t*ek*ekm1 - 2(k+1)*t^2*ek*ekm2
        --    = k*ek^2 - 2*t*ek*ekm1 + k*t^2*ekm1^2 - 2(k+1)*t^2*ek*ekm2
        --    = k*ek^2 - 2*t*ek*ekm1 + t^2*(k*ekm1^2 - 2(k+1)*ek*ekm2)
        -- From h_sos_coeff: (k-1)*ekm1^2 ≥ 2k*ek*ekm2
        --   so k*ekm1^2 - 2(k+1)*ek*ekm2 = k*ekm1^2 - 2k*ek*ekm2 - 2*ek*ekm2
        --                                  ≥ (k-1)*ekm1^2 - 2*ek*ekm2 + ekm1^2 - 2*ek*ekm2
        -- This doesn't simplify nicely. Let me try a different SOS.
        -- Actually: k*ek^2 - 2*t*ek*ekm1 + t^2*(k*ekm1^2 - 2(k+1)*ek*ekm2)
        -- We need this ≥ 0 for t ≥ 0. This is quadratic in t with:
        -- A = k*ekm1^2 - 2(k+1)*ek*ekm2 (coefficient of t^2)
        -- B = -2*ek*ekm1 (coefficient of t)
        -- C = k*ek^2 (constant)
        -- If A ≥ 0 and 4AC ≥ B², then ≥ 0 for all t.
        -- 4AC = 4k^2*ek^2*(ekm1^2 - 2(k+1)/k*ek*ekm2)
        -- B² = 4*ek^2*ekm1^2
        -- 4AC - B² = 4*ek^2*(k^2*ekm1^2 - 2k(k+1)*ek*ekm2 - ekm1^2)
        --          = 4*ek^2*((k^2-1)*ekm1^2 - 2k(k+1)*ek*ekm2)
        --          = 4*ek^2*(k+1)*((k-1)*ekm1^2 - 2k*ek*ekm2) ≥ 0 by h_sos_coeff!
        -- So: use discriminant argument: A ≥ 0 ∧ 4AC ≥ B² → At^2+Bt+C ≥ 0
        -- But actually for t ≥ 0 we can be weaker: just need C ≥ 0 and
        -- the minimum in [0,∞) to be ≥ 0. If B ≤ 0 (which it is since ek,ekm1 ≥ 0),
        -- min is at t = -B/(2A) if A > 0, and value = C - B²/(4A) = (4AC-B²)/(4A) ≥ 0.
        -- Or if A = 0, need B ≥ 0 (B = -2*ek*ekm1 ≤ 0, so need ek*ekm1 = 0).
        -- Let's just use nlinarith with the right hints.
        rw [hCmp1km1, hCmp1k]
        -- Goal: (ek+t*ekm1)^2 * (k*(k+1)/2) ≥ (ekm1+t*ekm2)*(t*ek)*(k+1)^2
        -- Reduce to division-free form by suffices
        have hk_pos : (0 : ℝ) < k := by positivity
        have hkp1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        -- Suffices: k*(ek+t*ekm1)^2 ≥ 2*(k+1)*(ekm1+t*ekm2)*(t*ek)
        -- Then multiply by (k+1)/2 to get the original goal
        suffices hsuff : (↑k : ℝ) * (ek + t * ekm1) ^ 2 ≥
            2 * ((↑k : ℝ) + 1) * ((ekm1 + t * ekm2) * (t * ek)) by
          -- hsuff * (k+1)/2 gives: k*(k+1)/2 * f^2 ≥ (k+1)^2 * g*t*ek
          nlinarith [mul_le_mul_of_nonneg_right hsuff (by linarith : (0 : ℝ) ≤ ((↑k : ℝ) + 1) / 2)]
        -- Now prove hsuff (no division in goal)
        -- SOS: k*(k*f^2 - 2*(k+1)*g*t*ek) = (k*ek-t*ekm1)^2 + t^2*(k+1)*((k-1)*ekm1^2-2k*ek*ekm2)
        have h_coeff_nn : ((k : ℝ) - 1) * ekm1 ^ 2 - 2 * (k : ℝ) * ek * ekm2 ≥ 0 := by
          linarith [h_sos_coeff]
        have h_sq1 := sq_nonneg ((k : ℝ) * ek - t * ekm1)
        have h_term2 : t ^ 2 * ((k : ℝ) + 1) * (((k : ℝ) - 1) * ekm1 ^ 2 - 2 * (k : ℝ) * ek * ekm2) ≥ 0 := by
          apply mul_nonneg
          · apply mul_nonneg; exact sq_nonneg t; linarith
          · linarith [h_coeff_nn]
        -- k * (k*f^2 - 2*(k+1)*g*t*ek) ≥ 0, and k > 0, so k*f^2 ≥ 2*(k+1)*g*t*ek
        have h_k_times : (↑k : ℝ) * ((↑k : ℝ) * (ek + t * ekm1) ^ 2 -
            2 * ((↑k : ℝ) + 1) * ((ekm1 + t * ekm2) * (t * ek))) ≥ 0 := by
          -- SOS identity: K*expr = (K*ek - t*ekm1)² + (K+1)*t²*((K-1)*ekm1² - 2K*ek*ekm2)
          have h_sos_id :
            (↑k : ℝ) * ((↑k : ℝ) * (ek + t * ekm1) ^ 2 -
            2 * ((↑k : ℝ) + 1) * ((ekm1 + t * ekm2) * (t * ek))) =
            ((↑k : ℝ) * ek - t * ekm1) ^ 2 +
            ((↑k : ℝ) + 1) * t ^ 2 * (((↑k : ℝ) - 1) * ekm1 ^ 2 - 2 * (↑k : ℝ) * ek * ekm2) := by
            ring
          rw [h_sos_id]
          apply add_nonneg (sq_nonneg _)
          apply mul_nonneg
          · apply mul_nonneg
            · linarith
            · exact sq_nonneg t
          · linarith [h_coeff_nn]
        -- Divide by k > 0
        have hk_pos : (↑k : ℝ) > 0 := by positivity
        by_contra h_neg
        push_neg at h_neg
        have : (↑k : ℝ) * ((↑k : ℝ) * (ek + t * ekm1) ^ 2 -
            2 * ((↑k : ℝ) + 1) * ((ekm1 + t * ekm2) * (t * ek))) < 0 := by
          exact mul_neg_of_pos_of_neg hk_pos (by linarith)
        linarith

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
## Part VII: Power Inequality and Maclaurin Step

Now that newton_log_concavity_proved is available as a theorem (not an axiom),
we derive the remaining results without any axiom dependency.
-/

/-- Normalized Newton's log-concavity as a lemma (proved, not axiom). -/
lemma normESym_log_concave {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    normESym k x ^ 2 ≥ normESym (k - 1) x * normESym (k + 1) x :=
  newton_log_concavity_proved k hk hkn x hx

/-- Key lemma: log-concavity implies the power inequality aₖ^(k+1) ≥ aₖ₊₁^k.
    Proved by induction on k using a division-free argument. -/
theorem power_ineq_of_log_concave {n : ℕ} (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    normESym k x ^ (k + 1) ≥ normESym (k + 1) x ^ k := by
  induction k with
  | zero => omega
  | succ m ih =>
    by_cases ha_zero : normESym (m + 1) x = 0
    · have hb_zero : normESym (m + 2) x = 0 :=
        normESym_zero_implies_higher_zero (m + 1) (m + 2) x hx
          (by omega) (by omega) (by omega) ha_zero
      simp [ha_zero, hb_zero]
    · have ha_nn : 0 ≤ normESym (m + 1) x := normESym_nonneg _ x hx
      have ha_pos : 0 < normESym (m + 1) x := lt_of_le_of_ne ha_nn (Ne.symm ha_zero)
      cases m with
      | zero =>
        have h_newton := normESym_log_concave 1 le_rfl hkn x hx
        simp only [show (1 : ℕ) - 1 = 0 from rfl, show (1 : ℕ) + 1 = 2 from rfl,
                   normESym_zero] at h_newton
        simp only [show (0 : ℕ) + 1 = 1 from rfl, show (0 : ℕ) + 2 = 2 from rfl]
        linarith
      | succ p =>
        have ha_prev_nn : 0 ≤ normESym (p + 1) x := normESym_nonneg _ x hx
        have h_newton : normESym (p + 2) x ^ 2 ≥
            normESym (p + 1) x * normESym (p + 3) x := by
          have := normESym_log_concave (p + 2) (by omega) (by omega : p + 2 + 1 ≤ n) x hx
          simp only [show p + 2 - 1 = p + 1 from by omega,
                     show p + 2 + 1 = p + 3 from by omega] at this
          exact this
        have h_ih : normESym (p + 1) x ^ (p + 2) ≥ normESym (p + 2) x ^ (p + 1) := by
          have := ih (by omega : 1 ≤ p + 1) (by omega : p + 1 + 1 ≤ n)
          simp only [show p + 1 + 1 = p + 2 from by omega] at this
          exact this
        simp only [show p + 1 + 1 = p + 2 from by omega,
                   show p + 1 + 2 = p + 3 from by omega]
        have h1 : (normESym (p + 2) x ^ 2) ^ (p + 2) ≥
            (normESym (p + 1) x * normESym (p + 3) x) ^ (p + 2) :=
          pow_le_pow_left₀ (mul_nonneg ha_prev_nn (normESym_nonneg _ x hx)) h_newton (p + 2)
        rw [← pow_mul, mul_pow] at h1
        have h2 : normESym (p + 2) x ^ (2 * (p + 2)) ≥
            normESym (p + 2) x ^ (p + 1) * normESym (p + 3) x ^ (p + 2) :=
          calc normESym (p + 2) x ^ (2 * (p + 2))
              ≥ normESym (p + 1) x ^ (p + 2) * normESym (p + 3) x ^ (p + 2) := h1
            _ ≥ normESym (p + 2) x ^ (p + 1) * normESym (p + 3) x ^ (p + 2) :=
                mul_le_mul_of_nonneg_right h_ih (pow_nonneg (normESym_nonneg _ x hx) _)
        have h_split : 2 * (p + 2) = (p + 1) + (p + 3) := by omega
        rw [h_split, pow_add] at h2
        have ha_pow_pos : 0 < normESym (p + 2) x ^ (p + 1) := pow_pos ha_pos _
        exact le_of_mul_le_mul_left (by linarith) ha_pow_pos

/-- If 0 ≤ a, 0 ≤ b, 0 < k, and a^(k+1) ≥ b^k, then a^(1/k) ≥ b^(1/(k+1)).
    Uses the identity a^(1/k) = (a^(k+1))^(1/(k(k+1))) and monotonicity of rpow. -/
theorem rpow_ineq_of_pow_ineq (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℕ) (hk : 0 < k) (h : a ^ (k + 1) ≥ b ^ k) :
    a ^ ((1 : ℝ) / k) ≥ b ^ ((1 : ℝ) / (↑k + 1)) := by
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hk1_pos : (0 : ℝ) < ↑k + 1 := by positivity
  have hkk1_pos : (0 : ℝ) < ↑k * (↑k + 1) := by positivity
  have h_a_rw : a ^ ((1 : ℝ) / k) = (a ^ (k + 1 : ℕ)) ^ ((1 : ℝ) / (↑k * (↑k + 1))) := by
    rw [← Real.rpow_natCast a (k + 1), ← Real.rpow_mul ha]
    congr 1
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  have h_b_rw : b ^ ((1 : ℝ) / (↑k + 1)) = (b ^ (k : ℕ)) ^ ((1 : ℝ) / (↑k * (↑k + 1))) := by
    rw [← Real.rpow_natCast b k, ← Real.rpow_mul hb]
    congr 1
    field_simp
  rw [ge_iff_le, h_b_rw, h_a_rw]
  exact Real.rpow_le_rpow (pow_nonneg hb _) h (by positivity)

/-
## Part VIII: Main Result — Maclaurin Step
-/

/-- Maclaurin step derived as a theorem (not axiom).
    Both axioms in AmgmInequalityOQ02.lean are now redundant. -/
theorem maclaurin_step_derived {n : ℕ} (k : ℕ) (hk : 0 < k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    maclaurinMean k x ≥ maclaurinMean (k + 1) x := by
  unfold maclaurinMean
  have h_pow := power_ineq_of_log_concave k hk hkn x hx
  have h_rpow := rpow_ineq_of_pow_ineq
    (normESym k x) (normESym (k + 1) x)
    (normESym_nonneg k x hx) (normESym_nonneg (k + 1) x hx)
    k hk h_pow
  simp only [normESym, ge_iff_le] at h_rpow ⊢
  convert h_rpow using 2 <;> simp [one_div, Nat.cast_add, Nat.cast_one]

/-
## Summary

### All theorems fully proved (0 axioms, 0 sorries):
1. `elemSymm_zero_implies_higher_zero` — zero tail property
2. `normESym_zero_implies_higher_zero` — normalized version
3. `cross_product_of_log_concave` — aₖ·aₖ₋₁ ≥ aₖ₋₂·aₖ₊₁
4. `elemSymm_log_concave` — eₖ² ≥ eₖ₋₁·eₖ₊₁ (unnormalized Newton)
5. `binom_log_concave` — C(n,k)² ≥ C(n,k-1)·C(n,k+1)
6. `newton_cleared_denom_inductive_step` — inductive step via absorption + discriminant
7. `newton_cleared_denom` — cleared-denominator form by induction
8. `newton_log_concavity_proved` — normalized Newton (replaces axiom)
9. `normESym_log_concave` — convenience wrapper using the proved theorem
10. `power_ineq_of_log_concave` — aₖ^(k+1) ≥ aₖ₊₁^k
11. `rpow_ineq_of_pow_ineq` — nat pow to rpow conversion
12. `maclaurin_step_derived` — Mₖ ≥ Mₖ₊₁ (replaces axiom)

### Axiom elimination:
Both `newton_log_concavity` and `maclaurin_step` axioms in AmgmInequalityOQ02.lean
are now proved as theorems. The full Maclaurin chain M₁ ≥ M₂ ≥ ⋯ ≥ Mₙ
is a complete theorem with no axioms.
-/

end NewtonLogConcavity

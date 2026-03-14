/-
  Newton's Log-Concavity of Elementary Symmetric Polynomials
  Research: amgm-inequality-oq-02-oq-02

  Goal: Prove that for non-negative reals x₁,...,xₙ and 1 ≤ k < n:
    (eₖ/C(n,k))² ≥ (eₖ₋₁/C(n,k-1)) · (eₖ₊₁/C(n,k+1))

  This eliminates the last axiom in the Maclaurin inequalities formalization.

  Proof strategy: Induction on n using the recurrence
    eₖ(x₁,...,xₙ₊₁) = eₖ(x₁,...,xₙ) + xₙ₊₁ · eₖ₋₁(x₁,...,xₙ)

  References:
  - Hardy-Littlewood-Pólya "Inequalities" (1934) §2.22
-/

import Proofs.AmgmInequalityOQ02

open Finset Real

namespace NewtonLC

/-
## Part I: Small cases verified by nlinarith
-/

/-- Newton's inequality for n=3, k=1 -/
theorem newton_n3_k1 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ((a + b + c) / 3) ^ 2 ≥ (a * b + b * c + c * a) / 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

/-- Newton's inequality for n=3, k=2 -/
theorem newton_n3_k2 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ((a * b + b * c + c * a) / 3) ^ 2 ≥
    ((a + b + c) / 3) * (a * b * c) := by
  nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a),
             sq_nonneg (c * a - a * b), mul_nonneg ha hb, mul_nonneg hb hc,
             mul_nonneg hc ha, sq_nonneg a, sq_nonneg b, sq_nonneg c]

/-
## Part II: Infrastructure for the general proof
-/

/-- C(n,k) > 0 when k ≤ n -/
lemma choose_pos_cast {n k : ℕ} (hk : k ≤ n) : (0 : ℝ) < (Nat.choose n k : ℝ) :=
  Nat.cast_pos.mpr (Nat.choose_pos hk)

/-- elemSymm is non-negative for non-negative inputs -/
private lemma esymm_nn {n : ℕ} (k : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ elemSymm k x := elemSymm_nonneg k x hx

/-- A quadratic At² + Bt + C is non-negative for t ≥ 0 when
    A ≥ 0, C ≥ 0, and the discriminant B² ≤ 4AC. -/
private lemma quadratic_nonneg_nonneg_t (A B C t : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hdisc : B ^ 2 ≤ 4 * A * C) (ht : 0 ≤ t) :
    A * t ^ 2 + B * t + C ≥ 0 := by
  -- 4A(At² + Bt + C) = (2At + B)² + (4AC - B²)
  -- Both terms ≥ 0
  by_cases hA0 : A = 0
  · simp [hA0] at hdisc ⊢
    have hB0 : B = 0 := by nlinarith [sq_nonneg B]
    simp [hB0]; linarith
  · have hA_pos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    have h : 0 ≤ 4 * A * (A * t ^ 2 + B * t + C) := by
      nlinarith [sq_nonneg (2 * A * t + B)]
    by_contra hc; push_neg at hc
    have := mul_neg_of_pos_of_neg (by positivity : (0:ℝ) < 4 * A) hc
    linarith

/-
## Part III: Newton's inequality — general proof

We prove this by strong induction on n (number of variables).

The proof uses the recurrence:
  eⱼ(x₁,...,xₙ₊₁) = eⱼ(x₁,...,xₙ) + xₙ₊₁ · eⱼ₋₁(x₁,...,xₙ)

Setting t = xₙ₊₁ and aⱼ = eⱼ(x₁,...,xₙ), the (n+1)-variable
elementary symmetric polynomials become:
  eⱼ(x₁,...,xₙ₊₁) = aⱼ + t · aⱼ₋₁

The Newton inequality for n+1 variables at index k becomes:
  (aₖ + t·aₖ₋₁)² / C(n+1,k) ≥ (aₖ₋₁ + t·aₖ₋₂) · (aₖ₊₁ + t·aₖ) / (C(n+1,k-1)·C(n+1,k+1))

After cross-multiplying and expanding, the difference LHS - RHS is a
quadratic form in t. The constant, linear, and quadratic coefficients
are all non-negative by the inductive hypothesis (Newton for n variables).
-/

set_option maxHeartbeats 800000 in
/-- Newton's inequality — the main theorem.
    For 1 ≤ k, k+1 ≤ n, non-negative x:
    (eₖ(x)/C(n,k))² ≥ (eₖ₋₁(x)/C(n,k-1)) · (eₖ₊₁(x)/C(n,k+1)) -/
theorem newton_ineq : ∀ (n : ℕ) (k : ℕ) (hk : 1 ≤ k) (hkn : k + 1 ≤ n)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i),
    (elemSymm k x / (Nat.choose n k : ℝ)) ^ 2 ≥
    (elemSymm (k - 1) x / (Nat.choose n (k - 1) : ℝ)) *
    (elemSymm (k + 1) x / (Nat.choose n (k + 1) : ℝ)) := by
  -- Strong induction on n
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro k hk hkn x hx
  -- k=1 case: use the already-proved newton_k1
  by_cases hk1 : k = 1
  · subst hk1
    exact newton_k1 (by omega : 2 ≤ n) x
  -- k ≥ 2
  have hk_ge2 : 2 ≤ k := by omega
  -- Base case: n = k+1
  -- When n = k+1, eₖ₊₁ = ∏xᵢ (only full subset), C(n,k+1) = C(k+1,k+1) = 1
  by_cases hbase : n = k + 1
  · -- n = k + 1
    subst hbase
    -- Decompose into first k variables (y) and last variable (t)
    set y := x ∘ Fin.castSucc with hy_def
    set t := x (Fin.last k) with ht_def
    have ht_nn : 0 ≤ t := hx (Fin.last k)
    have hy_nn : ∀ i, 0 ≤ y i := fun i => hx (Fin.castSucc i)
    -- Key quantities
    set P := elemSymm k y with hP_def
    set E := elemSymm (k - 1) y with hE_def
    set F := elemSymm (k - 2) y with hF_def
    -- Non-negativity
    have hP_nn : 0 ≤ P := elemSymm_nonneg k y hy_nn
    have hE_nn : 0 ≤ E := elemSymm_nonneg (k - 1) y hy_nn
    have hF_nn : 0 ≤ F := elemSymm_nonneg (k - 2) y hy_nn
    -- Simplifications for n = k+1 (k variables in y)
    have hEkp1_zero : elemSymm (k + 1) y = 0 :=
      elemSymm_gt_eq_zero (k + 1) (by omega) y
    -- Recurrences
    have h_rec_k : elemSymm k x = P + t * E := by
      have hkm : k - 1 + 1 = k := by omega
      have h := elemSymm_succ (k - 1) x
      rwa [hkm] at h
    have h_rec_kp1 : elemSymm (k + 1) x = t * P := by
      have h := elemSymm_succ k x
      rw [hEkp1_zero, zero_add] at h; exact h
    have h_rec_km1 : elemSymm (k - 1) x = E + t * F := by
      have hkm : k - 2 + 1 = k - 1 := by omega
      have h := elemSymm_succ (k - 2) x
      rwa [hkm] at h
    -- IH at (m=k, index=k-1): Newton's inequality for k variables at index k-1
    -- This is valid since k-1 ≥ 1 (k ≥ 2) and (k-1)+1 = k ≤ k
    have h_ih_km1 : (E / (Nat.choose k (k - 1) : ℝ)) ^ 2 ≥
        (F / (Nat.choose k (k - 2) : ℝ)) * (P / (Nat.choose k k : ℝ)) := by
      have h := ih k (by omega) (k - 1) (by omega) (by omega : k - 1 + 1 ≤ k) y hy_nn
      have h1 : k - 1 - 1 = k - 2 := by omega
      have h2 : k - 1 + 1 = k := by omega
      rwa [h1, h2] at h
    -- Cross-multiply the IH to get: (k-1) · E² ≥ 2k · P · F
    -- C(k, k-1) = k, C(k, k-2) = k(k-1)/2, C(k, k) = 1
    have hCk_km1 : (Nat.choose k (k - 1) : ℝ) = (k : ℝ) := by
      have h := Nat.choose_symm (show k - 1 ≤ k by omega)
      have h1 : k - (k - 1) = 1 := by omega
      rw [h1, Nat.choose_one_right] at h
      exact_mod_cast h.symm
    have hCk_k : (Nat.choose k k : ℝ) = 1 := by simp
    have hCk_km2 : (Nat.choose k (k - 2) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
      have hnat : Nat.choose k (k - 2) = Nat.choose k 2 := by
        have h := Nat.choose_symm (show k - 2 ≤ k by omega)
        have h2 : k - (k - 2) = 2 := by omega
        rw [h2] at h; exact h.symm
      rw [show (Nat.choose k (k - 2) : ℝ) = (Nat.choose k 2 : ℝ) from by exact_mod_cast hnat]
      have h2cn2 : 2 * (Nat.choose k 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
        suffices ∀ m : ℕ, 2 * (Nat.choose m 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) from this k
        intro m; induction m with
        | zero => simp
        | succ j ihj =>
          have hstep : Nat.choose (j + 1) 2 = j + Nat.choose j 2 := by
            have h := Nat.choose_succ_succ j 1; simp only [Nat.choose_one_right] at h; omega
          rw [hstep]; push_cast; nlinarith
      linarith
    -- Cross-multiply IH
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    have hkm1_pos : (0 : ℝ) < (k : ℝ) - 1 := by exact_mod_cast (show (0 : ℤ) < (k : ℤ) - 1 by omega)
    have hCk_km2_pos : (0 : ℝ) < (Nat.choose k (k - 2) : ℝ) := choose_pos_cast (by omega)
    have h_ih_cross : ((k : ℝ) - 1) * E ^ 2 ≥ 2 * (k : ℝ) * P * F := by
      -- From IH: (E/k)² ≥ (F/(k(k-1)/2)) · (P/1), cross-multiply to get (k-1)E² ≥ 2kPF
      rw [hCk_km1, hCk_k, div_one, hCk_km2] at h_ih_km1
      rw [ge_iff_le, ← sub_nonneg] at h_ih_km1 ⊢
      -- Multiply by k²(k-1) > 0 to clear denominators
      have h_mul := mul_nonneg h_ih_km1
        (show (0 : ℝ) ≤ (k : ℝ) ^ 2 * ((k : ℝ) - 1) by positivity)
      have h_expand : ((E / (k : ℝ)) ^ 2 - F / ((k : ℝ) * ((k : ℝ) - 1) / 2) * P) *
          ((k : ℝ) ^ 2 * ((k : ℝ) - 1)) =
          ((k : ℝ) - 1) * E ^ 2 - 2 * (k : ℝ) * P * F := by
        have : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
        have : (k : ℝ) - 1 ≠ 0 := ne_of_gt hkm1_pos
        field_simp <;> ring
      linarith
    -- Main goal: rewrite using recurrences
    rw [h_rec_k, h_rec_km1, h_rec_kp1]
    -- Binomial coefficients for n = k+1
    have hCn_k : (Nat.choose (k + 1) k : ℝ) = (k : ℝ) + 1 := by
      have h := Nat.choose_symm (show k ≤ k + 1 by omega)
      have h2 : k + 1 - k = 1 := by omega
      rw [h2, Nat.choose_one_right] at h
      exact_mod_cast h.symm
    have hCn_kp1 : (Nat.choose (k + 1) (k + 1) : ℝ) = 1 := by simp
    have hCn_km1_val : (Nat.choose (k + 1) (k - 1) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
      have hnat : Nat.choose (k + 1) (k - 1) = Nat.choose (k + 1) 2 := by
        have hsymm := Nat.choose_symm (show k - 1 ≤ k + 1 by omega)
        have hval : k + 1 - (k - 1) = 2 := by omega
        rw [hval] at hsymm; exact hsymm.symm
      rw [show (Nat.choose (k + 1) (k - 1) : ℝ) = (Nat.choose (k + 1) 2 : ℝ) from
        by exact_mod_cast hnat]
      have h2cn2 : 2 * (Nat.choose (k + 1) 2 : ℝ) = ((k : ℝ) + 1) * (k : ℝ) := by
        suffices ∀ m : ℕ, 2 * (Nat.choose m 2 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) from by
          have := this (k + 1); push_cast at this ⊢; linarith
        intro m; induction m with
        | zero => simp
        | succ j ihj =>
          have hstep : Nat.choose (j + 1) 2 = j + Nat.choose j 2 := by
            have h := Nat.choose_succ_succ j 1; simp only [Nat.choose_one_right] at h; omega
          rw [hstep]; push_cast; nlinarith
      linarith
    rw [hCn_k, hCn_kp1, div_one, hCn_km1_val]
    -- Goal: ((P+tE)/(k+1))² ≥ ((E+tF)/(k(k+1)/2)) · (tP)
    -- Use field_simp to clear all denominators, then nlinarith with SOS witness
    rw [ge_iff_le, ← sub_nonneg]
    rw [div_pow, div_mul_eq_mul_div, div_sub_div _ _
          (ne_of_gt (pow_pos (by positivity : (0:ℝ) < (k:ℝ) + 1) 2))
          (ne_of_gt (by positivity : (0:ℝ) < (k:ℝ) * ((k:ℝ) + 1) / 2))]
    apply div_nonneg _ (by positivity)
    -- Goal: 0 ≤ (P+tE)²·(k(k+1)/2) - (E+tF)·tP·(k+1)²
    -- Key identity: 2k · this = (k+1)·[(kP-Et)² + (k+1)·((k-1)E²-2kPF)·t²] ≥ 0
    nlinarith [sq_nonneg ((k : ℝ) * P - E * t),
               mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (k:ℝ) + 1 by linarith)
                 (show (0:ℝ) ≤ ((k:ℝ) - 1) * E ^ 2 - 2 * (k:ℝ) * P * F by linarith))
                 (sq_nonneg t),
               sq_nonneg P, sq_nonneg E, sq_nonneg t,
               mul_nonneg hP_nn hE_nn, mul_nonneg ht_nn hP_nn,
               mul_nonneg ht_nn hE_nn, mul_nonneg hF_nn ht_nn,
               sq_nonneg (k : ℝ)]
  -- Inductive step: n ≥ k + 2
  · have hn_ge : k + 2 ≤ n := by omega
    -- Decompose: n = m + 1 for m ≥ k + 1
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm_ge : k + 1 ≤ m := by omega
    -- y = first m variables, t = last variable
    set y := x ∘ Fin.castSucc with hy_def
    set t := x (Fin.last m) with ht_def
    have ht_nn : 0 ≤ t := hx (Fin.last m)
    have hy_nn : ∀ i, 0 ≤ y i := fun i => hx (Fin.castSucc i)
    -- Recurrences
    have h_rec_k : elemSymm k x = elemSymm k y + t * elemSymm (k - 1) y := by
      have : k - 1 + 1 = k := by omega
      have h := elemSymm_succ (k - 1) x
      rwa [this] at h
    have h_rec_k1 : elemSymm (k + 1) x = elemSymm (k + 1) y + t * elemSymm k y :=
      elemSymm_succ k x
    have h_rec_km1 : elemSymm (k - 1) x = elemSymm (k - 1) y + t * elemSymm (k - 2) y := by
      have : k - 2 + 1 = k - 1 := by omega
      have h := elemSymm_succ (k - 2) x
      rwa [this] at h
    -- IH for m variables at index k (if k + 1 ≤ m)
    have h_ih_k : (elemSymm k y / (Nat.choose m k : ℝ)) ^ 2 ≥
        (elemSymm (k - 1) y / (Nat.choose m (k - 1) : ℝ)) *
        (elemSymm (k + 1) y / (Nat.choose m (k + 1) : ℝ)) := by
      exact ih m (by omega) k hk hm_ge y hy_nn
    -- IH for m variables at index k-1 (if k ≥ 2 and k ≤ m)
    have h_ih_km1 : (elemSymm (k - 1) y / (Nat.choose m (k - 1) : ℝ)) ^ 2 ≥
        (elemSymm (k - 2) y / (Nat.choose m (k - 2) : ℝ)) *
        (elemSymm k y / (Nat.choose m k : ℝ)) := by
      have h := ih m (by omega) (k - 1) (by omega) (by omega) y hy_nn
      -- ih gives: (e_{k-1}/C)² ≥ (e_{k-1-1}/C) · (e_{k-1+1}/C)
      -- Need to show k-1-1 = k-2 and k-1+1 = k
      have h1 : k - 1 - 1 = k - 2 := by omega
      have h2 : k - 1 + 1 = k := by omega
      rwa [h1, h2] at h
    -- Binomial coefficients
    have hCmk : (0 : ℝ) < (Nat.choose m k : ℝ) := choose_pos_cast (by omega)
    have hCmk1 : (0 : ℝ) < (Nat.choose m (k - 1) : ℝ) := choose_pos_cast (by omega)
    have hCmk2 : (0 : ℝ) < (Nat.choose m (k + 1) : ℝ) := choose_pos_cast (by omega)
    have hCmk3 : (0 : ℝ) < (Nat.choose m (k - 2) : ℝ) := choose_pos_cast (by omega)
    -- Abbreviations for readability
    set a := elemSymm k y with ha_def
    set b := elemSymm (k - 1) y with hb_def
    set c := elemSymm (k + 1) y with hc_def
    set d := elemSymm (k - 2) y with hd_def
    set p := (Nat.choose m k : ℝ) with hp_def
    set q := (Nat.choose m (k - 1) : ℝ) with hq_def
    set r := (Nat.choose m (k + 1) : ℝ) with hr_def
    set s := (Nat.choose m (k - 2) : ℝ) with hs_def
    -- Non-negativity
    have ha_nn : 0 ≤ a := elemSymm_nonneg k y hy_nn
    have hb_nn : 0 ≤ b := elemSymm_nonneg (k - 1) y hy_nn
    have hc_nn : 0 ≤ c := elemSymm_nonneg (k + 1) y hy_nn
    have hd_nn : 0 ≤ d := elemSymm_nonneg (k - 2) y hy_nn
    -- Cross-multiplied IH at k: a² · q · r ≥ b · c · p²
    have hIH1 : a ^ 2 * q * r ≥ b * c * p ^ 2 := by
      have h := h_ih_k
      rw [ge_iff_le, ← sub_nonneg] at h ⊢
      have h_denom : (0 : ℝ) < p ^ 2 * q * r :=
        mul_pos (mul_pos (pow_pos hCmk 2) hCmk1) hCmk2
      have h2 : 0 ≤ ((a / p) ^ 2 - b / q * (c / r)) * (p ^ 2 * q * r) :=
        mul_nonneg h h_denom.le
      have h3 : ((a / p) ^ 2 - b / q * (c / r)) * (p ^ 2 * q * r) =
          a ^ 2 * q * r - b * c * p ^ 2 := by
        field_simp <;> ring
      linarith
    -- Cross-multiplied IH at k-1: b² · s · p ≥ d · a · q²
    have hIH2 : b ^ 2 * s * p ≥ d * a * q ^ 2 := by
      have h := h_ih_km1
      rw [ge_iff_le, ← sub_nonneg] at h ⊢
      have h_denom : (0 : ℝ) < q ^ 2 * s * p :=
        mul_pos (mul_pos (pow_pos hCmk1 2) hCmk3) hCmk
      have h2 : 0 ≤ ((b / q) ^ 2 - d / s * (a / p)) * (q ^ 2 * s * p) :=
        mul_nonneg h h_denom.le
      have h3 : ((b / q) ^ 2 - d / s * (a / p)) * (q ^ 2 * s * p) =
          b ^ 2 * s * p - d * a * q ^ 2 := by
        field_simp <;> ring
      linarith
    -- Pascal's rule: C(m+1,j) = C(m,j) + C(m,j-1)
    have hPk : (Nat.choose (m + 1) k : ℝ) = p + q := by
      have h := Nat.choose_succ_succ m (k - 1)
      simp only [Nat.succ_eq_add_one] at h
      rw [show k - 1 + 1 = k from by omega] at h
      push_cast [h] <;> ring
    have hPkm1 : (Nat.choose (m + 1) (k - 1) : ℝ) = q + s := by
      have h := Nat.choose_succ_succ m (k - 2)
      simp only [Nat.succ_eq_add_one] at h
      rw [show k - 2 + 1 = k - 1 from by omega] at h
      push_cast [h] <;> ring
    have hPkp1 : (Nat.choose (m + 1) (k + 1) : ℝ) = r + p := by
      have h := Nat.choose_succ_succ m k
      simp only [Nat.succ_eq_add_one] at h
      push_cast [h] <;> ring
    -- Substitute recurrences into goal
    rw [h_rec_k, h_rec_k1, h_rec_km1, hPk, hPkm1, hPkp1]
    -- Goal: ((a+tb)/(p+q))² ≥ ((b+td)/(q+s)) · ((c+ta)/(r+p))
    -- Cross-multiply: (a+tb)²(q+s)(r+p) ≥ (b+td)(c+ta)(p+q)²
    rw [ge_iff_le, ← sub_nonneg, div_pow, div_mul_div_comm]
    -- Suffices: (a+tb)²·(q+s)·(r+p) - (b+td)·(c+ta)·(p+q)² ≥ 0
    -- (after clearing positive denominators)
    have h_denom_pos : (0 : ℝ) < (p + q) ^ 2 * ((q + s) * (r + p)) := by positivity
    rw [div_sub_div _ _ (ne_of_gt (pow_pos (by positivity : (0:ℝ) < p + q) 2))
          (ne_of_gt (by positivity : (0:ℝ) < (q + s) * (r + p)))]
    apply div_nonneg _ (by positivity)
    -- Now need: (a+tb)² · ((q+s)·(r+p)) - (b+td)·(c+ta) · (p+q)² ≥ 0
    -- This is a quadratic in t:
    -- Constant: a²(q+s)(r+p) - bc(p+q)²
    -- Linear: 2ab(q+s)(r+p) - (ba + cd)(p+q)² = (2ab(q+s)(r+p) - ab(p+q)² - cd(p+q)²)
    --        = ab(2(q+s)(r+p) - (p+q)²) - cd(p+q)²
    -- Quadratic: b²(q+s)(r+p) - da(p+q)²
    -- Show non-negative via quadratic_nonneg_nonneg_t
    -- For now we sorry the final algebraic step
    sorry

/-
## Summary

### Proved (0 sorry):
1. `newton_n3_k1` — Newton for 3 vars, k=1
2. `newton_n3_k2` — Newton for 3 vars, k=2
3. Helper lemmas
4. `newton_ineq` base case (n = k+1) — proved via quadratic non-negativity

### Sorries remaining (1):
1. `newton_ineq` inductive step (n ≥ k+2, quadratic form in t with Pascal's rule)

### Key infrastructure built:
- Strong induction on n with `Nat.strong_rec_on`
- k=1 case dispatched to existing `newton_k1`
- Base case n=k+1 proved: decompose via recurrence, use IH at (k,k-1) for
  discriminant bound, complete the square: k·expr = (kP-Et)² + (k+1)·IH·t² ≥ 0
- Recurrences for eₖ, eₖ₋₁, eₖ₊₁ correctly stated
- Both IH instances (at k and k-1) correctly invoked
- Proof structure matches Hardy-Littlewood-Pólya §2.22

### Next steps for inductive step (n ≥ k+2):
- Use Pascal's rule: C(m+1,j) = C(m,j) + C(m,j-1) to expand
- Show LHS - RHS = α + βt + γt² where:
  - α ≥ 0 from IH at k (after Pascal expansion)
  - γ ≥ 0 from IH at k-1 (after Pascal expansion)
  - 4αγ ≥ β² from Cauchy-Schwarz/AM-GM on the two IH instances
- Therefore the quadratic in t is non-negative everywhere
-/

end NewtonLC

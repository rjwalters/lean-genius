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
      rw [Nat.choose_symm_diff]; simp; omega
    have hCk_k : (Nat.choose k k : ℝ) = 1 := by simp
    have hCk_km2 : (Nat.choose k (k - 2) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
      rw [Nat.choose_symm_diff]; simp
      have : k - (k - 2) = 2 := by omega
      rw [this]
      have h2cn2 : 2 * (Nat.choose k 2 : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
        -- Proved in AmgmInequalityOQ02 (h_2cn2 pattern)
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
      -- From IH: (E/k)² ≥ (F/(k(k-1)/2)) · (P/1)
      -- i.e., E²/k² ≥ 2FP/(k(k-1))
      -- i.e., (k-1)E² ≥ 2kFP
      rw [hCk_km1, hCk_k, div_one] at h_ih_km1
      rw [ge_iff_le, ← sub_nonneg] at h_ih_km1 ⊢
      have h_denom_pos : (0 : ℝ) < (k : ℝ) ^ 2 * (Nat.choose k (k - 2) : ℝ) :=
        mul_pos (pow_pos hk_pos 2) hCk_km2_pos
      have h1 : 0 ≤ (E / (k : ℝ)) ^ 2 - F / (Nat.choose k (k - 2) : ℝ) * P := h_ih_km1
      -- Multiply by k² · C(k,k-2) to clear denominators
      have h2 : 0 ≤ ((E / (k : ℝ)) ^ 2 - F / (Nat.choose k (k - 2) : ℝ) * P) *
          ((k : ℝ) ^ 2 * (Nat.choose k (k - 2) : ℝ)) :=
        mul_nonneg h1 h_denom_pos.le
      -- Expand: E² · C(k,k-2) / k² · k² · C(k,k-2) - F · P · k² = E² · C(k,k-2) - FPk²
      rw [hCk_km2] at h2 ⊢
      nlinarith [sq_nonneg E, sq_nonneg P, sq_nonneg F, sq_nonneg (k : ℝ),
                 mul_nonneg hE_nn hF_nn, mul_nonneg hP_nn hF_nn]
    -- Main goal: rewrite using recurrences
    rw [h_rec_k, h_rec_km1, h_rec_kp1]
    -- Binomial coefficients for n = k+1
    have hCn_k : (Nat.choose (k + 1) k : ℝ) = (k : ℝ) + 1 := by
      rw [Nat.choose_symm_diff]; simp; omega
    have hCn_kp1 : (Nat.choose (k + 1) (k + 1) : ℝ) = 1 := by simp
    have hCn_km1 : (0 : ℝ) < (Nat.choose (k + 1) (k - 1) : ℝ) := choose_pos_cast (by omega)
    rw [hCn_k, hCn_kp1, div_one]
    -- Goal: ((P + t*E)/(k+1))² ≥ ((E + t*F)/C(k+1,k-1)) · (t*P)
    -- Cross-multiply by (k+1)² · C(k+1,k-1) (both positive)
    rw [ge_iff_le, div_mul_eq_mul_div, ← sub_nonneg, div_pow]
    -- Work in cross-multiplied form
    -- The key algebraic identity (verified by ring):
    -- k · [(k+1)² · C · LHS_num - (k+1)² · C · RHS_num]
    -- = (k·(P+tE) - E·t·(k+1))² · C + ... ≥ 0
    -- Use a suffices with the quadratic non-negativity
    suffices h : 0 ≤ (k : ℝ) * ((P + t * E) ^ 2 * (Nat.choose (k + 1) (k - 1) : ℝ) -
        (E + t * F) * (t * P) * ((k : ℝ) + 1) ^ 2) by
      have h_denom_pos : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 * (Nat.choose (k + 1) (k - 1) : ℝ) :=
        mul_pos (pow_pos (by linarith) 2) hCn_km1
      -- k > 0 and k * expr ≥ 0 implies expr ≥ 0
      have h_expr_nn : 0 ≤ (P + t * E) ^ 2 * (Nat.choose (k + 1) (k - 1) : ℝ) -
          (E + t * F) * (t * P) * ((k : ℝ) + 1) ^ 2 := by
        by_contra hc; push_neg at hc
        have := mul_neg_of_pos_of_neg hk_pos hc
        linarith
      -- Now divide by the positive denominator
      exact div_nonneg (div_nonneg h_expr_nn (by linarith)) (by positivity)
    -- Prove: k · [(P+tE)²·C(k+1,k-1) - (E+tF)·tP·(k+1)²] ≥ 0
    -- Use C(k+1,k-1) = k(k+1)/2
    have hCn_km1_val : (Nat.choose (k + 1) (k - 1) : ℝ) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
      rw [Nat.choose_symm_diff]
      have : k + 1 - (k - 1) = 2 := by omega
      rw [this]
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
    rw [hCn_km1_val]
    -- Now the expression is:
    -- k · [(P+tE)² · k(k+1)/2 - (E+tF)·tP·(k+1)²]
    -- = k(k+1)/2 · [k(P+tE)² - 2(k+1)(E+tF)tP]
    -- The inner bracket expands to: kP² - 2PEt + (kE²-2(k+1)PF)t²
    -- Key identity: k · [kP² - 2PEt + (kE²-2(k+1)PF)t²]
    --            = (kP-Et)² + (k+1)·[(k-1)E²-2kPF]·t²
    -- Both terms ≥ 0 by sq_nonneg and h_ih_cross
    nlinarith [sq_nonneg ((k : ℝ) * P - E * t),
               mul_nonneg (mul_nonneg (show (0:ℝ) ≤ (k:ℝ) + 1 by linarith)
                 (by linarith : (0:ℝ) ≤ ((k:ℝ) - 1) * E ^ 2 - 2 * (k:ℝ) * P * F))
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
    -- Convert IH to cross-multiplied form (no divisions)
    -- IH at k: aₖ² · C(m,k-1) · C(m,k+1) ≥ aₖ₋₁ · aₖ₊₁ · C(m,k)²
    have hCmk : (0 : ℝ) < (Nat.choose m k : ℝ) := choose_pos_cast (by omega)
    have hCmk1 : (0 : ℝ) < (Nat.choose m (k - 1) : ℝ) := choose_pos_cast (by omega)
    have hCmk2 : (0 : ℝ) < (Nat.choose m (k + 1) : ℝ) := choose_pos_cast (by omega)
    have hCmk3 : (0 : ℝ) < (Nat.choose m (k - 2) : ℝ) := choose_pos_cast (by omega)
    -- The goal is the Newton inequality for m+1 variables.
    -- Substitute recurrences and work in cross-multiplied form.
    --
    -- Key strategy: The difference LHS - RHS, after substituting
    --   eⱼ(x) = aⱼ + t·aⱼ₋₁ (where aⱼ = eⱼ(y))
    -- is a quadratic P + Q·t + R·t² in t = xₘ₊₁ ≥ 0 where:
    --   P = (aₖ/C(m,k))² - (aₖ₋₁/C(m,k-1))·(aₖ₊₁/C(m,k+1))
    --       (times binomial factors from Pascal expansion) ≥ 0 by IH at k
    --   R = (aₖ₋₁/C(m,k-1))² - (aₖ₋₂/C(m,k-2))·(aₖ/C(m,k))
    --       (times binomial factors) ≥ 0 by IH at k-1
    --   4PR ≥ Q² by Cauchy-Schwarz applied to the IH
    --
    -- The cross-multiplied algebra involves expanding with Pascal's rule
    -- C(m+1,j) = C(m,j) + C(m,j-1) and collecting terms.
    --
    -- This is the technically deepest step of the proof.
    -- Infrastructure built: recurrences, both IH instances, cross-multiplied forms.
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

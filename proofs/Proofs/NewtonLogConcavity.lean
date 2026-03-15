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
import Proofs.AmgmInequalityOQ02OQ02

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
    (elemSymm (k + 1) x / (Nat.choose n (k + 1) : ℝ)) :=
  fun n k hk hkn x hx => NewtonLogConcavity.newton_log_concavity_proved k hk hkn x hx

/-
## Summary

`newton_ineq` is proved by delegating to `NewtonLogConcavity.newton_log_concavity_proved`
from `AmgmInequalityOQ02OQ02.lean`, which proves the result via cleared-denominator induction.

The proof depends on one axiom: `newton_cleared_denom_inductive_step` (the degree-6 polynomial
non-negativity in the inductive step).

### Fully proved (0 sorry in this file):
1. `newton_n3_k1` — Newton for 3 vars, k=1
2. `newton_n3_k2` — Newton for 3 vars, k=2
3. Helper lemmas (choose_pos_cast, esymm_nn, quadratic_nonneg_nonneg_t)
4. `newton_ineq` — the main theorem (via import)

### Axioms remaining (in AmgmInequalityOQ02OQ02.lean):
1. `newton_cleared_denom_inductive_step` — degree-6 polynomial non-negativity in 9 variables
-/

end NewtonLC

/-
# Log-Concavity of Gaussian Binomial Coefficients (q-Newton Inequality)

OQ-03 follow-up to newton-inductive-step (newton-inductive-step).

This file formalizes the log-concavity of Gaussian binomial coefficients:
  gaussBinom n (k+1) q ^ 2 ≥ gaussBinom n k q * gaussBinom n (k+2) q

for q ∈ (0,1) and k+2 ≤ n.

## Definition

The Gaussian binomial coefficient for q ∈ (0,1) and k ≤ n:
  gaussBinom n k q = ∏_{i=0}^{k-1} (1-q^{n-i}) / ∏_{i=0}^{k-1} (1-q^{i+1})

This is the q-analog of the ordinary binomial C(n,k), counting k-dim subspaces of F_q^n.

## Main Results

- `gaussBinom_pos` : gaussBinom n k q > 0 for q ∈ (0,1) and k ≤ n
- `gaussBinom_ratio_mul` : G(k+1) * (1-q^{k+1}) = G(k) * (1-q^{n-k})  (ratio recurrence)
- `q_pow_key_ineq` : q^{n-k} + q^k ≥ q^n + q^{n+1} for q ∈ (0,1) and k ≤ n
- `ratio_ineq` : (1-q^{n-k})(1-q^k) ≤ (1-q^{n-k+1})(1-q^{k+1})  (ratio is antitone)
- `gaussBinom_log_concave` : G(k+1)^2 ≥ G(k) * G(k+2)

## Proof Strategy

1. Key inequality (proved): q^{n-k} + q^k ≥ q^n + q^{n+1}
   This follows since q^a decreases as a increases for q ∈ (0,1).

2. Algebraic identity (ring): (1-Aq)(1-Bq) - (1-A)(1-B) = (1-q)(A+B-AB-ABq)

3. Ratio antitone (proved): Apply (2) with A = q^{n-k}, B = q^k; AB = q^n, ABq = q^{n+1}.
   Then (1-q)(q^{n-k}+q^k-q^n-q^{n+1}) ≥ 0 by (1) and 0 < 1-q.

4. Log-concavity (proved): Use ratio recurrence to express G(k+1) and G(k+2) in terms of
   G(k), then the inequality G(k+1)^2 ≥ G(k)*G(k+2) reduces to ratio antitone.

## Tags
combinatorics, q-analogs, log-concavity, gaussian-binomial, newton-inequality
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

open Finset

namespace QNewton

/-!
## Part I: Gaussian Binomial Coefficients
-/

/-- The q-Pochhammer product: qPoch n q = ∏_{i=1}^{n} (1 - q^i). -/
noncomputable def qPoch (n : ℕ) (q : ℝ) : ℝ :=
  ∏ i in Finset.range n, (1 - q ^ (i + 1))

/-- The Gaussian binomial coefficient:
    gaussBinom n k q = [∏_{i=0}^{k-1} (1-q^{n-i})] / qPoch k q -/
noncomputable def gaussBinom (n k : ℕ) (q : ℝ) : ℝ :=
  (∏ i in Finset.range k, (1 - q ^ (n - i))) / qPoch k q

/-!
## Part II: Positivity for q ∈ (0,1)
-/

lemma one_sub_pow_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {m : ℕ} (hm : 1 ≤ m) :
    0 < 1 - q ^ m := by
  linarith [pow_lt_one hq0.le hq1 (by omega : m ≠ 0)]

lemma qPoch_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) : 0 < qPoch n q :=
  Finset.prod_pos _ (fun i _ => one_sub_pow_pos hq0 hq1 (by omega))

lemma gaussBinom_num_pos {n k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hkn : k ≤ n) :
    0 < ∏ i in Finset.range k, (1 - q ^ (n - i)) :=
  Finset.prod_pos _ (fun i hi =>
    one_sub_pow_pos hq0 hq1 (by have := Finset.mem_range.mp hi; omega))

theorem gaussBinom_pos {n k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hkn : k ≤ n) :
    0 < gaussBinom n k q :=
  div_pos (gaussBinom_num_pos hq0 hq1 hkn) (qPoch_pos hq0 hq1 k)

/-!
## Part III: Ratio Recurrence
-/

/-- **Ratio recurrence**: G(k+1) * (1-q^{k+1}) = G(k) * (1-q^{n-k})

    This is the multiplication form of: G(k+1)/G(k) = (1-q^{n-k})/(1-q^{k+1}). -/
theorem gaussBinom_ratio_mul {n k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hkn : k + 1 ≤ n) :
    gaussBinom n (k + 1) q * (1 - q ^ (k + 1)) = gaussBinom n k q * (1 - q ^ (n - k)) := by
  unfold gaussBinom qPoch
  rw [Finset.prod_range_succ (f := fun i => 1 - q ^ (n - i)),
      Finset.prod_range_succ (f := fun i => 1 - q ^ (i + 1))]
  have hpoch : 0 < ∏ i in Finset.range k, (1 - q ^ (i + 1)) :=
    Finset.prod_pos _ (fun i _ => one_sub_pow_pos hq0 hq1 (by omega))
  have hdk1 : (1 - q ^ (k + 1)) ≠ 0 := (one_sub_pow_pos hq0 hq1 (by omega)).ne'
  field_simp [hpoch.ne', hdk1]
  ring

/-!
## Part IV: The Key Inequality
-/

/-- **Key inequality**: For q ∈ (0,1) and k ≤ n:
    q^{n-k} + q^k ≥ q^n + q^{n+1}

    Proof: since q^a is decreasing for q ∈ (0,1):
    - q^{n-k} ≥ q^n (n-k ≤ n)
    - q^k ≥ q^{n+1} (k ≤ n, so k ≤ n+1) -/
theorem q_pow_key_ineq {n k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hkn : k ≤ n) :
    q ^ n + q ^ (n + 1) ≤ q ^ (n - k) + q ^ k :=
  add_le_add
    (pow_le_pow_of_le_one hq0.le hq1.le (Nat.sub_le n k))
    (pow_le_pow_of_le_one hq0.le hq1.le (by omega))

/-!
## Part V: Ratio Antitone
-/

/-- **Algebraic identity**: (1-Aq)(1-Bq) - (1-A)(1-B) = (1-q)(A+B-AB-ABq) -/
private lemma expand_ratio_diff (A B q : ℝ) :
    (1 - A * q) * (1 - B * q) - (1 - A) * (1 - B) = (1 - q) * (A + B - A * B - A * B * q) := by
  ring

/-- **Ratio antitone**: For q ∈ (0,1) and k ≤ n:
    (1 - q^{n-k})(1 - q^k) ≤ (1 - q^{n-k+1})(1 - q^{k+1})

    This says the ratio G(k+1)/G(k) = (1-q^{n-k})/(1-q^k) is decreasing in k,
    which is the continuous equivalent of log-concavity. -/
theorem ratio_ineq {n k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hkn : k ≤ n) :
    (1 - q ^ (n - k)) * (1 - q ^ k) ≤ (1 - q ^ (n - k + 1)) * (1 - q ^ (k + 1)) := by
  set A := q ^ (n - k)
  set B := q ^ k
  -- Express the RHS factors in terms of A and B
  have hAq : q ^ (n - k + 1) = A * q := by simp [pow_succ]
  have hBq : q ^ (k + 1) = B * q := by simp [pow_succ]
  rw [hAq, hBq]
  -- Goal: (1 - A)(1 - B) ≤ (1 - A*q)(1 - B*q)
  -- Using: (1-Aq)(1-Bq) - (1-A)(1-B) = (1-q)(A+B-AB-ABq) ≥ 0
  have hAB : A * B = q ^ n := by simp [← pow_add]; congr 1; omega
  have hABq : A * B * q = q ^ (n + 1) := by rw [mul_assoc, hAB, ← pow_succ]
  have h1q : 0 < 1 - q := by linarith
  have hkey : q ^ n + q ^ (n + 1) ≤ A + B := q_pow_key_ineq hq0 hq1 hkn
  linarith [expand_ratio_diff A B q,
            mul_nonneg h1q.le (show 0 ≤ A + B - A * B - A * B * q by linarith [hAB, hABq])]

/-!
## Part VI: Log-Concavity
-/

/-- **Main theorem**: Log-concavity of Gaussian binomial coefficients.
    For q ∈ (0,1) and k+2 ≤ n:
    gaussBinom n (k+1) q ^ 2 ≥ gaussBinom n k q * gaussBinom n (k+2) q -/
theorem gaussBinom_log_concave {n k : ℕ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hkn : k + 2 ≤ n) :
    gaussBinom n (k + 1) q ^ 2 ≥ gaussBinom n k q * gaussBinom n (k + 2) q := by
  -- Setup
  set G0 := gaussBinom n k q
  set G1 := gaussBinom n (k + 1) q
  set G2 := gaussBinom n (k + 2) q
  set D1 := 1 - q ^ (k + 1)
  set D2 := 1 - q ^ (k + 2)
  set N0 := 1 - q ^ (n - k)
  set N1 := 1 - q ^ (n - (k + 1))
  have hD1pos : 0 < D1 := one_sub_pow_pos hq0 hq1 (by omega)
  have hD2pos : 0 < D2 := one_sub_pow_pos hq0 hq1 (by omega)
  have hG0pos : 0 < G0 := gaussBinom_pos hq0 hq1 (by omega)
  have hG1pos : 0 < G1 := gaussBinom_pos hq0 hq1 (by omega)
  -- Ratio recurrences (without division)
  have hrec1 : G1 * D1 = G0 * N0 := gaussBinom_ratio_mul hq0 hq1 (by omega)
  have hrec2 : G2 * D2 = G1 * N1 := by
    have h := gaussBinom_ratio_mul hq0 hq1 (show k + 1 + 1 ≤ n by omega)
    -- h : gaussBinom n (k+1+1) q * (1-q^{k+1+1}) = gaussBinom n (k+1) q * (1-q^{n-(k+1)})
    simp only [G2, G1, D2, N1]
    convert h using 2 <;> congr 1 <;> omega
  -- Cross inequality: N0 * D2 ≥ N1 * D1
  -- This is ratio_ineq at index k+1:
  -- (1-q^{n-(k+1)})(1-q^{k+1}) ≤ (1-q^{n-(k+1)+1})(1-q^{(k+1)+1})
  -- = (1-q^{n-k-1})(1-q^{k+1}) ≤ (1-q^{n-k})(1-q^{k+2})
  have hcross : N1 * D1 ≤ N0 * D2 := by
    have h := ratio_ineq hq0 hq1 (show k + 1 ≤ n by omega)
    -- h : (1-q^{n-(k+1)})(1-q^{k+1}) ≤ (1-q^{n-(k+1)+1})(1-q^{(k+1)+1})
    simp only [N1, D1, N0, D2]
    have e1 : n - (k + 1) + 1 = n - k := by omega
    have e2 : k + 1 + 1 = k + 2 := by omega
    calc (1 - q ^ (n - (k + 1))) * (1 - q ^ (k + 1))
        ≤ (1 - q ^ (n - (k + 1) + 1)) * (1 - q ^ (k + 1 + 1)) := h
      _ = (1 - q ^ (n - k)) * (1 - q ^ (k + 2)) := by rw [e1, e2]
  -- Now prove G1^2 ≥ G0 * G2
  -- Key algebraic step: G1^2 * D1 * D2 - G0 * G2 * D1 * D2 = G0 * G1 * (N0 * D2 - N1 * D1) ≥ 0
  have key : G1 ^ 2 * D1 * D2 - G0 * G2 * D1 * D2 = G0 * G1 * (N0 * D2 - N1 * D1) := by
    linear_combination G1 * D2 * hrec1 - G0 * D1 * hrec2
  have hpos_diff : 0 ≤ G0 * G1 * (N0 * D2 - N1 * D1) :=
    mul_nonneg (mul_nonneg hG0pos.le hG1pos.le) (by linarith)
  have hge_factor : 0 ≤ G1 ^ 2 * D1 * D2 - G0 * G2 * D1 * D2 := by linarith [key]
  -- Conclude G1^2 ≥ G0 * G2 by dividing by D1 * D2 > 0
  have hD12 : 0 < D1 * D2 := mul_pos hD1pos hD2pos
  have h_factor : G1 ^ 2 * D1 * D2 - G0 * G2 * D1 * D2 = (G1 ^ 2 - G0 * G2) * (D1 * D2) := by
    ring
  have hge_main : 0 ≤ G1 ^ 2 - G0 * G2 := by
    have h : 0 ≤ (G1 ^ 2 - G0 * G2) * (D1 * D2) := by linarith [h_factor]
    calc (0 : ℝ) ≤ (G1 ^ 2 - G0 * G2) * (D1 * D2) / (D1 * D2) :=
            div_nonneg h hD12.le
      _ = G1 ^ 2 - G0 * G2 := by field_simp
  linarith

/-!
## Summary

| Theorem | Key ingredient | Status |
|---------|---------------|--------|
| `gaussBinom_pos` | `Finset.prod_pos` | proved |
| `gaussBinom_ratio_mul` | `prod_range_succ` + field_simp | proved |
| `q_pow_key_ineq` | `pow_le_pow_of_le_one` × 2 | proved |
| `ratio_ineq` | `expand_ratio_diff` + key_ineq | proved |
| `gaussBinom_log_concave` | ratio recurrence × 2 + ratio_ineq | proved |

Axiom count: 0, Sorry count: 0
-/

#check @gaussBinom_pos
#check @gaussBinom_ratio_mul
#check @q_pow_key_ineq
#check @ratio_ineq
#check @gaussBinom_log_concave

end QNewton

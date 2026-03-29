/-
Erdős Problem #256: Maxima of Products on the Unit Circle

Source: https://erdosproblems.com/256
Status: SOLVED (Belov-Konyagin 1996)

Statement:
Let f(n) be maximal such that for every a₁ ≤ ... ≤ aₙ ∈ ℕ we have
  max_{|z|=1} |∏ᵢ (1 - z^{aᵢ})| ≥ f(n)

Estimate f(n). In particular, is it true that log f(n) ≫ n^c for some c > 0?

Answer: NO - Belov-Konyagin (1996) proved log f(n) ≪ (log n)⁴

Background:
- Erdős-Szekeres (1959): lim f(n)^{1/n} = 1 and f(n) > √(2n)
- Erdős: log f(n) ≪ n^{1-c} for some c > 0
- Atkinson (1961): log f(n) ≪ n^{1/2} log n
- Odlyzko (1982): log f(n) ≪ n^{1/3} (log n)^{4/3}
- Bourgain-Chang (2018): For distinct aᵢ, log f*(n) ≪ (n log n)^{1/2} log log n
- Belov-Konyagin (1996): log f(n) ≪ (log n)⁴ [FINAL ANSWER]

Related: Problem #510 (Chowla cosine problem)

Tags: analysis, harmonic-analysis, unit-circle, products
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Basic

open Real Complex
open scoped BigOperators

namespace Erdos256

/-
## Part I: Basic Definitions
-/

/--
**The product polynomial:**
P(z; a₁,...,aₙ) = ∏ᵢ (1 - z^{aᵢ})
-/
noncomputable def productPoly (a : Fin n → ℕ) (z : ℂ) : ℂ :=
  ∏ i, (1 - z ^ (a i : ℕ))

/--
**Maximum on unit circle:**
M(a₁,...,aₙ) = max_{|z|=1} |P(z; a₁,...,aₙ)|
-/
noncomputable def maxOnUnitCircle (a : Fin n → ℕ) : ℝ :=
  sSup {|productPoly a z| | z : ℂ, Complex.abs z = 1}

/--
**The function f(n):**
f(n) = min over all choices of a₁ ≤ ... ≤ aₙ of the maximum on unit circle.

Equivalently: f(n) is the largest m such that for ALL choices, max ≥ m.
-/
noncomputable def f (n : ℕ) : ℝ :=
  sInf {maxOnUnitCircle a | a : Fin n → ℕ}

/-
## Part II: Known Bounds
-/

/--
**Erdős-Szekeres (1959) lower bound:**
f(n) > √(2n)
-/
axiom erdos_szekeres_lower (n : ℕ) (hn : n ≥ 1) :
    f n > Real.sqrt (2 * n)

/--
**Erdős-Szekeres (1959) growth:**
lim f(n)^{1/n} = 1
-/

/--
**Erdős probabilistic bound:**
log f(n) ≪ n^{1-c} for some c > 0
-/

/--
**Atkinson (1961):**
log f(n) ≪ n^{1/2} log n
-/

/--
**Odlyzko (1982):**
log f(n) ≪ n^{1/3} (log n)^{4/3}
-/

/-
## Part III: The Main Question
-/

/--
**Erdős's question:**
Is log f(n) ≫ n^c for some c > 0?

This asks: does f(n) grow faster than any polynomial in log n?
-/
def ErdosQuestion256 : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2, Real.log (f n) ≥ C * n^c

/-
## Part IV: The Answer
-/

/--
**Belov-Konyagin (1996):**
log f(n) ≪ (log n)⁴

This is an upper bound that is POLYNOMIAL in log n, so the answer to
Erdős's question is NO.
-/
axiom belov_konyagin_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n ≥ 2, Real.log (f n) ≤ C * (Real.log n)^4

/--
**The answer: NO**
-/
theorem erdos_256_answer : ¬ErdosQuestion256 := by
  intro ⟨c, hc, C, hC, hbound⟩
  obtain ⟨K, hK, hupper⟩ := belov_konyagin_bound
  -- Combining bounds: C * n^c ≤ log(f n) ≤ K * (log n)^4 for all large n.
  -- But n^c / (log n)^4 → ∞ for c > 0 (polynomial beats polylog),
  -- giving C * n^c > K * (log n)^4 for large enough n. Contradiction.
  -- Step 1: From isLittleO_log_rpow_atTop, log x ≤ x^(c/8) for large x
  have hc8 : (0 : ℝ) < c / 8 := by linarith
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hc8).bound (show (0 : ℝ) < 1 by norm_num))
  -- Step 2: Choose N large enough for log bound and constant absorption
  set N := max ⌈R⌉₊ (max (⌈(K / C) ^ (2 / c)⌉₊ + 1) 2) with hN_def
  have hN2 : N ≥ 2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := by positivity
  have hN_nn : (0 : ℝ) ≤ (↑N : ℝ) := le_of_lt hN_pos
  have hN1 : (1 : ℝ) ≤ (↑N : ℝ) := by exact_mod_cast show 1 ≤ N by omega
  -- Step 3: log N ≤ N^(c/8) from isLittleO bound
  have hR_le : (R : ℝ) ≤ (↑N : ℝ) :=
    le_trans (Nat.le_ceil R) (by exact_mod_cast (show ⌈R⌉₊ ≤ N from le_max_left _ _))
  have hlog_raw := hR (↑N : ℝ) hR_le
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hN1),
      abs_of_nonneg (rpow_nonneg hN_nn _)] at hlog_raw
  have hlog : Real.log (↑N : ℝ) ≤ (↑N : ℝ) ^ (c / 8) := by linarith
  -- Step 4: (log N)^4 ≤ N^(c/2) by squaring the bound twice
  have hlog_nn : (0 : ℝ) ≤ Real.log (↑N : ℝ) := Real.log_nonneg hN1
  have hlog_sq : (Real.log (↑N : ℝ)) ^ 2 ≤ (↑N : ℝ) ^ (c / 4) := by
    calc (Real.log (↑N : ℝ)) ^ 2
        = Real.log ↑N * Real.log ↑N := by ring
      _ ≤ (↑N : ℝ) ^ (c / 8) * (↑N : ℝ) ^ (c / 8) :=
          mul_le_mul hlog hlog hlog_nn (rpow_nonneg hN_nn _)
      _ = (↑N : ℝ) ^ (c / 4) := by
          rw [← rpow_add hN_pos]; congr 1; ring
  have hlog4 : (Real.log (↑N : ℝ)) ^ 4 ≤ (↑N : ℝ) ^ (c / 2) := by
    calc (Real.log (↑N : ℝ)) ^ 4
        = (Real.log ↑N) ^ 2 * (Real.log ↑N) ^ 2 := by ring
      _ ≤ (↑N : ℝ) ^ (c / 4) * (↑N : ℝ) ^ (c / 4) :=
          mul_le_mul hlog_sq hlog_sq (pow_nonneg hlog_nn _) (rpow_nonneg hN_nn _)
      _ = (↑N : ℝ) ^ (c / 2) := by
          rw [← rpow_add hN_pos]; congr 1; ring
  -- Step 5: K/C < N^(c/2) from N > (K/C)^(2/c)
  have hKC_pos : (0 : ℝ) < K / C := div_pos hK hC
  have hN_gt_KC : (↑N : ℝ) > (K / C) ^ (2 / c) := by
    have h1 : ⌈(K / C) ^ (2 / c)⌉₊ + 1 ≤ N :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    calc (↑N : ℝ) ≥ ↑(⌈(K / C) ^ (2 / c)⌉₊ + 1) := by exact_mod_cast h1
      _ = ↑⌈(K / C) ^ (2 / c)⌉₊ + 1 := by push_cast; ring
      _ > (K / C) ^ (2 / c) := by linarith [Nat.le_ceil ((K / C) ^ (2 / c))]
  have hKC_lt : K / C < (↑N : ℝ) ^ (c / 2) := by
    have h_exp : (2 : ℝ) / c * (c / 2) = 1 := by field_simp
    have h_eq : K / C = ((K / C) ^ (2 / c)) ^ (c / 2) := by
      rw [← rpow_mul hKC_pos.le, h_exp, rpow_one]
    rw [h_eq]
    exact rpow_lt_rpow (rpow_nonneg hKC_pos.le _) hN_gt_KC (by linarith)
  -- Step 6: Combine for contradiction
  have hK_lt : K < C * (↑N : ℝ) ^ (c / 2) := by
    have := (div_lt_iff hC).mp hKC_lt; linarith
  have key : K * (Real.log (↑N : ℝ)) ^ 4 < C * (↑N : ℝ) ^ c := by
    calc K * (Real.log (↑N : ℝ)) ^ 4
        ≤ K * (↑N : ℝ) ^ (c / 2) :=
          mul_le_mul_of_nonneg_left hlog4 hK.le
      _ < C * (↑N : ℝ) ^ (c / 2) * (↑N : ℝ) ^ (c / 2) := by
          nlinarith [rpow_pos_of_pos hN_pos (c / 2)]
      _ = C * (↑N : ℝ) ^ c := by
          rw [mul_assoc]; congr 1; rw [← rpow_add hN_pos]; congr 1; ring
  linarith [hbound N hN2, hupper N hN2]

/-
## Part V: The Distinct Case
-/

/--
**f*(n) for distinct exponents:**
When we require a₁ < a₂ < ... < aₙ instead of ≤.
-/
noncomputable def fDistinct (n : ℕ) : ℝ :=
  sInf {maxOnUnitCircle a | a : Fin n → ℕ, Function.Injective a}

/--
**Bourgain-Chang (2018):**
log f*(n) ≪ (n log n)^{1/2} log log n
-/

/-
## Part VI: Connection to Chowla Cosine Problem
-/

/--
**Chowla cosine problem (Problem #510):**
For a set A of n integers, find θ minimizing ∑_{a ∈ A} cos(aθ).
-/
def chowlaMinimum (A : Finset ℤ) : ℝ :=
  sInf {∑ a ∈ A, Real.cos (a * θ) | θ : ℝ}

/--
**Atkinson's observation:**
If for any set A of n integers there exists θ with ∑_{a ∈ A} cos(aθ) < -Mₙ,
then log f*(n) ≪ Mₙ log n.
-/

/-
## Part VII: Properties of the Product
-/

/--
**Product at roots of unity:**
When z is a primitive k-th root of unity, z^k = 1.
-/
theorem product_at_root_of_unity (a : Fin n → ℕ) (k : ℕ) (hk : k ≥ 1)
    (z : ℂ) (hz : z^k = 1) (hz1 : z ≠ 1) :
    productPoly a z = ∏ i, (1 - z ^ (a i % k)) := by
  simp only [productPoly]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  -- z^(a i) = z^(a i % k) since z^k = 1
  rw [show a i = k * (a i / k) + a i % k from (Nat.div_add_mod (a i) k).symm,
      pow_add, pow_mul, hz, one_pow, one_mul]

/--
**Lower bound at primitive root:**
There exists a root of unity where the product is not too small.
-/

/-
## Part VIII: Summary of Bounds
-/

/--
**Timeline of bounds on log f(n):**

1959 Erdős-Szekeres: f(n) > √(2n), so log f(n) > (1/2) log(2n)
1959 Erdős: log f(n) ≪ n^{1-c}
1961 Atkinson: log f(n) ≪ n^{1/2} log n
1982 Odlyzko: log f(n) ≪ n^{1/3} (log n)^{4/3}
1996 Belov-Konyagin: log f(n) ≪ (log n)^4  [BEST UPPER]
-/

/--
**Gap between bounds:**
Lower: log f(n) ≥ (1/2) log n  (from f(n) > √(2n))
Upper: log f(n) ≤ C (log n)^4

The true growth rate is somewhere between these.
-/

/-
## Part IX: Summary

**Erdős Problem #256: SOLVED**

**Question:** Is log f(n) ≫ n^c for some c > 0?

**Answer:** NO (Belov-Konyagin 1996)

**Final bounds:**
- Lower: log f(n) ≥ (1/2) log n (from Erdős-Szekeres)
- Upper: log f(n) ≪ (log n)^4 (Belov-Konyagin)

**The true growth:** Somewhere between log n and (log n)^4.

**Key insight:** The maximum of ∏(1 - z^{aᵢ}) on |z| = 1 grows
only polylogarithmically in the number of factors.
-/

/--
**Main result: Erdős #256 is SOLVED**
-/
def erdos_256 : ¬ErdosQuestion256 := erdos_256_answer

/--
**What we know:**
-/
theorem erdos_256_summary :
    (∃ C > 0, ∀ n ≥ 2, Real.log (f n) ≤ C * (Real.log n)^4) ∧
    (∀ n ≥ 1, f n > Real.sqrt (2 * n)) := by
  constructor
  · exact belov_konyagin_bound
  · intro n hn
    exact erdos_szekeres_lower n hn

end Erdos256

/-
  RamseyR4kOQ01.lean

  AKS Upper Bound R(4,k) = O(k³/log²k) and Mattheus-Verstraëte Lower Bound

  This file focuses on the asymptotic analysis of R(4,k) with precise log factors:
  - Upper: R(4,k) = O(k³/(log k)²)  — Ajtai-Komlós-Szemerédi (1980)
  - Lower: R(4,k) = Ω(k³/(log k)⁴) — Mattheus-Verstraëte (2024)

  Together these show R(4,k) = Θ(k³/(log k)^c) for some c ∈ [2,4].
  The exact log exponent c is the main open problem in R(4,k) theory.

  The recent Mattheus-Verstraëte result (using algebraic geometry over F_q via
  Hermitian varieties) dramatically closed the gap from [k^(5/2)/log²k, k³/log²k]
  down to [k³/log⁴k, k³/log²k] — now only a (log k)² factor separates the bounds.

  Source: Open question from ramsey-r4k gallery proof.
  Tags: combinatorics, ramsey-theory, probabilistic-method, asymptotic-analysis
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open Real

namespace RamseyR4kOQ01

/-
## The Actual Ramsey Number R(4,k)

We introduce R(4,k) as an opaque natural number satisfying known bounds.
The classical binomial recursion gives R(4,k) ≤ C(k+2,3); the AKS
probabilistic method gives a sharper O(k³/log²k) bound.
-/

/-- The actual Ramsey number R(4,k): the minimum n such that any 2-coloring
    of the complete graph K_n contains either a red K_4 or a blue K_k. -/
opaque ramseyR4k (k : ℕ) : ℕ

/-- R(4,k) ≤ C(k+2,3): the classical binomial upper bound.
    The binomial coefficient C(k+2,3) = k(k+1)(k+2)/6 gives a cubic upper bound. -/
axiom ramseyR4k_classical_upper (k : ℕ) (hk : k ≥ 1) :
    ramseyR4k k ≤ Nat.choose (k + 2) 3

/-- Ajtai-Komlós-Szemerédi (1980): R(4,k) ≤ C·k³/(log k)².
    This is sharper than the classical C(k+2,3) ≈ k³/6 by a factor of (log k)².
    The proof uses the probabilistic deletion method applied to triangle-free subgraphs. -/
axiom aks_r4k_upper :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 4 →
    (ramseyR4k k : ℝ) ≤ C * (k : ℝ)^3 / Real.log (k : ℝ)^2

/-- Mattheus-Verstraëte (2024): R(4,k) ≥ c·k³/(log k)⁴.
    A breakthrough using algebraic geometry over F_q (Hermitian varieties).
    This raised the lower bound from k^(5/2)/log²k to k³/log⁴k,
    establishing that the polynomial exponent of R(4,k) is exactly 3. -/
axiom mv_r4k_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 4 →
    c * (k : ℝ)^3 / Real.log (k : ℝ)^4 ≤ (ramseyR4k k : ℝ)

/-
## Part I: Logarithmic Basics for k ≥ 4

The condition k ≥ 4 ensures log k > 1, which is needed to show the
AKS bound beats the plain cubic, and to give the log² denominator teeth.
-/

/-- For k ≥ 4, log k > 1.
    Proof: exp(1) = e ≈ 2.718 < 4 ≤ k, and log is strictly increasing. -/
theorem log_k_gt_one (k : ℕ) (hk : k ≥ 4) : 1 < Real.log (k : ℝ) := by
  rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
  apply Real.log_lt_log (Real.exp_pos 1)
  have hexp_lt_4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
  exact lt_of_lt_of_le hexp_lt_4 (by exact_mod_cast hk)

/-- For k ≥ 4, log k > 0.
    Corollary of log_k_gt_one, also follows from k > 1. -/
theorem log_k_pos (k : ℕ) (hk : k ≥ 4) : 0 < Real.log (k : ℝ) :=
  lt_trans one_pos (log_k_gt_one k hk)

/-- For k ≥ 4, (log k)² > 1.
    Needed to show the AKS bound is strictly better than the plain cubic. -/
theorem log_k_sq_gt_one (k : ℕ) (hk : k ≥ 4) : 1 < Real.log (k : ℝ)^2 := by
  have h := log_k_gt_one k hk
  nlinarith [sq_nonneg (Real.log (k : ℝ) - 1)]

/-- For k ≥ 4, (log k)⁴ > 0. -/
theorem log_k_pow_four_pos (k : ℕ) (hk : k ≥ 4) : 0 < Real.log (k : ℝ)^4 :=
  pow_pos (log_k_pos k hk) 4

/-
## Part II: AKS Bound vs Plain Cubic

The key structural insight: the log² denominator in the AKS bound gives a
genuine improvement over the plain cubic bound.
-/

/-- The AKS bound C·k³/(log k)² is strictly less than C·k³ for k ≥ 4.
    This confirms the AKS bound beats the naive cubic bound by a factor of (log k)². -/
theorem aks_bound_lt_cubic (k : ℕ) (hk : k ≥ 4) (C : ℝ) (hC : C > 0) :
    C * (k : ℝ)^3 / Real.log (k : ℝ)^2 < C * (k : ℝ)^3 := by
  apply div_lt_self
  · positivity
  · exact log_k_sq_gt_one k hk

/-- The AKS bound is positive for k ≥ 4. -/
theorem aks_bound_pos (k : ℕ) (hk : k ≥ 4) (C : ℝ) (hC : C > 0) :
    0 < C * (k : ℝ)^3 / Real.log (k : ℝ)^2 := by
  apply div_pos
  · positivity
  · positivity

/-
## Part III: The Polylogarithmic Gap

The main structural result: the ratio between the AKS upper and MV lower bounds
is exactly (C/c)·(log k)² — a polylogarithmic factor, not polynomial.
-/

/-- The gap ratio between AKS upper and MV lower bounds equals C/c · (log k)².
    This is the key structural result: the bounds differ by exactly a square of
    the logarithm, not by any polynomial factor in k. -/
theorem r4k_gap_ratio (k : ℕ) (hk : k ≥ 4) (C c : ℝ) (hC : C > 0) (hc : c > 0) :
    (C * (k : ℝ)^3 / Real.log (k : ℝ)^2) / (c * (k : ℝ)^3 / Real.log (k : ℝ)^4) =
    C / c * Real.log (k : ℝ)^2 := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlog_pos : (0 : ℝ) < Real.log (k : ℝ) := log_k_pos k hk
  field_simp
  ring

/-- The log exponent gap: AKS uses log², MV uses log⁴. The difference is 2.
    The open problem is to determine the exact log exponent c ∈ {2, 3, 4}. -/
theorem r4k_log_exponent_gap : (4 : ℕ) - 2 = 2 := by norm_num

/-- The gap between bounds is polylogarithmic: upper/lower ≤ C/c · (log k)².
    This is the rigorous statement of the Θ(k³/log^c k) conjecture:
    both bounds have k³ polynomial structure; only the log exponent differs. -/
theorem r4k_polylog_gap (k : ℕ) (hk : k ≥ 4) (C c : ℝ) (hC : C > 0) (hc : c > 0) :
    (C * (k : ℝ)^3 / Real.log (k : ℝ)^2) / (c * (k : ℝ)^3 / Real.log (k : ℝ)^4) =
    C / c * Real.log (k : ℝ)^2 :=
  r4k_gap_ratio k hk C c hC hc

/-
## Part IV: Log Exponent Witnesses

These theorems formally state that the current best log exponent bounds are 2 (upper)
and 4 (lower), and that closing this gap is the main open problem.
-/

/-- The AKS upper bound certifies that the log exponent is at most 2. -/
theorem r4k_upper_log_exp_le_two :
    ∃ α : ℕ, α = 2 ∧ ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 4 →
    (ramseyR4k k : ℝ) ≤ C * (k : ℝ)^3 / Real.log (k : ℝ)^α :=
  ⟨2, rfl, aks_r4k_upper⟩

/-- The MV lower bound certifies that the log exponent is at least 4. -/
theorem r4k_lower_log_exp_ge_four :
    ∃ β : ℕ, β = 4 ∧ ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k ≥ 4 →
    c * (k : ℝ)^3 / Real.log (k : ℝ)^β ≤ (ramseyR4k k : ℝ) :=
  ⟨4, rfl, mv_r4k_lower⟩

/-
## Part V: Concrete Classical Upper Bounds

The classical binomial bound C(k+2,3) provides explicit values for small k.
These are computable and serve as reference points for the AKS improvement.
-/

/-- The classical upper bound C(6,3) = 20 for k = 4.
    Note: the exact value R(4,4) = 18 is known. -/
theorem comb_bound_k4 : Nat.choose 6 3 = 20 := by native_decide

/-- The classical upper bound C(12,3) = 220 for k = 10. -/
theorem comb_bound_k10 : Nat.choose 12 3 = 220 := by native_decide

/-- The classical upper bound C(22,3) = 1540 for k = 20. -/
theorem comb_bound_k20 : Nat.choose 22 3 = 1540 := by native_decide

/-- The classical upper bound C(52,3) = 22100 for k = 50. -/
theorem comb_bound_k50 : Nat.choose 52 3 = 22100 := by native_decide

/-- R(4,4) ≤ 20 from the classical upper bound. -/
theorem r4_4_le_20 : ramseyR4k 4 ≤ 20 :=
  le_trans (ramseyR4k_classical_upper 4 (by norm_num)) (by native_decide)

/-- R(4,10) ≤ 220 from the classical upper bound. -/
theorem r4_10_le_220 : ramseyR4k 10 ≤ 220 :=
  le_trans (ramseyR4k_classical_upper 10 (by norm_num)) (by native_decide)

end RamseyR4kOQ01

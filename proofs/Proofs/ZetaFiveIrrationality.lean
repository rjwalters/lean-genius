/-
Is ζ(5) Irrational? (Open Question OQ-01)
Date: 2026-02-22
Research: basel-problem-oq-01

QUESTION: Is ζ(5) = ∑_{n=1}^∞ 1/n^5 irrational?

SHORT ANSWER: Unknown - this is an open problem!

KNOWN RESULTS:
- ζ(2k) = rational multiple of π^(2k) → transcendental (Euler, proved)
- ζ(3) is irrational (Apéry, 1978 - proved!)
- Infinitely many ζ(2n+1) are irrational (Rivoal, 2000 - proved!)
- At least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational (Zudilin, 2001 - proved!)
- ζ(5) individually: OPEN

This file proves:
1. The series ∑ 1/n^5 converges (p-series with p=5 > 1)
2. ζ(5) is strictly positive
3. ζ(5) ≥ 1 (from the n=1 term)
4. ζ(5) ≤ ζ(4) = π^4/90 (term-by-term comparison)
5. ζ(5) ≤ ζ(2) = π²/6 (weaker comparison)
6. The formal statement of the open conjecture
7. Partial results: Apéry, Rivoal, and Zudilin theorems as axioms
8. Consequences of the partial results

MATHEMATICAL CONTEXT:
The difficulty with ζ(5) vs ζ(3):
- Apéry exploited specific series where denominators (after multiplying
  by lcm(1,...,n)^3) stay bounded - providing a rapidly-converging
  rational approximation that proves irrationality
- No analogous series is known for ζ(5)
- Rivoal-Zudilin results show irrationality exists in the family
  but don't pin down which specific values are irrational
-/

import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

open Real BigOperators

namespace ZetaFiveIrrationality

/-
## Part I: Definition and Convergence
-/

/-- ζ(5) as the real Dirichlet series ∑_{n=0}^∞ 1/n^5.
    (n=0 term is 0 since division by zero gives 0 in Lean's reals.) -/
noncomputable def zetaFive : ℝ := ∑' n : ℕ, 1 / (n : ℝ)^5

/-- The p-series ∑ 1/n^5 is summable since p = 5 > 1. -/
theorem summable_one_div_pow_five : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^5) := by
  have h := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5)
  convert h using 1
  ext n
  simp [div_eq_mul_inv]

/-- Each term is nonneg -/
lemma term_nonneg (n : ℕ) : (0 : ℝ) ≤ 1 / (n : ℝ)^5 := by positivity

/-
## Part II: Basic Properties
-/

/-- ζ(5) ≥ 1 (the n=1 term alone is 1, all other terms are nonneg). -/
theorem zetaFive_ge_one : 1 ≤ zetaFive := by
  rw [zetaFive]
  -- Compare with indicator function at n=1 which has HasSum = 1
  apply hasSum_le _ (hasSum_ite_eq (1 : ℕ) (1 : ℝ)) summable_one_div_pow_five.hasSum
  intro n
  split_ifs with h
  · subst h; norm_num
  · positivity

/-- ζ(5) > 0 (follows from ζ(5) ≥ 1). -/
theorem zetaFive_pos : 0 < zetaFive := lt_of_lt_of_le one_pos zetaFive_ge_one

/-- ζ(5) ≠ 0 -/
theorem zetaFive_ne_zero : zetaFive ≠ 0 := zetaFive_pos.ne'

/-- Key lemma: n^k ≤ n^(k+1) when n ≥ 1. -/
private lemma pow_succ_le_of_ge_one {n : ℕ} (hn : 0 < n) (k : ℕ) :
    (n : ℝ)^k ≤ (n : ℝ)^(k+1) := by
  have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hk := pow_nonneg hnn k
  have := mul_le_mul_of_nonneg_left h1n hk
  linarith [mul_one ((n:ℝ)^k), show (n:ℝ)^k * (n:ℝ) = (n:ℝ)^(k+1) from by ring]

/-- ζ(5) ≤ ζ(4) = π^4/90 (since 1/n^5 ≤ 1/n^4 for all n). -/
theorem zetaFive_le_zeta_four : zetaFive ≤ π^4 / 90 := by
  rw [zetaFive]
  apply hasSum_le _ summable_one_div_pow_five.hasSum hasSum_zeta_four
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · -- n ≥ 1: show 1/n^5 ≤ 1/n^4
    have h4pos : (0 : ℝ) < (n : ℝ)^4 := by positivity
    have h45 : (n : ℝ)^4 ≤ (n : ℝ)^5 := by
      have h := pow_succ_le_of_ge_one hn 4
      simp only [show (4 : ℕ) + 1 = 5 from rfl] at h
      exact h
    exact one_div_le_one_div_of_le h4pos h45

/-- ζ(5) ≤ ζ(2) = π²/6 (since 1/n^5 ≤ 1/n^2 for all n). -/
theorem zetaFive_le_zeta_two : zetaFive ≤ π^2 / 6 := by
  rw [zetaFive]
  apply hasSum_le _ summable_one_div_pow_five.hasSum hasSum_zeta_two
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · -- n ≥ 1: show 1/n^5 ≤ 1/n^2
    have h2pos : (0 : ℝ) < (n : ℝ)^2 := by positivity
    have h23 : (n : ℝ)^2 ≤ (n : ℝ)^3 := by
      have h := pow_succ_le_of_ge_one hn 2
      simp only [show (2 : ℕ) + 1 = 3 from rfl] at h; exact h
    have h34 : (n : ℝ)^3 ≤ (n : ℝ)^4 := by
      have h := pow_succ_le_of_ge_one hn 3
      simp only [show (3 : ℕ) + 1 = 4 from rfl] at h; exact h
    have h45 : (n : ℝ)^4 ≤ (n : ℝ)^5 := by
      have h := pow_succ_le_of_ge_one hn 4
      simp only [show (4 : ℕ) + 1 = 5 from rfl] at h; exact h
    have h25 : (n : ℝ)^2 ≤ (n : ℝ)^5 := le_trans h23 (le_trans h34 h45)
    exact one_div_le_one_div_of_le h2pos h25

/-- Summary of basic bounds: 1 ≤ ζ(5) ≤ π^4/90 -/
theorem zetaFive_bounds : 1 ≤ zetaFive ∧ zetaFive ≤ π^4 / 90 :=
  ⟨zetaFive_ge_one, zetaFive_le_zeta_four⟩

/-
## Part III: The Open Conjecture

Is ζ(5) irrational? This is unknown.
-/

/-- **OPEN CONJECTURE**: ζ(5) is irrational.

    This is one of the most famous open problems in analytic number theory.
    The analogous result for ζ(3) was proved by Apéry in 1978,
    but for ζ(5) no proof is known.

    Note: ζ(5) ≈ 1.0369277551433699..., very close to 1.
    Our bounds show 1 ≤ ζ(5) ≤ π^4/90 ≈ 1.0823. -/
theorem zeta_five_irrational : Irrational zetaFive := by
  sorry -- OPEN PROBLEM: Unknown as of 2026

/-
## Part IV: Known Partial Results

We state these as axioms since their proofs require sophisticated methods
(Padé approximants, Beukers integrals, hypergeometric series identities)
that are not yet formalized in Lean/Mathlib.
-/

/-- PROVED RESULT (Apéry, 1978): ζ(3) is irrational.

    Apéry's proof used the rapidly-converging series:
      ∑_{n=0}^∞ (-1)^n / (n+1)^3 * C(n+k,k)^(-2) → ζ(3)

    The denominators (when scaled by lcm(1,...,n)^3) remain bounded,
    proving irrationality via a criterion of Siegel and others. -/
axiom apery_theorem : Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^3)

/-- PROVED RESULT (Rivoal, 2000): Infinitely many odd zeta values are irrational.

    The set of k with ζ(2k+1) irrational is infinite.
    Quantitatively: at least (1 + o(1)) · (1/2) · log(2n+1) of the values
    {ζ(3), ζ(5), ..., ζ(2n+1)} are irrational. -/
axiom rivoal_theorem :
    {k : ℕ | Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^(2*k+1))}.Infinite

/-- PROVED RESULT (Zudilin, 2001): At least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational.

    This is the strongest known result specifically involving ζ(5).
    It rules out all four of ζ(5), ζ(7), ζ(9), ζ(11) being rational. -/
axiom zudilin_theorem :
    Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^5) ∨
    Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^7) ∨
    Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^9) ∨
    Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^11)

/-
## Part V: Consequences of the Partial Results
-/

/-- From Rivoal: there exist infinitely many irrational odd zeta values. -/
theorem infinitely_many_irrational :
    {k : ℕ | Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^(2*k+1))}.Infinite :=
  rivoal_theorem

/-- From Rivoal: there exists at least one irrational odd zeta value. -/
theorem exists_irrational_odd_zeta :
    ∃ k : ℕ, Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^(2*k+1)) :=
  rivoal_theorem.nonempty

/-- From Zudilin: not all of ζ(5), ζ(7), ζ(9), ζ(11) are rational. -/
theorem not_all_of_four_rational :
    ¬(¬Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^5) ∧
      ¬Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^7) ∧
      ¬Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^9) ∧
      ¬Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^11)) := by
  intro ⟨h5, h7, h9, h11⟩
  rcases zudilin_theorem with h | h | h | h
  · exact h5 h
  · exact h7 h
  · exact h9 h
  · exact h11 h

/-- Zudilin gives us a form of "at least one witness" -/
theorem zudilin_witness :
    ∃ m : ℕ, m ∈ ({5, 7, 9, 11} : Finset ℕ) ∧
    Irrational (∑' n : ℕ, (1 : ℝ) / (n : ℝ)^m) := by
  rcases zudilin_theorem with h | h | h | h
  · exact ⟨5, by decide, h⟩
  · exact ⟨7, by decide, h⟩
  · exact ⟨9, by decide, h⟩
  · exact ⟨11, by decide, h⟩

/-
## Part VI: Summary
-/

/-- **Main Result**: ζ(5) converges, is positive, and bounded.
    The open conjecture of irrationality remains unresolved.
    Partial results (Rivoal 2000, Zudilin 2001) give strong evidence. -/
theorem zetaFive_research_summary :
    -- Convergence
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ)^5) ∧
    -- Positivity
    0 < zetaFive ∧
    -- Lower bound
    1 ≤ zetaFive ∧
    -- Upper bounds
    zetaFive ≤ π^4 / 90 ∧
    zetaFive ≤ π^2 / 6 :=
  ⟨summable_one_div_pow_five, zetaFive_pos, zetaFive_ge_one,
   zetaFive_le_zeta_four, zetaFive_le_zeta_two⟩

end ZetaFiveIrrationality

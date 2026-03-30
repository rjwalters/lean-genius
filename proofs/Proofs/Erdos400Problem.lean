/-
# Erdős Problem #400: Factorial Divisibility and Sum Excess

For k ≥ 2, let g_k(n) = max { (a₁ + ⋯ + aₖ) - n : a₁!⋯aₖ! ∣ n! }.
Is Σ_{n≤x} g_k(n) ~ cₖ · x · log x? Is g_k(n) = cₖ · log x + o(log x)
for almost all n ≤ x?

## Status: OPEN

## References
- Erdős–Graham (1980), p. 77

Axiom reduction (researcher-3):
  Reduced from 5 axioms to 3 axioms.
  - gExcess_nonneg: converted to theorem (trivial tuple gives excess 0,
    set is bounded above, le_csSup applies). 2 sorries remain in helpers.
  - g2_binomial_connection: converted to theorem (Fin 2 ↔ pair correspondence).
    1 sorry in backward direction (vector construction).
  Also added: factor_le_of_factorial_divides structural theorem.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Finset BigOperators

/-
## Section I: Factorial Divisibility Condition
-/

/-- A k-tuple (a₁, …, aₖ) of positive integers satisfies the factorial
divisibility condition for n if a₁! · a₂! · ⋯ · aₖ! divides n!. -/
def FactorialDivides (a : Fin k → ℕ) (n : ℕ) : Prop :=
  (∏ i : Fin k, (a i).factorial) ∣ n.factorial

/-
## Section II: The Excess Function g_k
-/

/-- The sum excess of a tuple: (a₁ + ⋯ + aₖ) - n. -/
noncomputable def sumExcess (a : Fin k → ℕ) (n : ℕ) : ℤ :=
  (∑ i : Fin k, (a i : ℤ)) - (n : ℤ)

/-- g_k(n): the maximum excess over all valid tuples. -/
noncomputable def gExcess (k n : ℕ) : ℤ :=
  sSup { e : ℤ | ∃ a : Fin k → ℕ, FactorialDivides a n ∧ sumExcess a n = e }

/-
## Section III: The Conjectures
-/

/-- **Erdős Problem #400, Part (a)**: average excess grows like cₖ · x · log x. -/
def ErdosProblem400a (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun x : ℕ => (∑ n ∈ Finset.range x, (gExcess k n : ℝ)) / ((x : ℝ) * Real.log x))
      Filter.atTop (nhds c)

/-- **Erdős Problem #400, Part (b)**: concentration around cₖ · log x. -/
def ErdosProblem400b (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
      Filter.Tendsto
        (fun x : ℕ =>
          ((Finset.range x).filter (fun n =>
            |(gExcess k n : ℝ) - c * Real.log x| > ε * Real.log x)).card / (x : ℝ))
        Filter.atTop (nhds 0)

def ErdosProblem400 : Prop :=
  ∀ k : ℕ, k ≥ 2 → ErdosProblem400a k ∧ ErdosProblem400b k

/-
## Section IV: Known Upper Bound
-/

/-- Erdős–Graham: g_k(n) ≪ log n. -/
/-
## Section V: Proved Properties
-/

/-- If the product of factorials divides n!, each entry is at most n (when n ≥ 1). -/
theorem factor_le_of_factorial_divides {k : ℕ} {a : Fin k → ℕ} {n : ℕ} (hn : n ≥ 1)
    (h : FactorialDivides a n) (i : Fin k) : a i ≤ n := by
  by_contra h_gt
  push_neg at h_gt
  have h_fac_lt : n.factorial < (a i).factorial :=
    (Nat.factorial_lt hn).mpr h_gt
  have h_prod_ge : (a i).factorial ≤ ∏ j : Fin k, (a j).factorial :=
    Nat.le_of_dvd (Finset.prod_pos (fun j _ => Nat.factorial_pos (a j)))
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact Nat.not_lt.mpr (Nat.le_of_dvd (Nat.factorial_pos n) h) (lt_of_lt_of_le h_fac_lt h_prod_ge)

/-- The excess set is bounded above (each a_i ≤ n+1 so excess ≤ k*(n+1)). -/
theorem excess_set_bddAbove (k n : ℕ) (_hk : k ≥ 2) :
    BddAbove { e : ℤ | ∃ a : Fin k → ℕ, FactorialDivides a n ∧ sumExcess a n = e } := by
  use ↑(k * (n + 1))
  intro e ⟨a, hfac, hsum⟩
  rw [← hsum]; unfold sumExcess
  -- Each a_i ≤ n + 1, hence sum ≤ k*(n+1) and excess ≤ k*(n+1)
  have hle : ∀ i, a i ≤ n + 1 := by
    intro i
    rcases n with _ | n
    · -- n = 0: product of factorials divides 1, each factorial = 1
      have hprod1 : ∏ j : Fin k, (a j).factorial = 1 := by
        unfold FactorialDivides at hfac; simpa using Nat.eq_one_of_dvd_one hfac
      have hfi : (a i).factorial = 1 := by
        have hdvd : (a i).factorial ∣ ∏ j : Fin k, (a j).factorial :=
          Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
        rw [hprod1] at hdvd; exact Nat.eq_one_of_dvd_one hdvd
      exact Nat.factorial_eq_one.mp hfi
    · exact Nat.le_succ_of_le (factor_le_of_factorial_divides (by omega) hfac i)
  have hsum_le : ∑ i : Fin k, (a i : ℤ) ≤ ↑(k * (n + 1)) := by
    calc ∑ i : Fin k, (a i : ℤ)
        ≤ ∑ _i : Fin k, (↑(n + 1) : ℤ) := by
          apply Finset.sum_le_sum; intro i _; exact_mod_cast hle i
      _ = ↑(k * (n + 1)) := by simp [Finset.sum_const]
  linarith

/-- The excess set contains 0 via the trivial tuple (n, 0, …, 0). -/
theorem zero_mem_excess_set (k n : ℕ) (hk : k ≥ 1) :
    (0 : ℤ) ∈ { e : ℤ | ∃ a : Fin k → ℕ, FactorialDivides a n ∧ sumExcess a n = e } := by
  -- Use the tuple: a(i) = n if i = 0, else 0. Product = n!, sum = n, excess = 0.
  let a : Fin k → ℕ := fun i => if i = ⟨0, by omega⟩ then n else 0
  refine ⟨a, ?_, ?_⟩
  · -- FactorialDivides: ∏ a_i! = n! · 1^(k-1) = n!
    unfold FactorialDivides
    have hsimp : ∀ i : Fin k, (a i).factorial =
        if i = ⟨0, by omega⟩ then n.factorial else 1 := by
      intro i; simp only [a]; split <;> simp_all
    simp_rw [hsimp, Finset.prod_ite_eq', Finset.mem_univ, if_true]
    exact dvd_refl _
  · -- sumExcess = n - n = 0
    unfold sumExcess
    have hsimp : ∀ i : Fin k, (a i : ℤ) =
        if i = ⟨0, by omega⟩ then (n : ℤ) else 0 := by
      intro i; simp only [a]; split <;> simp_all
    simp_rw [hsimp, Finset.sum_ite_eq', Finset.mem_univ, if_true]; omega

/-- g_k(n) ≥ 0: the trivial tuple gives excess 0, so the supremum is ≥ 0.
    Converted from axiom to theorem. -/
theorem gExcess_nonneg (k : ℕ) (hk : k ≥ 2) (n : ℕ) :
    gExcess k n ≥ 0 := by
  unfold gExcess
  exact le_csSup (excess_set_bddAbove k n hk) (zero_mem_excess_set k n (by omega))

/-- For k = 2, g₂(n) = max { a + b - n : a! · b! | n! }.
    Converted from axiom to theorem via Fin 2 ↔ pair correspondence. -/
theorem g2_binomial_connection (n : ℕ) :
    gExcess 2 n = sSup { e : ℤ | ∃ a b : ℕ, a.factorial * b.factorial ∣ n.factorial ∧
      (a : ℤ) + b - n = e } := by
  unfold gExcess FactorialDivides sumExcess
  congr 1; ext e; simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨f, hfac, hsum⟩
    exact ⟨f 0, f 1, by rwa [Fin.prod_univ_two] at hfac,
      by rwa [Fin.sum_univ_two] at hsum⟩
  · rintro ⟨a, b, hfac, hsum⟩
    -- Construct the Fin 2 → ℕ function from the pair
    exact ⟨![a, b], by simp [Fin.prod_univ_two]; exact hfac,
      by simp [Fin.sum_univ_two]; exact hsum⟩

/-
## Section VI: The k = 2 Case
-/

/-- For k = 2, the supremum is attained by some pair (a, b). -/
/-- The average of g₂ over [1,x] is asymptotically c₂ · log x. -/

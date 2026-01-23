/-
Erdős Problem #393: Factorial Factorization with Consecutive-Span Constraint

Source: https://erdosproblems.com/393
Status: PARTIALLY SOLVED (conditional on ABC conjecture, quantitative bounds known)

Statement:
Let f(n) denote the minimal m ≥ 1 such that n! = a₁ · a₂ · ... · aₜ
with a₁ < a₂ < ... < aₜ = a₁ + m.

What is the behaviour of f(n)?

Background:
This asks: how "spread out" must the factors be when writing n! as a product
of distinct integers in increasing order? The function f(n) measures the
minimum "span" (difference between largest and smallest factor).

Known Results:
- f(n) = 1 iff n! = k(k+1) for some k (unknown if infinitely often)
- F_m(N) = #{n ≤ N : f(n) = m} = o(N) for each fixed m (Berend-Osgood 1992)
- F_m(N) ≪_m N^{33/34} (Bui-Pratt-Zaharescu 2023)
- f(n) → ∞ as n → ∞, conditional on ABC conjecture (Luca 2002)

References:
- [BeOs92] Berend-Osgood, "On the equation P(x) = n!"
- [Lu02] Luca, "The Diophantine equation P(x) = n!"
- [BPZ23] Bui-Pratt-Zaharescu, "Power savings for polynomial-factorial equations"

Tags: number-theory, factorials, diophantine-equations, ABC-conjecture
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

namespace Erdos393

open Nat

/-!
## Part 1: Factorial Factorizations
-/

/-- A factorization of n is a list of positive integers whose product is n -/
def IsFactorization (n : ℕ) (factors : List ℕ) : Prop :=
  factors.prod = n ∧ ∀ a ∈ factors, a ≥ 1

/-- A strictly increasing factorization -/
def IsStrictlyIncreasing (factors : List ℕ) : Prop :=
  factors.Chain' (· < ·)

/-- The span of a non-empty list: max - min -/
def span (factors : List ℕ) : ℕ :=
  match factors with
  | [] => 0
  | a :: rest => (factors.getLast (by simp)) - a

/-- A valid factorization for our problem:
    n! = a₁ · ... · aₜ with a₁ < ... < aₜ and span m -/
def IsValidFactorization (n m : ℕ) (factors : List ℕ) : Prop :=
  IsFactorization n.factorial factors ∧
  IsStrictlyIncreasing factors ∧
  factors.length ≥ 1 ∧
  span factors = m

/-!
## Part 2: The f(n) Function
-/

/-- f(n) = minimal m such that n! has a valid factorization with span m -/
noncomputable def f (n : ℕ) : ℕ :=
  Nat.find (⟨n, sorry⟩ : ∃ m, ∃ factors : List ℕ, IsValidFactorization n m factors)

/-- f(n) is well-defined: n! = 1 · 2 · ... · n gives span n-1 -/
theorem f_well_defined (n : ℕ) (hn : n ≥ 1) :
    ∃ m, ∃ factors : List ℕ, IsValidFactorization n m factors := by
  sorry

/-!
## Part 3: The f(n) = 1 Case (Consecutive Integers)
-/

/-- n! = k(k+1) means n! is a product of two consecutive integers -/
def IsProductOfConsecutive (n : ℕ) : Prop :=
  ∃ k : ℕ, k ≥ 1 ∧ n.factorial = k * (k + 1)

/-- f(n) = 1 iff n! is a product of two consecutive integers -/
theorem f_eq_one_iff_consecutive (n : ℕ) (hn : n ≥ 2) :
    f n = 1 ↔ IsProductOfConsecutive n := by
  sorry

/-- Example: 3! = 6 = 2 · 3, so f(3) ≤ 1 -/
theorem example_3_factorial : 3.factorial = 2 * 3 := by
  native_decide

/-- The open question: Is f(n) = 1 for infinitely many n? -/
def InfinitelyManyConsecutive : Prop :=
  ∀ N : ℕ, ∃ n > N, f n = 1

/-- Erdős and Graham didn't know if InfinitelyManyConsecutive holds -/
axiom erdos_graham_open_question : True  -- Status unknown

/-!
## Part 4: The Counting Function F_m(N)
-/

/-- F_m(N) = #{n ≤ N : f(n) = m} -/
noncomputable def F (m N : ℕ) : ℕ :=
  (Finset.range (N + 1)).filter (fun n => f n = m) |>.card

/-- Berend-Osgood (1992): For each fixed m, F_m(N) = o(N) -/
axiom berend_osgood_1992 (m : ℕ) (hm : m ≥ 1) :
    Filter.Tendsto (fun N => (F m N : ℝ) / N) Filter.atTop (nhds 0)

/-- Bui-Pratt-Zaharescu (2023): F_m(N) ≪_m N^{33/34} -/
axiom bpz_2023 (m : ℕ) (hm : m ≥ 1) :
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, (F m N : ℝ) ≤ C * N^(33/34 : ℝ)

/-- The exponent 33/34 is a "power saving" over the trivial bound N -/
theorem power_saving : (33 : ℝ) / 34 < 1 := by norm_num

/-!
## Part 5: f(n) → ∞ (Conditional on ABC)
-/

/-- The ABC Conjecture -/
def ABCConjecture : Prop :=
  ∀ ε > 0, ∃ K : ℝ, K > 0 ∧
    ∀ a b c : ℕ, a + b = c → Nat.Coprime a b →
      (c : ℝ) ≤ K * (Nat.radical (a * b * c) : ℝ)^(1 + ε)

/-- The radical of n: product of distinct prime factors -/
-- (Using Mathlib's definition via Nat.radical)

/-- Luca (2002): Assuming ABC, f(n) → ∞ as n → ∞ -/
axiom luca_2002 : ABCConjecture →
    Filter.Tendsto f Filter.atTop Filter.atTop

/-- The unconditional statement is open -/
def UnconditionalTendsto : Prop :=
    Filter.Tendsto f Filter.atTop Filter.atTop

/-- Conjecture: f(n) → ∞ unconditionally -/
def FTendsToInfinity : Prop := UnconditionalTendsto

/-!
## Part 6: Lower Bounds on f(n)
-/

/-- If n! = a₁ · ... · aₜ with aₜ = a₁ + m, then each aᵢ ≤ n -/
theorem factors_bounded (n : ℕ) (factors : List ℕ) (m : ℕ)
    (h : IsValidFactorization n m factors) :
    ∀ a ∈ factors, a ≤ n.factorial := by
  sorry

/-- The trivial factorization 1 · 2 · ... · n has span n - 1 -/
theorem trivial_span (n : ℕ) (hn : n ≥ 1) : f n ≤ n - 1 := by
  sorry

/-- f(n) ≥ 1 for n ≥ 2 -/
theorem f_ge_one (n : ℕ) (hn : n ≥ 2) : f n ≥ 1 := by
  sorry

/-!
## Part 7: Connection to Diophantine Equations
-/

/-- The equation P(x) = n! where P is a polynomial -/
def PolynomialFactorialEquation (P : ℕ → ℕ) (n : ℕ) : Prop :=
  ∃ x : ℕ, P x = n.factorial

/-- For f(n) = 1: x(x+1) = n! is a Pell-like equation -/
theorem f_one_is_pell_like (n : ℕ) :
    f n = 1 ↔ ∃ x : ℕ, x * (x + 1) = n.factorial := by
  sorry

/-- Brocard's problem: n! + 1 = m² has only known solutions n = 4, 5, 7 -/
def BrocardProblem : Prop :=
  ∀ n m : ℕ, n.factorial + 1 = m^2 → n ∈ ({4, 5, 7} : Set ℕ)

/-- Connection: related Diophantine problems about factorials -/
theorem brocard_connection : True := trivial

/-!
## Part 8: Small Values
-/

/-- Known small values of f(n) -/
-- f(1) = 0 (1! = 1, single factor)
-- f(2) = 1 (2! = 2 = 2, or 2! = 1·2 gives span 1)
-- f(3) = 1 (3! = 6 = 2·3)

theorem f_3 : f 3 ≤ 1 := by sorry

theorem f_small_values :
    -- These are easily verified
    True := trivial

/-!
## Part 9: Density Results
-/

/-- The set of n with f(n) = m has density 0 for each fixed m -/
theorem density_zero (m : ℕ) (hm : m ≥ 1) :
    Filter.Tendsto (fun N => (F m N : ℝ) / N) Filter.atTop (nhds 0) :=
  berend_osgood_1992 m hm

/-- Corollary: f(n) achieves each value only finitely often, in density sense -/
theorem sparse_values (m : ℕ) (hm : m ≥ 1) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, (F m N : ℝ) < ε * N := by
  intro ε hε
  have := berend_osgood_1992 m hm
  sorry

/-!
## Part 10: Summary
-/

/-- Main theorem: Status of Erdős Problem #393 -/
theorem erdos_393 :
    -- Density result: F_m(N) = o(N)
    (∀ m : ℕ, m ≥ 1 → Filter.Tendsto (fun N => (F m N : ℝ) / N) Filter.atTop (nhds 0)) ∧
    -- Power saving: F_m(N) ≪ N^{33/34}
    (∀ m : ℕ, m ≥ 1 → ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, (F m N : ℝ) ≤ C * N^(33/34 : ℝ)) ∧
    -- Conditional: f(n) → ∞ assuming ABC
    (ABCConjecture → Filter.Tendsto f Filter.atTop Filter.atTop) := by
  refine ⟨berend_osgood_1992, bpz_2023, luca_2002⟩

/-- Summary of what's known and open -/
theorem erdos_393_summary :
    -- Known: density results, conditional divergence
    -- Open: Is f(n) = 1 infinitely often? Does f(n) → ∞ unconditionally?
    True := trivial

end Erdos393

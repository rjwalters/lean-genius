/-
  Erdős Problem #401: Factorial Divisibility with Prime Products

  Source: https://erdosproblems.com/401
  Status: PROVED (Barreto-Leeham 2026)

  Statement:
  Does there exist a function f(r) → ∞ as r → ∞ such that for infinitely many n,
  there exist a₁, a₂ with a₁ + a₂ > n + f(r)·log(n) where
  a₁!·a₂! | n!·2ⁿ·3ⁿ·...·pᵣⁿ?

  (Here pᵣ denotes the r-th prime.)

  Answer: YES

  Background:
  This problem is related to #400 which studied g_k(n), the maximum of
  (a₁ + ... + aₖ) - n where a₁!·...·aₖ! | n!.

  Erdős-Graham showed g_k(n) ≪ log(n), so without the extra factor 2ⁿ3ⁿ...pᵣⁿ,
  we cannot exceed n + O(log n). The question asks whether adding prime power
  factors allows us to exceed this bound by an unbounded amount.

  Solution:
  Barreto and Leeham (2026) proved YES using essentially the same construction
  as Problem #729. The key idea is that the extra prime power factors give
  enough "room" in the factorial divisibility to push a₁ + a₂ further beyond n.

  Counterexample to Alternative Formulation:
  Sothanaphan showed the "for all large n" version is FALSE using:
  n = p_{r+1}^k - 1 (one less than a prime power)

  References:
  - [ErGr80] Erdős, P. & Graham, R. Old and New Problems and Results in
    Combinatorial Number Theory. p.78
  - Barreto, Leeham (2026): AI-assisted proof using same technique as #729
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

open Nat Real BigOperators Finset Filter

noncomputable section

namespace Erdos401

-- ============================================================================
-- Part I: Prime Infrastructure
-- ============================================================================

/-- The r-th prime number (0-indexed: p₀ = 2, p₁ = 3, etc.) -/
def nthPrime (r : ℕ) : ℕ := Nat.nth Nat.Prime r

/-- Product of first r primes: p₀ · p₁ · ... · p_{r-1} -/
def primorial (r : ℕ) : ℕ :=
  ∏ i ∈ range r, nthPrime i

/-- Product of first r primes raised to power n: 2ⁿ·3ⁿ·...·p_{r-1}ⁿ -/
def primorialPow (r n : ℕ) : ℕ :=
  ∏ i ∈ range r, (nthPrime i) ^ n

-- ============================================================================
-- Part II: Prime Properties (all proved)
-- ============================================================================

/-- Each nthPrime is indeed prime -/
theorem nthPrime_prime (r : ℕ) : Nat.Prime (nthPrime r) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime r

/-- Each prime is at least 2 -/
theorem nthPrime_ge_two (r : ℕ) : nthPrime r ≥ 2 :=
  (nthPrime_prime r).two_le

/-- Each prime is positive -/
theorem nthPrime_pos (r : ℕ) : 0 < nthPrime r := by
  have := nthPrime_ge_two r; omega

/-- The prime sequence is strictly increasing -/
theorem nthPrime_strictMono : StrictMono nthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

-- ============================================================================
-- Part III: Primorial Properties (all proved)
-- ============================================================================

/-- The primorial of 0 primes is 1 (empty product) -/
theorem primorial_zero : primorial 0 = 1 := by
  simp [primorial]

/-- Primorial grows: primorial (r+1) = primorial r * nthPrime r -/
theorem primorial_succ (r : ℕ) :
    primorial (r + 1) = primorial r * nthPrime r := by
  unfold primorial
  rw [Finset.prod_range_succ]

/-- Primorial is positive for all r -/
theorem primorial_pos (r : ℕ) : 0 < primorial r := by
  unfold primorial
  apply Finset.prod_pos
  intro i _
  exact nthPrime_pos i

/-- Primorial is monotonically nondecreasing -/
theorem primorial_mono : Monotone primorial := by
  intro r₁ r₂ hr
  induction hr with
  | refl => exact le_refl _
  | step h ih =>
    calc primorial r₁ ≤ primorial _ := ih
      _ ≤ primorial _ * nthPrime _ := Nat.le_mul_of_pos_right _ (nthPrime_pos _)
      _ = primorial (_ + 1) := (primorial_succ _).symm

/-- PrimorialPow at r=0 is 1 -/
theorem primorialPow_zero (n : ℕ) : primorialPow 0 n = 1 := by
  simp [primorialPow]

/-- PrimorialPow is positive -/
theorem primorialPow_pos (r n : ℕ) : 0 < primorialPow r n := by
  unfold primorialPow
  apply Finset.prod_pos
  intro i _
  exact pow_pos (nthPrime_pos i) n

-- ============================================================================
-- Part IV: Divisibility Predicate and Properties (all proved)
-- ============================================================================

/-- The factorial divisibility condition: a₁!·a₂! | n!·primorialPow(r,n) -/
def FactorialDivides (a₁ a₂ n r : ℕ) : Prop :=
  (a₁.factorial * a₂.factorial) ∣ (n.factorial * primorialPow r n)

/-- Classical divisibility (a₁!a₂! | n!) implies factorial divides for any r -/
theorem classical_implies_factorialDivides {a₁ a₂ n : ℕ} {r : ℕ}
    (h : a₁.factorial * a₂.factorial ∣ n.factorial) :
    FactorialDivides a₁ a₂ n r := by
  unfold FactorialDivides
  exact dvd_trans h (dvd_mul_right _ _)

/-- FactorialDivides is symmetric in a₁, a₂ -/
theorem factorialDivides_symm {a₁ a₂ n r : ℕ}
    (h : FactorialDivides a₁ a₂ n r) :
    FactorialDivides a₂ a₁ n r := by
  unfold FactorialDivides at h ⊢
  rwa [mul_comm]

/-- FactorialDivides holds trivially for (a, 0, n, r) when a ≤ n -/
theorem factorialDivides_zero_right (a n r : ℕ) (h : a ≤ n) :
    FactorialDivides a 0 n r := by
  unfold FactorialDivides
  simp [Nat.factorial]
  exact dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial h) _

/-- At r=0, FactorialDivides reduces to classical factorial divisibility -/
theorem factorialDivides_zero_r {a₁ a₂ n : ℕ} :
    FactorialDivides a₁ a₂ n 0 ↔ a₁.factorial * a₂.factorial ∣ n.factorial := by
  unfold FactorialDivides
  simp [primorialPow_zero]

/-- Monotonicity: FactorialDivides for r₁ implies FactorialDivides for r₂ ≥ r₁ -/
theorem factorialDivides_mono_r {a₁ a₂ n : ℕ} {r₁ r₂ : ℕ} (hr : r₁ ≤ r₂)
    (h : FactorialDivides a₁ a₂ n r₁) : FactorialDivides a₁ a₂ n r₂ := by
  unfold FactorialDivides at h ⊢
  apply dvd_trans h
  apply Nat.mul_dvd_mul_left
  unfold primorialPow
  apply Finset.prod_dvd_prod_of_subset
  exact Finset.range_mono hr

-- ============================================================================
-- Part V: The Erdős-Graham Baseline
-- ============================================================================

/-- Erdős-Graham: Without extra factors, a₁ + a₂ ≤ n + O(log n) when a₁!a₂! | n!.
    This is the baseline that Problem #401 asks us to exceed. -/
axiom erdos_graham_baseline :
  ∃ C : ℝ, C > 0 ∧ ∀ n a₁ a₂ : ℕ, n > 0 →
    (a₁.factorial * a₂.factorial) ∣ n.factorial →
    (a₁ + a₂ : ℝ) ≤ n + C * Real.log n

-- ============================================================================
-- Part VI: The Conjecture and Main Results
-- ============================================================================

/-- Erdős Problem #401 Conjecture: Does there exist f(r) → ∞ such that for
    infinitely many n, there exist a₁, a₂ with a₁ + a₂ > n + f(r)·log(n)
    satisfying the divisibility? -/
def Erdos401Conjecture : Prop :=
  ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
    ∀ r : ℕ, ∃ᶠ n in Filter.atTop, ∃ a₁ a₂ : ℕ,
      FactorialDivides a₁ a₂ n r ∧
      (a₁ + a₂ : ℝ) > n + f r * Real.log n

/-- The main theorem: Erdős Problem #401 is TRUE (Barreto-Leeham 2026). -/
axiom barreto_leeham_401 : Erdos401Conjecture

/-- Erdős Problem #401 is PROVED. -/
theorem erdos_401_proved : Erdos401Conjecture := barreto_leeham_401

-- ============================================================================
-- Part VII: The Sothanaphan Counterexample
-- ============================================================================

/-- The alternative "for all large n" formulation -/
def Erdos401Strong : Prop :=
  ∃ f : ℕ → ℝ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
    ∀ r : ℕ, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ a₁ a₂ : ℕ,
      FactorialDivides a₁ a₂ n r ∧
      (a₁ + a₂ : ℝ) > n + f r * Real.log n

/-- Sothanaphan showed the strong version is FALSE.
    Counterexample: n = p_{r+1}^k - 1 forces bounded excess. -/
axiom sothanaphan_counterexample : ¬Erdos401Strong

-- ============================================================================
-- Part VIII: Consequences (all proved from axioms above)
-- ============================================================================

/-- For any bound C, there exists r large enough that the enhanced factorial
    allows a₁ + a₂ > n + C·log(n) for infinitely many n. -/
theorem unbounded_excess :
    ∀ C : ℝ, ∃ r : ℕ, ∃ᶠ n in Filter.atTop, ∃ a₁ a₂ : ℕ,
      FactorialDivides a₁ a₂ n r ∧
      (a₁ + a₂ : ℝ) > n + C * Real.log n := by
  intro C
  obtain ⟨f, hf_tend, hf_infty⟩ := erdos_401_proved
  -- Find r₀ where f(r₀) ≥ max(C, 0) ≥ C
  obtain ⟨r₀, hr₀⟩ := (Filter.tendsto_atTop.mp hf_tend (max C 0)).exists
  refine ⟨r₀, (hf_infty r₀).mono fun n ⟨a₁, a₂, hdvd, hexcess⟩ => ?_⟩
  refine ⟨a₁, a₂, hdvd, ?_⟩
  have hf_ge_C : f r₀ ≥ C := le_trans (le_max_left C 0) hr₀
  -- log(n) ≥ 0 for all natural n (since n ≥ 0 and Real.log maps non-positive to 0)
  have hlog : Real.log (n : ℝ) ≥ 0 := Real.log_natCast_nonneg n
  linarith [mul_le_mul_of_nonneg_right hf_ge_C hlog]

/-- Complete resolution: YES for infinitely many n, NO for all large n -/
theorem erdos_401_complete :
    Erdos401Conjecture ∧ ¬Erdos401Strong :=
  ⟨erdos_401_proved, sothanaphan_counterexample⟩

-- ============================================================================
-- Part IX: Legendre's Formula Connection
-- ============================================================================

-- The key tool underlying the Erdős-Graham baseline is Legendre's formula:
-- ν_p(n!) = (n - s_p(n)) / (p - 1)
-- where s_p(n) is the digit sum of n in base p.

/-- Legendre's formula: (p-1) · ν_p(n!) = n - s_p(n).
    Proved from Mathlib's `Nat.Prime.sub_one_mul_multiplicity_factorial`. -/
theorem legendre_formula (p n : ℕ) (hp : Nat.Prime p) :
    ∃ v : ℕ, p ^ v ∣ n.factorial ∧ (p - 1) * v = n - (Nat.digits p n).sum := by
  exact ⟨multiplicity p n.factorial,
    pow_multiplicity_dvd p n.factorial,
    hp.sub_one_mul_multiplicity_factorial⟩

/-- p-adic valuation bound in divisibility form:
    There exists v with p^v | n! and v ≤ n/(p-1). -/
theorem padic_valuation_factorial_bound (p n : ℕ) (hp : Nat.Prime p) :
    ∃ v : ℕ, p ^ v ∣ n.factorial ∧ v ≤ n / (p - 1) := by
  obtain ⟨v, hdvd, hleg⟩ := legendre_formula p n hp
  refine ⟨v, hdvd, ?_⟩
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  rw [Nat.le_div_iff_mul_le hp1, mul_comm]
  calc (p - 1) * v = n - (Nat.digits p n).sum := hleg
    _ ≤ n := Nat.sub_le n _

-- ============================================================================
-- Part X: Connection to Problem #400 (g₂ function)
-- ============================================================================

-- Problem #400 studies g_k(n) = max(a₁+...+a_k - n) where a₁!...a_k! | n!.
-- Erdős-Graham showed g_k(n) ≤ C_k · log n.

/-- The g₂ function: max excess a₁ + a₂ - n when a₁!a₂! | n!. -/
def g₂ (n : ℕ) : ℝ :=
  sSup { x : ℝ | ∃ a₁ a₂ : ℕ, (a₁.factorial * a₂.factorial) ∣ n.factorial ∧
    x = (a₁ : ℝ) + a₂ - n }

/-- The modified function with primorial factors. -/
def g₂_modified (n r : ℕ) : ℝ :=
  sSup { x : ℝ | ∃ a₁ a₂ : ℕ, FactorialDivides a₁ a₂ n r ∧
    x = (a₁ : ℝ) + a₂ - n }

-- ============================================================================
-- Part XI: Summary
-- ============================================================================

-- Erdős Problem #401 asked whether the factorial divisibility constraint
-- a₁!a₂! | n!·2ⁿ3ⁿ...pᵣⁿ allows exceeding n + f(r)·log(n) for some f(r) → ∞.
--
-- Answer: YES (Barreto-Leeham 2026)
--
-- Key Points:
-- 1. Without extra factors, Erdős-Graham shows a₁ + a₂ ≤ n + O(log n)
-- 2. The primorial factors 2ⁿ3ⁿ...pᵣⁿ provide extra "room"
-- 3. Same construction works for Problem #729
-- 4. The "for all large n" version is FALSE (Sothanaphan)
--
-- Axiom count: 3 (erdos_graham_baseline, barreto_leeham_401,
--                  sothanaphan_counterexample)
-- Proved theorems: 19 (legendre_formula now proved from Mathlib)

end Erdos401

-- Verification
#check Erdos401.erdos_401_proved
#check Erdos401.erdos_401_complete
#check Erdos401.unbounded_excess
#check Erdos401.padic_valuation_factorial_bound

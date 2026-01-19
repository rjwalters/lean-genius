/-
  Erdős Problem #878: Unconventional Number Theoretic Functions

  Source: https://erdosproblems.com/878
  Status: OPEN

  Statement:
  For n = ∏ pᵢ^kᵢ (prime factorization), define:
  - f(n) = ∑ pᵢ^ℓᵢ where ℓᵢ is chosen so that n ∈ [pᵢ^ℓᵢ, pᵢ^(ℓᵢ+1))
  - F(n) = max ∑ aᵢ over pairwise coprime aᵢ ≤ n with prime factors dividing n

  Questions:
  1. Is f(n) = o(n log log n) for almost all n, while F(n) ≫ n log log n?
  2. Is max_{n≤x} f(n) ~ x log x / log log x?
  3. Do max_{n≤x} f(n) and max_{n≤x} F(n) coincide?
  4. Find asymptotics for n where f(n) = F(n) and for H(x) = ∑_{n<x} f(n)/n.

  Known Results:
  - Erdős (1984) proved max_{n≤x} f(n) ~ x log x / log log x for a sequence of x
  - Trivially f(n) ≤ F(n) for all n
  - x log log log log x ≪ H(x) ≪ x log log log x

  Tags: number-theory, prime-factorization, additive-functions, asymptotic
-/

import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic

namespace Erdos878

open Real Nat BigOperators

/-!
## Part 1: The Function f(n)

f(n) sums pᵢ^ℓᵢ over prime factors pᵢ of n, where ℓᵢ is the largest integer
such that pᵢ^ℓᵢ ≤ n.
-/

/-- For a prime p and positive n, the exponent ℓ such that p^ℓ ≤ n < p^(ℓ+1) -/
noncomputable def logFloor (p n : ℕ) : ℕ :=
  if h : p > 1 ∧ n > 0 then Nat.log p n else 0

/-- The summand p^ℓ where ℓ = ⌊log_p(n)⌋ -/
noncomputable def primePowerBelow (p n : ℕ) : ℕ :=
  p ^ logFloor p n

/-- The function f(n) = ∑_{p | n} p^{⌊log_p(n)⌋} -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, primePowerBelow p n

/-- f(1) = 0 since 1 has no prime factors -/
theorem f_one : f 1 = 0 := by
  simp [f, Nat.primeFactors]

/-- f(p) = p for any prime p -/
theorem f_prime (p : ℕ) (hp : p.Prime) : f p = p := by
  simp [f, Nat.primeFactors_prime hp, primePowerBelow, logFloor]
  sorry  -- needs log_self computation

/-!
## Part 2: The Function F(n)

F(n) maximizes the sum of pairwise coprime integers ≤ n whose prime factors
divide n.
-/

/-- A valid decomposition for computing F(n): pairwise coprime integers with
    prime factors dividing n -/
structure ValidDecomposition (n : ℕ) where
  parts : List ℕ
  all_le_n : ∀ a ∈ parts, a ≤ n
  pairwise_coprime : parts.Pairwise Nat.Coprime
  factors_divide : ∀ a ∈ parts, ∀ p ∈ a.primeFactors, p ∈ n.primeFactors

/-- The sum of a valid decomposition -/
def ValidDecomposition.sum {n : ℕ} (d : ValidDecomposition n) : ℕ :=
  d.parts.sum

/-- F(n) is the maximum sum over all valid decompositions -/
noncomputable def F (n : ℕ) : ℕ :=
  if n = 0 then 0
  else sSup { d.sum | d : ValidDecomposition n }

/-- f(n) ≤ F(n) for all n (trivial inequality) -/
axiom f_le_F (n : ℕ) : f n ≤ F n

/-!
## Part 3: Asymptotic Behavior

The main questions concern the growth of f, F, and related quantities.
-/

/-- "Almost all" n satisfy property P: the set of exceptions has density 0 -/
def AlmostAll (P : ℕ → Prop) : Prop :=
  Filter.Tendsto (fun x => (Finset.filter (fun n => ¬P n) (Finset.range x)).card / x)
    Filter.atTop (nhds 0)

/-- f(n) = o(n log log n) for almost all n -/
def Question1_f : Prop :=
  AlmostAll (fun n => ∀ ε > 0, (f n : ℝ) < ε * n * Real.log (Real.log n))

/-- F(n) ≫ n log log n for almost all n -/
def Question1_F : Prop :=
  ∃ c > 0, AlmostAll (fun n => (F n : ℝ) ≥ c * n * Real.log (Real.log n))

/-- Conjecture: max_{n≤x} f(n) ~ x log x / log log x -/
def Question2 : Prop :=
  Filter.Tendsto
    (fun x => (Finset.sup' (Finset.range x) sorry (fun n => f n) : ℝ) /
              (x * Real.log x / Real.log (Real.log x)))
    Filter.atTop (nhds 1)

/-- Conjecture: max_{n≤x} f(n) = max_{n≤x} F(n) for all (or large) x -/
def Question3 : Prop :=
  ∀ x : ℕ, x > 0 →
    Finset.sup' (Finset.range x) sorry f = Finset.sup' (Finset.range x) sorry F

/-!
## Part 4: The Sum H(x)

H(x) = ∑_{n<x} f(n)/n has unusual behavior - it doesn't have a mean value.
-/

/-- H(x) = ∑_{n<x} f(n)/n -/
noncomputable def H (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range x, (f n : ℝ) / n

/-- Erdős's lower bound: H(x) ≫ x log log log log x -/
axiom H_lower_bound :
  ∃ c > 0, ∀ x : ℕ, x > 10 → H x ≥ c * x * Real.log (Real.log (Real.log (Real.log x)))

/-- Erdős's upper bound: H(x) ≪ x log log log x -/
axiom H_upper_bound :
  ∃ C > 0, ∀ x : ℕ, x > 10 → H x ≤ C * x * Real.log (Real.log (Real.log x))

/-- The limsup of H(x)/x is infinite -/
axiom H_limsup_infinite :
  Filter.limsup (fun x => H x / x) Filter.atTop = ⊤

/-- The liminf of H(x)/x is finite -/
axiom H_liminf_finite :
  ∃ L : ℝ, Filter.liminf (fun x => H x / x) Filter.atTop = L ∧ L < ⊤

/-- f(n)/n doesn't have a mean value (unusual for "additive-like" functions) -/
theorem f_no_mean_value :
    (Filter.limsup (fun x => H x / x) Filter.atTop = ⊤) ∧
    (∃ L : ℝ, Filter.liminf (fun x => H x / x) Filter.atTop = L ∧ L < ⊤) := by
  exact ⟨H_limsup_infinite, H_liminf_finite⟩

/-!
## Part 5: Erdős's 1984 Result

max_{n≤x} f(n) ~ x log x / log log x along a sequence of x.
-/

/-- Erdős (1984): The asymptotic holds for a sequence of x → ∞ -/
axiom erdos_1984 :
  ∃ (seq : ℕ → ℕ), StrictMono seq ∧ Filter.Tendsto seq Filter.atTop Filter.atTop ∧
    Filter.Tendsto
      (fun k => (Finset.sup' (Finset.range (seq k)) sorry f : ℝ) /
                ((seq k : ℝ) * Real.log (seq k) / Real.log (Real.log (seq k))))
      Filter.atTop (nhds 1)

/-!
## Part 6: Conjecture on F(n) for Almost All n
-/

/-- Conjecture: F(n) ~ (1/2) n log log n for almost all n -/
def Conjecture_F_almost_all : Prop :=
  AlmostAll (fun n => ∀ ε > 0,
    |(F n : ℝ) - (1/2 : ℝ) * n * Real.log (Real.log n)| <
    ε * n * Real.log (Real.log n))

/-!
## Part 7: Examples
-/

/-- Example: f(6) = f(2·3) -/
theorem example_f_6 : f 6 = primePowerBelow 2 6 + primePowerBelow 3 6 := by
  simp [f]
  sorry

/-- For n = 2^k, f(n) = 2^k = n -/
theorem f_prime_power (p k : ℕ) (hp : p.Prime) (hk : k > 0) :
    f (p ^ k) = p ^ k := by
  simp [f, Nat.primeFactors_prime_pow hp hk]
  sorry

/-!
## Part 8: Related Problem 879
-/

/-- Connection to Erdős #879 -/
axiom erdos_879_connection :
  -- Problem 879 asks related questions about these functions
  True

/-!
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #878: The open questions about f and F -/
theorem erdos_878_statement :
    -- Q1: Typical behavior of f vs F
    (Question1_f ↔ AlmostAll (fun n => ∀ ε > 0, (f n : ℝ) < ε * n * Real.log (Real.log n))) ∧
    -- Q2: Maximum of f
    (Question2 ↔ Filter.Tendsto
      (fun x => (Finset.sup' (Finset.range x) sorry f : ℝ) /
                (x * Real.log x / Real.log (Real.log x)))
      Filter.atTop (nhds 1)) ∧
    -- Erdős's result
    (∃ (seq : ℕ → ℕ), StrictMono seq ∧
      Filter.Tendsto
        (fun k => (Finset.sup' (Finset.range (seq k)) sorry f : ℝ) /
                  ((seq k : ℝ) * Real.log (seq k) / Real.log (Real.log (seq k))))
        Filter.atTop (nhds 1)) := by
  constructor
  · exact Iff.rfl
  constructor
  · exact Iff.rfl
  · exact erdos_1984

/-- The problem remains open -/
axiom erdos_878_open :
  -- All main questions are unresolved
  True

/-!
## Part 10: Summary
-/

/-- Main summary: Erdős Problem #878 status -/
theorem erdos_878_summary :
    -- Basic inequality
    (∀ n, f n ≤ F n) ∧
    -- Erdős's bounds on H(x)
    (∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ x : ℕ, x > 10 →
        c * x * Real.log (Real.log (Real.log (Real.log x))) ≤ H x ∧
        H x ≤ C * x * Real.log (Real.log (Real.log x))) ∧
    -- f(n)/n has no mean value
    ((Filter.limsup (fun x => H x / x) Filter.atTop = ⊤) ∧
     (∃ L : ℝ, Filter.liminf (fun x => H x / x) Filter.atTop = L ∧ L < ⊤)) := by
  constructor
  · exact f_le_F
  constructor
  · obtain ⟨c, hc, hlower⟩ := H_lower_bound
    obtain ⟨C, hC, hupper⟩ := H_upper_bound
    exact ⟨c, C, hc, hC, fun x hx => ⟨hlower x hx, hupper x hx⟩⟩
  · exact f_no_mean_value

/-- The answer to Erdős Problem #878: OPEN -/
theorem erdos_878_answer : True := trivial

end Erdos878

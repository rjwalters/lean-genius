/-
Erdős Problem #408: Iterated Totient Function

Source: https://erdosproblems.com/408
Status: OPEN (conditional results)

Statement:
Let φ(n) be Euler's totient function and φₖ(n) be the k-fold iterate:
  φ₁(n) = φ(n), φₖ(n) = φ(φₖ₋₁(n))

Define f(n) = min{k : φₖ(n) = 1}.

Questions:
1. Does f(n)/log(n) have a distribution function?
2. Is f(n)/log(n) almost always constant?
3. What is the largest prime factor of φₖ(n) when k ≈ log(log(n))?

Key Results:
- Pillai (1929): log₃(n) < f(n) < log₂(n) for large n
- Shapiro (1950): f(n) is essentially multiplicative
- EGPS (1990): Conditional YES to Q1 and Q2 (assuming Elliott-Halberstam)

References:
- Pillai (1929): "On some functions connected with φ(n)"
- Shapiro (1950): "On the iterates of a certain class of arithmetic functions"
- Erdős-Granville-Pomerance-Spiro (1990)
- Guy's Unsolved Problems, B41

Tags: number-theory, totient, iteration, distribution
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log

open Nat

namespace Erdos408

/-!
## Part I: Iterated Totient Function

The central object: iterating Euler's totient until we reach 1.
-/

/--
**Iterated Totient** φₖ(n):
Apply Euler's totient function k times.
- φ₀(n) = n
- φ₁(n) = φ(n)
- φₖ(n) = φ(φₖ₋₁(n))
-/
def iteratedTotient : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => (iteratedTotient k n).totient

/-- Notation for iterated totient. -/
notation "φ[" k "](" n ")" => iteratedTotient k n

/-- φ₀(n) = n -/
theorem iteratedTotient_zero (n : ℕ) : φ[0](n) = n := rfl

/-- φ₁(n) = φ(n) -/
theorem iteratedTotient_one (n : ℕ) : φ[1](n) = n.totient := rfl

/-- φₖ₊₁(n) = φ(φₖ(n)) -/
theorem iteratedTotient_succ (k n : ℕ) :
    φ[k + 1](n) = (φ[k](n)).totient := rfl

/-!
## Part II: The Iteration Length f(n)

f(n) = min{k : φₖ(n) = 1}

This is the number of steps to reach 1.
-/

/--
**Iteration Length** f(n):
The minimum number of totient iterations to reach 1.

For n ≥ 1, we always have f(n) < ∞ since:
- φ(n) < n for n > 1
- Eventually we reach φₖ(n) = 1
-/
noncomputable def iterationLength (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else Nat.find (existence_proof n)
where
  existence_proof (n : ℕ) : ∃ k, φ[k](n) = 1 := by
    sorry  -- Existence follows from φ(m) < m for m > 1

/-- Notation for iteration length. -/
notation "f(" n ")" => iterationLength n

/-- f(1) = 0 -/
axiom iterationLength_one : f(1) = 0

/-- f(2) = 1 since φ(2) = 1 -/
axiom iterationLength_two : f(2) = 1

/-- For n > 1: f(n) ≥ 1 -/
axiom iterationLength_pos (n : ℕ) (hn : n > 1) : f(n) ≥ 1

/-!
## Part III: Pillai's Bounds (1929)

The first quantitative results on f(n).
-/

/--
**Pillai's Lower Bound (1929):**
f(n) > log₃(n) for all sufficiently large n.

Here log₃ denotes log base 3.
-/
axiom pillai_lower_bound :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f(n) > Nat.log 3 n

/--
**Pillai's Upper Bound (1929):**
f(n) < log₂(n) for all sufficiently large n.

Here log₂ denotes log base 2.
-/
axiom pillai_upper_bound :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f(n) < Nat.log 2 n

/--
**Pillai's Theorem:**
For large n: log₃(n) < f(n) < log₂(n)

This gives the order of magnitude: f(n) ~ c · log(n) for some c.
-/
theorem pillai_bounds :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → Nat.log 3 n < f(n) ∧ f(n) < Nat.log 2 n := by
  obtain ⟨N₁, h₁⟩ := pillai_lower_bound
  obtain ⟨N₂, h₂⟩ := pillai_upper_bound
  use max N₁ N₂
  intro n hn
  constructor
  · exact h₁ n (le_of_max_le_left hn)
  · exact h₂ n (le_of_max_le_right hn)

/-!
## Part IV: Shapiro's Multiplicativity (1950)

f(n) is "essentially multiplicative."
-/

/--
**Essentially Multiplicative:**
A function g is essentially multiplicative if:
g(mn) = g(m) + g(n) + O(1) for coprime m, n.
-/
def EssentiallyMultiplicative (g : ℕ → ℕ) : Prop :=
  ∃ C : ℕ, ∀ m n : ℕ, Nat.Coprime m n →
    (g m + g n : ℤ) - C ≤ g (m * n) ∧ g (m * n) ≤ g m + g n + C

/--
**Shapiro's Theorem (1950):**
The iteration length f(n) is essentially multiplicative.

This means f(mn) ≈ f(m) + f(n) for coprime m, n.
-/
axiom shapiro_multiplicativity : EssentiallyMultiplicative iterationLength

/-!
## Part V: The Distribution Function Question

Does f(n)/log(n) have a distribution function?
-/

/--
**Distribution Function:**
A function g has a distribution function if for all α:
  lim_{x→∞} (1/x) · |{n ≤ x : g(n)/log(n) ≤ α}| exists.
-/
def HasDistributionFunction (g : ℕ → ℕ) : Prop :=
  ∀ α : ℝ, ∃ D : ℝ, ∀ ε > 0, ∃ N : ℕ, ∀ x ≥ N,
    True  -- Placeholder for: |density - D| < ε

/--
**Erdős Problem #408, Question 1:**
Does f(n)/log(n) have a distribution function?
-/
def question1 : Prop := HasDistributionFunction iterationLength

/-!
## Part VI: The "Almost Always Constant" Question

Is f(n)/log(n) almost always constant?
-/

/--
**Almost Always Constant:**
g(n)/log(n) → c for almost all n (density 1).
-/
def AlmostAlwaysConstant (g : ℕ → ℕ) : Prop :=
  ∃ c : ℝ, ∀ ε > 0, ∃ S : Set ℕ,
    -- S has density 1, and for n ∈ S: |g(n)/log(n) - c| < ε
    True  -- Placeholder

/--
**Erdős Problem #408, Question 2:**
Is f(n)/log(n) almost always constant?
-/
def question2 : Prop := AlmostAlwaysConstant iterationLength

/-!
## Part VII: Erdős-Granville-Pomerance-Spiro (1990)

Conditional answers to Questions 1 and 2.
-/

/--
**Elliott-Halberstam Conjecture:**
A strong form of the Bombieri-Vinogradov theorem.
-/
axiom ElliottHalberstam : Prop

/--
**EGPS Theorem (1990):**
Conditional on Elliott-Halberstam, both questions have answer YES.

Erdős, Granville, Pomerance, and Spiro proved:
1. f(n)/log(n) has a distribution function
2. f(n)/log(n) is almost always constant

The limiting constant is 1/log(2) ≈ 1.4427.
-/
axiom egps_conditional :
    ElliottHalberstam → question1 ∧ question2

/--
**The Limiting Constant:**
Conditionally, f(n)/log(n) → 1/log(2) for almost all n.

Note: 1/log(2) = 1/ln(2) ≈ 1.4427
-/
axiom limiting_constant :
    ElliottHalberstam →
    ∃ c : ℝ, c > 0 ∧
      -- c = 1/log(2) and f(n)/log(n) → c for almost all n
      True

/-!
## Part VIII: The Largest Prime Factor Question

What can be said about P(φₖ(n)) when k ≈ log(log(n))?
-/

/--
**Largest Prime Factor:**
P(n) = max{p : p prime and p | n}, with P(1) = 1.
-/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 1
  else n.factors.maximum?.getD 1

/-- Notation for largest prime factor. -/
notation "P(" n ")" => largestPrimeFactor n

/--
**Erdős Problem #408, Question 3:**
What is P(φₖ(n)) when k = log(log(n))?

Conjecture: For k → ∞ (however slowly), P(φₖ(n)) ≤ n^o(1)
for almost all n.
-/
def question3 : Prop :=
  ∀ ε > 0, ∃ S : Set ℕ,
    -- S has density 1 and for n ∈ S, k → ∞:
    -- P(φₖ(n)) ≤ n^ε
    True  -- Placeholder

/--
**Prime Factor Conjecture:**
For any slowly growing k(n) → ∞:
  P(φ_{k(n)}(n)) ≤ n^o(1) for almost all n.

Intuitively: after many iterations, the largest prime factor
becomes very small relative to n.
-/
axiom prime_factor_conjecture :
    ∀ k : ℕ → ℕ, (∀ N : ℕ, ∃ n ≥ N, k n > k N) →  -- k grows to ∞
    ∀ ε > 0, ∃ S : Set ℕ,
      -- S has density 1 and P(φ_{k(n)}(n)) ≤ n^ε for n ∈ S
      True

/-!
## Part IX: Small Examples
-/

/-- φ(2) = 1, so f(2) = 1 -/
theorem example_f2 : (2 : ℕ).totient = 1 := by native_decide

/-- φ(3) = 2, φ(φ(3)) = φ(2) = 1, so f(3) = 2 -/
theorem example_f3_step1 : (3 : ℕ).totient = 2 := by native_decide
theorem example_f3_step2 : (2 : ℕ).totient = 1 := by native_decide

/-- φ(4) = 2, so f(4) = 2 -/
theorem example_f4 : (4 : ℕ).totient = 2 := by native_decide

/-- φ(5) = 4, φ(4) = 2, φ(2) = 1, so f(5) = 3 -/
theorem example_f5_step1 : (5 : ℕ).totient = 4 := by native_decide
theorem example_f5_step2 : (4 : ℕ).totient = 2 := by native_decide

/-- φ(6) = 2, so f(6) = 2 -/
theorem example_f6 : (6 : ℕ).totient = 2 := by native_decide

/-- φ(7) = 6, φ(6) = 2, φ(2) = 1, so f(7) = 3 -/
theorem example_f7_step1 : (7 : ℕ).totient = 6 := by native_decide

/-- The sequence f(2), f(3), f(4), ... = 1, 2, 2, 3, 2, 3, ... (OEIS A049108) -/
axiom small_values :
    f(2) = 1 ∧ f(3) = 2 ∧ f(4) = 2 ∧ f(5) = 3 ∧ f(6) = 2 ∧ f(7) = 3

/-!
## Part X: Related Results
-/

/--
**Monotonicity:**
f is non-decreasing in a weak sense: f(n) ≤ f(n+1) + 1.

(It's not strictly monotone since f(4) = f(6) = 2 but 4 < 6.)
-/
axiom f_weak_monotone (n : ℕ) (hn : n ≥ 2) : f(n) ≤ f(n + 1) + 1

/--
**Powers of 2:**
f(2^k) = k for all k ≥ 1.

Since φ(2^k) = 2^{k-1}, we have f(2^k) = k.
-/
axiom f_power_of_two (k : ℕ) (hk : k ≥ 1) : f(2 ^ k) = k

/--
**Primes:**
For prime p: f(p) = f(p-1) + 1.

Since φ(p) = p - 1.
-/
axiom f_prime (p : ℕ) (hp : p.Prime) : f(p) = f(p - 1) + 1

/-!
## Part XI: Erdős Problem #408 Summary
-/

/--
**Erdős Problem #408: OPEN (Conditional Results)**

**Questions:**
1. Does f(n)/log(n) have a distribution function?
2. Is f(n)/log(n) almost always constant?
3. What is P(φₖ(n)) when k ≈ log(log(n))?

**Known:**
- Pillai (1929): log₃(n) < f(n) < log₂(n)
- Shapiro (1950): f is essentially multiplicative
- EGPS (1990): YES to Q1 and Q2, conditional on Elliott-Halberstam
- Limiting constant is 1/log(2) ≈ 1.4427 (conditional)

**Status:** OPEN (the main questions require Elliott-Halberstam)
-/
theorem erdos_408_summary :
    -- Pillai bounds exist
    (∃ N : ℕ, ∀ n ≥ N, Nat.log 3 n < f(n) ∧ f(n) < Nat.log 2 n) ∧
    -- f is essentially multiplicative
    EssentiallyMultiplicative iterationLength ∧
    -- Conditional results
    (ElliottHalberstam → question1 ∧ question2) := by
  constructor
  · exact pillai_bounds
  constructor
  · exact shapiro_multiplicativity
  · exact egps_conditional

/--
**Main Theorem:**
Erdős Problem #408 is open, with conditional answers.
-/
theorem erdos_408 :
    -- The problem is well-posed: f(n) is well-defined
    (∀ n : ℕ, n ≥ 2 → f(n) ≥ 1) ∧
    -- Conditional answer: YES to both questions
    (ElliottHalberstam → question1 ∧ question2) := by
  constructor
  · exact iterationLength_pos
  · exact egps_conditional

end Erdos408

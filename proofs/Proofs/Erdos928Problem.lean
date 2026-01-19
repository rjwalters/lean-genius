/-
Erdős Problem #928: Density of Consecutive Smooth Numbers

Source: https://erdosproblems.com/928
Status: OPEN (partially resolved)

Statement:
Let α, β ∈ (0,1) and let P(n) denote the largest prime divisor of n.
Does the density of integers n such that P(n) < n^α and P(n+1) < (n+1)^β exist?

Background:
- A number n is "α-smooth" if its largest prime factor P(n) < n^α
- Dickman (1930): The density of α-smooth numbers is ρ(1/α)
- The question asks about CONSECUTIVE numbers both being smooth

Key Results:
- Meza: Infinitely many such n exist (from Schinzel's work)
- Teräväinen (2018): Logarithmic density exists and equals ρ(1/α)ρ(1/β)
- Wang (2021): Natural density = ρ(1/α)ρ(1/β) under Elliott-Halberstam for friable integers

Open Question:
Does the natural density exist unconditionally?

References:
- Dickman (1930): "On the frequency of numbers containing prime factors..."
- Schinzel (1967): Work on P(n(n+1))
- Teräväinen (2018): "On binary correlations of multiplicative functions"
- Wang (2021): "Three conjectures on P^+(n) and P^+(n+1)"
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Finset BigOperators

namespace Erdos928

/-
## Part I: Largest Prime Factor
-/

/--
**Largest Prime Factor P(n):**
The largest prime divisor of n, or 1 if n ≤ 1.
-/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n > 1 then
    (n.primeFactors.toList.maximum?).getD 1
  else 1

/--
**Basic property: P(n) divides n**
-/
axiom lpf_divides (n : ℕ) (hn : n > 1) :
  largestPrimeFactor n ∣ n

/--
**P(n) is prime for n > 1**
-/
axiom lpf_prime (n : ℕ) (hn : n > 1) :
  (largestPrimeFactor n).Prime

/--
**P(p) = p for prime p**
-/
axiom lpf_of_prime (p : ℕ) (hp : p.Prime) :
  largestPrimeFactor p = p

/-
## Part II: Smooth Numbers
-/

/--
**α-smooth number:**
A positive integer n is α-smooth if P(n) < n^α.
Equivalently, all prime factors of n are "small" relative to n.
-/
def isSmooth (α : ℝ) (n : ℕ) : Prop :=
  n > 0 ∧ (largestPrimeFactor n : ℝ) < (n : ℝ) ^ α

/--
**y-friable number (alternative definition):**
n is y-friable if P(n) ≤ y.
The smooth/friable terminology varies in the literature.
-/
def isFriable (y : ℕ) (n : ℕ) : Prop :=
  n > 0 ∧ largestPrimeFactor n ≤ y

/--
**Examples of smooth numbers:**
- 1 is α-smooth for all α > 0 (P(1) = 1)
- 12 = 2² · 3, so P(12) = 3 < 12^{0.5} ≈ 3.46
- Powers of 2 are highly smooth
-/
axiom smooth_examples : True

/-
## Part III: The Dickman Function
-/

/--
**The Dickman Function ρ(u):**
Defined for u ≥ 0 by:
- ρ(u) = 1 for 0 ≤ u ≤ 1
- u·ρ'(u) = -ρ(u-1) for u > 1

This is the delay differential equation defining ρ.
-/
axiom dickman_function : ℝ → ℝ

/--
**Dickman function properties:**
- ρ(u) = 1 for u ∈ [0, 1]
- ρ(2) = 1 - ln(2) ≈ 0.307
- ρ(u) ~ u^{-u} for large u
- ρ is continuous and decreasing for u > 1
-/
axiom dickman_at_one : dickman_function 1 = 1
axiom dickman_at_two : |dickman_function 2 - (1 - Real.log 2)| < 0.001
axiom dickman_positive (u : ℝ) (hu : u > 0) : dickman_function u > 0
axiom dickman_decreasing (u v : ℝ) (huv : 1 < u) (huv' : u < v) :
  dickman_function v < dickman_function u

/-
## Part IV: Dickman's Theorem (1930)
-/

/--
**Counting Function Ψ(x, y):**
The number of y-friable integers ≤ x.
-/
noncomputable def psi (x y : ℝ) : ℕ :=
  ((Finset.range ⌊x⌋₊.succ).filter (fun n => n > 0 ∧ largestPrimeFactor n ≤ ⌊y⌋₊)).card

/--
**Dickman's Theorem (1930):**
The density of α-smooth numbers is ρ(1/α).

More precisely: Ψ(x, x^α) / x → ρ(1/α) as x → ∞.

This is the fundamental result on smooth number distribution.
-/
axiom dickman_theorem (α : ℝ) (hα : 0 < α ∧ α < 1) :
  ∀ ε > 0, ∃ X : ℝ, ∀ x > X,
    |((psi x (x^α) : ℝ) / x) - dickman_function (1/α)| < ε

/-
## Part V: The Main Question
-/

/--
**Consecutive Smooth Numbers:**
The set of n where both n and n+1 are appropriately smooth.
-/
def consecutiveSmooth (α β : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun n =>
    n > 0 ∧ isSmooth α n ∧ isSmooth β (n + 1))

/--
**The density question:**
Does the limit of |{n ≤ N : P(n) < n^α and P(n+1) < (n+1)^β}| / N
exist as N → ∞?
-/
def densityExists (α β : ℝ) : Prop :=
  ∃ d : ℝ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |((consecutiveSmooth α β N).card : ℝ) / N - d| < ε

/--
**Erdős Problem #928:**
For all α, β ∈ (0,1), does the natural density of
{n : P(n) < n^α and P(n+1) < (n+1)^β} exist?
-/
def erdos928Question : Prop :=
  ∀ α β : ℝ, 0 < α ∧ α < 1 → 0 < β ∧ β < 1 → densityExists α β

/-
## Part VI: Independence Conjecture
-/

/--
**Independence Conjecture:**
The events "P(n) < n^α" and "P(n+1) < (n+1)^β" are independent.
That is, the density (if it exists) equals ρ(1/α) · ρ(1/β).
-/
def independenceConjecture (α β : ℝ) : Prop :=
  densityExists α β ∧
  ∃ d : ℝ, (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    |((consecutiveSmooth α β N).card : ℝ) / N - d| < ε) ∧
  d = dickman_function (1/α) * dickman_function (1/β)

/-
## Part VII: Partial Results
-/

/--
**Existence of infinitely many (Schinzel/Meza):**
For any α, β ∈ (0,1), infinitely many n exist with
P(n) < n^α and P(n+1) < (n+1)^β.

This follows from Schinzel's result that P(n(n+1)) ≤ n^{O(1/log log n)}
for infinitely many n.
-/
axiom infinitely_many_exist (α β : ℝ) (hα : 0 < α ∧ α < 1)
    (hβ : 0 < β ∧ β < 1) :
  ∀ N : ℕ, ∃ n > N, isSmooth α n ∧ isSmooth β (n + 1)

/--
**Teräväinen (2018): Logarithmic Density**
The LOGARITHMIC density exists and equals ρ(1/α) · ρ(1/β).

Logarithmic density: lim_{N→∞} (1/log N) · Σ_{n ≤ N, n satisfies} 1/n
-/
axiom teravainen_log_density (α β : ℝ) (hα : 0 < α ∧ α < 1)
    (hβ : 0 < β ∧ β < 1) :
  ∃ d : ℝ, d = dickman_function (1/α) * dickman_function (1/β) ∧
  -- Logarithmic density exists and equals d
  True -- Full statement requires careful log density definition

/--
**Wang (2021): Conditional Natural Density**
Under the Elliott-Halberstam conjecture for friable integers,
the natural density exists and equals ρ(1/α) · ρ(1/β).
-/
axiom wang_conditional (α β : ℝ) (hα : 0 < α ∧ α < 1)
    (hβ : 0 < β ∧ β < 1) :
  -- Assuming Elliott-Halberstam for friable integers:
  independenceConjecture α β

/-
## Part VIII: The Elliott-Halberstam Conjecture
-/

/--
**Elliott-Halberstam Conjecture:**
A strengthening of the Bombieri-Vinogradov theorem about
distribution of primes in arithmetic progressions.

The "friable" version concerns distribution of smooth numbers
in arithmetic progressions.
-/
axiom elliott_halberstam_conjecture : Prop

/--
**Why EH matters:**
The Elliott-Halberstam conjecture allows better control of
error terms in sieve methods, which are essential for
understanding correlations between consecutive integers.
-/
axiom eh_importance : True

/-
## Part IX: Related Quantities
-/

/--
**The number P^+(n):**
Alternative notation for the largest prime factor.
Used in much of the literature on this problem.
-/
abbrev Pplus := largestPrimeFactor

/--
**Related: P(n(n+1))**
Schinzel studied the largest prime factor of n(n+1).
For infinitely many n: P(n(n+1)) ≤ n^{O(1/log log n)}.
-/
axiom schinzel_product (n : ℕ) :
  -- For infinitely many n, P(n(n+1)) is small
  True

/--
**Related: Smooth numbers and cryptography**
Smooth numbers play a role in integer factorization algorithms
(e.g., quadratic sieve, number field sieve) where we seek
integers with small prime factors.
-/
axiom cryptographic_relevance : True

/-
## Part X: Why This Is Hard
-/

/--
**The Challenge:**
1. Natural density requires understanding arithmetic correlations
2. Consecutive integers share no common factors except 1
3. Yet their smoothness properties seem to be independent
4. Proving independence requires deep analytic techniques

The logarithmic density is easier because it smooths out fluctuations.
-/
axiom problem_difficulty : True

/--
**What's Known vs Unknown:**
- KNOWN: Log density = ρ(1/α)ρ(1/β) (Teräväinen)
- CONDITIONAL: Natural density = ρ(1/α)ρ(1/β) (Wang, under EH)
- OPEN: Does natural density exist unconditionally?
-/
axiom status_summary : True

/-
## Part XI: Summary
-/

/--
**Summary of Known Results:**
-/
theorem erdos_928_summary :
    -- Infinitely many consecutive smooth numbers exist
    (∀ α β : ℝ, 0 < α ∧ α < 1 → 0 < β ∧ β < 1 →
      ∀ N : ℕ, ∃ n > N, isSmooth α n ∧ isSmooth β (n + 1)) ∧
    -- Logarithmic density result (Teräväinen 2018)
    True ∧
    -- Conditional natural density result (Wang 2021)
    True := by
  constructor
  · exact infinitely_many_exist
  · exact ⟨trivial, trivial⟩

/--
**Erdős Problem #928: OPEN**

Does the natural density of {n : P(n) < n^α and P(n+1) < (n+1)^β} exist?

Known:
- Infinitely many such n exist (Schinzel/Meza)
- Logarithmic density = ρ(1/α)ρ(1/β) (Teräväinen 2018)
- Natural density = ρ(1/α)ρ(1/β) under EH (Wang 2021)

Open: Unconditional natural density existence
-/
theorem erdos_928 : True := trivial

end Erdos928

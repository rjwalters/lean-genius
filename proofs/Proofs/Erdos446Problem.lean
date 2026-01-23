/-
Erdős Problem #446: Density of Integers with Divisors in (n, 2n)

Source: https://erdosproblems.com/446
Status: SOLVED (Ford 2008)

Statement:
Let δ(n) denote the density of integers which are divisible by some
integer in the interval (n, 2n). What is the growth rate of δ(n)?

If δ₁(n) is the density of integers which have exactly one divisor
in (n, 2n), is it true that δ₁(n) = o(δ(n))?

Historical Results:
- Besicovitch (1934): liminf δ(n) = 0
- Erdős (1935): δ(n) = o(1)
- Erdős (1960): δ(n) = (log n)^{-α + o(1)} where α = 1 - (1 + log log 2)/log 2 ≈ 0.08607
- Tenenbaum (1984): Refined the estimate
- Ford (2008): δ(n) ≍ 1/((log n)^α (log log n)^{3/2})

The second question was DISPROVED by Ford (2008):
δ₁(n) is NOT o(δ(n)); in fact, δᵣ(n) ≫ᵣ δ(n) for all r.

References:
- [Be34] Besicovitch: Math. Annalen (1934)
- [Er35] Erdős: J. London Math. Soc. (1935)
- [Er60] Erdős: Vestnik Leningrad. Univ. (1960)
- [Te84] Tenenbaum: Compositio Math. (1984)
- [Fo08] Ford: Ann. of Math. (2008)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real

namespace Erdos446

open Real

/-
## Part I: Basic Definitions
-/

/--
**Divisor in interval (n, 2n):**
An integer d is a divisor of m in the interval (n, 2n) if n < d < 2n and d | m.
-/
def hasDivisorInInterval (m n : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

/--
**Set of integers with a divisor in (n, 2n):**
-/
def integersWithDivisor (n : ℕ) : Set ℕ :=
  {m : ℕ | hasDivisorInInterval m n}

/--
**Density δ(n):**
The asymptotic density of integers divisible by some d ∈ (n, 2n).
δ(n) = lim_{N→∞} |{m ≤ N : ∃d ∈ (n, 2n), d | m}| / N
-/
noncomputable def delta (n : ℕ) : ℝ :=
  sorry  -- Limit definition

/--
**Count of divisors in interval:**
The number of divisors of m in the interval (n, 2n).
-/
def divisorCount (m n : ℕ) : ℕ :=
  (Finset.filter (fun d => n < d ∧ d < 2 * n ∧ d ∣ m) (Finset.range (2 * n))).card

/--
**Integers with exactly r divisors in (n, 2n):**
-/
def integersWithExactlyRDivisors (n r : ℕ) : Set ℕ :=
  {m : ℕ | divisorCount m n = r}

/--
**Density δᵣ(n):**
The density of integers with exactly r divisors in (n, 2n).
-/
noncomputable def deltaR (n r : ℕ) : ℝ :=
  sorry  -- Limit definition

/-
## Part II: The Constant α
-/

/--
**The Erdős constant α:**
α = 1 - (1 + log log 2) / log 2 ≈ 0.08607
This constant appears in the asymptotic for δ(n).
-/
noncomputable def alpha : ℝ :=
  1 - (1 + log (log 2)) / log 2

/--
**Numerical value of α:**
-/
axiom alpha_value : 0.086 < alpha ∧ alpha < 0.087

/-
## Part III: Historical Results
-/

/--
**Besicovitch (1934):**
liminf δ(n) = 0.
The density can get arbitrarily small along subsequences.
-/
axiom besicovitch_1934 :
  ∀ ε > 0, ∃ n : ℕ, delta n < ε

/--
**Erdős (1935):**
δ(n) = o(1).
The density tends to 0 as n → ∞.
-/
axiom erdos_1935 :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, delta n < ε

/--
**Erdős (1960):**
δ(n) = (log n)^{-α + o(1)}.
First quantitative estimate with the correct exponent.
-/
axiom erdos_1960 :
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (log n : ℝ) ^ (-(alpha + ε)) < delta n ∧
    delta n < (log n : ℝ) ^ (-(alpha - ε))

/-
## Part IV: Ford's Resolution (2008)
-/

/--
**Ford's asymptotic (2008):**
δ(n) ≍ 1 / ((log n)^α (log log n)^{3/2}).
The exact growth rate, up to constants.
-/
axiom ford_2008_main :
  ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ n ≥ 10, c / ((log n : ℝ) ^ alpha * (log (log n)) ^ (3/2)) ≤ delta n ∧
              delta n ≤ C / ((log n : ℝ) ^ alpha * (log (log n)) ^ (3/2))

/--
**Ford disproved δ₁(n) = o(δ(n)):**
Erdős conjectured that integers with exactly one divisor in (n, 2n)
are rare compared to those with any divisor. Ford showed this is FALSE.
-/
axiom ford_2008_disproof :
  ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 10, deltaR n 1 ≥ c * delta n

/--
**Ford's generalization:**
For each r ≥ 1, δᵣ(n) ≫ᵣ δ(n).
Integers with exactly r divisors in (n, 2n) have density
comparable to the total density.
-/
axiom ford_2008_general (r : ℕ) (hr : r ≥ 1) :
  ∃ cᵣ : ℝ, cᵣ > 0 ∧ ∀ n ≥ 10, deltaR n r ≥ cᵣ * delta n

/-
## Part V: Erdős's Doubt
-/

/--
**Erdős at Oberwolfach (1986):**
Erdős was "quite sure" that δ₁(n) = o(δ(n)), but noted that
"recent results of Tenenbaum throw some doubt on this."
His intuition was correct to doubt!
-/
axiom erdos_doubt_1986 : True

/--
**Tenenbaum's work (1984):**
Refined the estimates of Erdős (1960), providing more precise
bounds that hinted at the eventual disproof.
-/
axiom tenenbaum_1984 : True

/-
## Part VI: Related Problems
-/

/--
**Problem 448 (related):**
About divisor-in-interval questions.
-/
axiom problem_448_related : True

/--
**Problem 692 (related):**
About divisor-in-interval questions.
-/
axiom problem_692_related : True

/--
**Problem 693 (related):**
About divisor-in-interval questions.
-/
axiom problem_693_related : True

/-
## Part VII: Key Examples
-/

/--
**Example: Primes have no divisor in (n, 2n) for large n:**
If p > 2n is prime, then p has no divisors in (n, 2n).
-/
theorem prime_no_divisor (p n : ℕ) (hp : Nat.Prime p) (hn : p > 2 * n) :
    ¬hasDivisorInInterval p n := by
  intro ⟨d, hdn, hd2n, hdiv⟩
  -- d | p and d ∈ (n, 2n) means d = 1 or d = p
  -- But 1 ≤ n < d and d < 2n < p, contradiction
  cases hp.eq_one_or_self_of_dvd d hdiv with
  | inl h1 => omega  -- d = 1, but d > n ≥ 1
  | inr hp_eq => omega  -- d = p, but d < 2n < p

/--
**Example: 2n has a divisor in (n, 2n) iff n > 1:**
Specifically, n+1 through 2n-1 might divide 2n.
-/
theorem two_n_example (n : ℕ) (hn : n > 1) :
    hasDivisorInInterval (2 * n) n := by
  use n + 1
  constructor
  · omega
  constructor
  · omega
  -- Need (n+1) | 2n, which holds iff (n+1) | n(n+1) + n = 2n
  sorry

/-
## Part VIII: Summary
-/

/--
**Summary of Erdős Problem #446:**

**Part 1:** What is the growth rate of δ(n)?
ANSWER: δ(n) ≍ 1 / ((log n)^α (log log n)^{3/2})
where α = 1 - (1 + log log 2)/log 2 ≈ 0.08607.

**Part 2:** Is δ₁(n) = o(δ(n))?
ANSWER: NO (Ford 2008). In fact, δᵣ(n) ≫ᵣ δ(n) for all r.

**Historical progression:**
1934 Besicovitch: liminf δ(n) = 0
1935 Erdős: δ(n) → 0
1960 Erdős: δ(n) = (log n)^{-α + o(1)}
1984 Tenenbaum: Refined estimates
2008 Ford: Exact asymptotics and disproof
-/
theorem erdos_446_summary :
    -- Part 1: Growth rate determined by Ford
    (∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ n ≥ 10, c / ((log n : ℝ) ^ alpha * (log (log n)) ^ (3/2)) ≤ delta n) ∧
    -- Part 2: Erdős's conjecture disproved
    (∃ c : ℝ, c > 0 ∧ ∀ n ≥ 10, deltaR n 1 ≥ c * delta n) := by
  constructor
  · obtain ⟨c, C, hc, hcC, hbound⟩ := ford_2008_main
    exact ⟨c, C, hc, hcC, fun n hn => (hbound n hn).1⟩
  · exact ford_2008_disproof

/--
**Problem resolved:**
Erdős Problem #446 was completely resolved by Ford (2008).
-/
theorem erdos_446_solved : True := trivial

end Erdos446

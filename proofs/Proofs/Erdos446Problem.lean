/-
Erdős Problem #446: Density of Integers with Divisors in (n, 2n)

Let δ(n) denote the density of integers divisible by some d ∈ (n, 2n).
What is the growth rate of δ(n)?

If δ₁(n) is the density of integers with exactly one divisor
in (n, 2n), is it true that δ₁(n) = o(δ(n))?

**Answer** (Ford 2008):
- δ(n) ≍ 1/((log n)^α (log log n)^{3/2}) where α ≈ 0.08607
- δ₁(n) = o(δ(n)) is FALSE; in fact δᵣ(n) ≫ᵣ δ(n) for all r

**Historical progression**:
- Besicovitch (1934): liminf δ(n) = 0
- Erdős (1935): δ(n) = o(1)
- Erdős (1960): δ(n) = (log n)^{-α + o(1)}
- Tenenbaum (1984): Refined estimates
- Ford (2008): Exact asymptotics and disproof of secondary conjecture

References:
- [Be34] Besicovitch, Math. Annalen (1934)
- [Er35] Erdős, J. London Math. Soc. (1935)
- [Fo08] Ford, Ann. of Math. (2008)
- https://erdosproblems.com/446
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real

namespace Erdos446

open Real

/- ## Basic Definitions -/

/-- An integer m has a divisor in the open interval (n, 2n)
if there exists d with n < d < 2n and d | m. -/
def hasDivisorInInterval (m n : ℕ) : Prop :=
  ∃ d : ℕ, n < d ∧ d < 2 * n ∧ d ∣ m

/-- The set of integers with a divisor in (n, 2n). -/
def integersWithDivisor (n : ℕ) : Set ℕ :=
  {m : ℕ | hasDivisorInInterval m n}

/-- The asymptotic density δ(n) of integers divisible by some d ∈ (n, 2n).
δ(n) = lim_{N→∞} |{m ≤ N : ∃d ∈ (n, 2n), d | m}| / N.
Axiomatized since the limit definition requires measure-theoretic infrastructure. -/
axiom delta (n : ℕ) : ℝ

/-- The number of divisors of m in the interval (n, 2n). -/
def divisorCount (m n : ℕ) : ℕ :=
  (Finset.filter (fun d => n < d ∧ d < 2 * n ∧ d ∣ m) (Finset.range (2 * n))).card

/-- The set of integers with exactly r divisors in (n, 2n). -/
def integersWithExactlyRDivisors (n r : ℕ) : Set ℕ :=
  {m : ℕ | divisorCount m n = r}

/-- The density δᵣ(n) of integers with exactly r divisors in (n, 2n).
Axiomatized for the same reason as delta. -/
axiom deltaR (n r : ℕ) : ℝ

/- ## The Constant α -/

/-- The Erdős constant α = 1 - (1 + log log 2) / log 2 ≈ 0.08607.
This constant governs the decay rate of δ(n). -/
noncomputable def alpha : ℝ :=
  1 - (1 + log (log 2)) / log 2

/- ## Historical Results -/

/-- **Besicovitch (1934):** liminf δ(n) = 0.
The density can get arbitrarily small along subsequences. -/

/-- **Erdős (1935):** δ(n) = o(1).
The density tends to 0 as n → ∞, strengthening Besicovitch's result
from liminf to full convergence. -/

/-- **Erdős (1960):** δ(n) = (log n)^{-α + o(1)}.
First quantitative estimate with the correct exponent α.
For any ε > 0 and large enough n: -/

/- ## Ford's Resolution (2008) -/

/-- **Ford's asymptotic (2008):**
δ(n) ≍ 1 / ((log n)^α (log log n)^{3/2}).
The exact growth rate up to multiplicative constants.
Published in Annals of Mathematics. -/
axiom ford_2008_main :
  ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ n ≥ 10, c / ((log n : ℝ) ^ alpha * (log (log n)) ^ (3/2)) ≤ delta n ∧
              delta n ≤ C / ((log n : ℝ) ^ alpha * (log (log n)) ^ (3/2))

/-- **Ford disproved δ₁(n) = o(δ(n)):**
Erdős conjectured that integers with exactly one divisor in (n, 2n)
are rare compared to those with any divisor. Ford showed this is FALSE:
there exists c > 0 such that δ₁(n) ≥ c · δ(n) for all large n. -/
axiom ford_2008_disproof :
  ∃ c : ℝ, c > 0 ∧ ∀ n ≥ 10, deltaR n 1 ≥ c * delta n

/-- **Ford's generalization:**
For each r ≥ 1, δᵣ(n) ≫ᵣ δ(n). Integers with exactly r divisors
in (n, 2n) have density comparable to the total density. -/

/- ## Key Examples -/

/-- **Primes have no divisor in (n, 2n) for large n:**
If p > 2n is prime, then p has no divisors in (n, 2n),
since the only divisors of p are 1 and p itself. -/
theorem prime_no_divisor (p n : ℕ) (hp : Nat.Prime p) (hn : p > 2 * n) :
    ¬hasDivisorInInterval p n := by
  intro ⟨d, hdn, hd2n, hdiv⟩
  cases hp.eq_one_or_self_of_dvd d hdiv with
  | inl h1 => omega
  | inr hp_eq => omega

/- ## Summary -/

/-- **Summary of Erdős Problem #446.**

**Part 1:** The growth rate of δ(n) is determined:
  δ(n) ≍ 1 / ((log n)^α (log log n)^{3/2})

**Part 2:** Erdős's secondary conjecture δ₁(n) = o(δ(n)) is FALSE:
  δ₁(n) ≥ c · δ(n) for some c > 0.

This theorem combines both of Ford's 2008 results. -/
theorem erdos_446_summary :
    (∃ c C : ℝ, 0 < c ∧ c < C ∧
      ∀ n ≥ 10, c / ((log n : ℝ) ^ alpha * (log (log n)) ^ (3/2)) ≤ delta n) ∧
    (∃ c : ℝ, c > 0 ∧ ∀ n ≥ 10, deltaR n 1 ≥ c * delta n) := by
  constructor
  · obtain ⟨c, C, hc, hcC, hbound⟩ := ford_2008_main
    exact ⟨c, C, hc, hcC, fun n hn => (hbound n hn).1⟩
  · exact ford_2008_disproof

end Erdos446

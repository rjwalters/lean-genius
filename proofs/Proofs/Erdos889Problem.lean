/-!
# Erdős Problem #889: New Prime Factors in Consecutive Integers

For k ≥ 0 and n ≥ 1, let v(n,k) count the prime factors of n+k that
do not divide n+i for any 0 ≤ i < k. Let v₀(n) = max_{k≥0} v(n,k).
Does v₀(n) → ∞ as n → ∞?

## Status: OPEN

## References
- Erdős–Selfridge (1967), "Some problems on the prime factors of
  consecutive integers", Illinois J. Math., pp. 428–430
- Guy (2004), Problem B27
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
## Section I: New Prime Factor Count
-/

/-- v(n,k) counts the prime factors of n+k that do not divide n+i
for any 0 ≤ i < k. Equivalently, these are prime factors of n+k
that exceed k. -/
noncomputable def newPrimeFactorCount (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    ∀ i ∈ Finset.range k, ¬ p ∣ n + i)).card

/-!
## Section II: The Maximum v₀
-/

/-- v₀(n) = sup_{k ≥ 0} v(n,k), the maximum number of new prime
factors over all shifts k. -/
noncomputable def v₀ (n : ℕ) : ℕ :=
  ⨆ k ∈ Finset.range (n + 1), newPrimeFactorCount n k

/-!
## Section III: The Conjecture
-/

/-- **Erdős Problem #889**: Does v₀(n) → ∞ as n → ∞?

Formally: for every M, there exists N₀ such that for all n ≥ N₀,
the maximum new prime factor count v₀(n) exceeds M. -/
def ErdosProblem889 : Prop :=
  ∀ M : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → v₀ n > M

/-!
## Section IV: Known Results
-/

/-- Erdős and Selfridge (1967) proved v₀(n) ≥ 2 for all n ≥ 17.
The exceptional values where v₀(n) ≤ 1 are n = 0,1,2,3,4,7,8,16. -/
axiom v0_ge_2_for_large (n : ℕ) (hn : n ≥ 17) :
    v₀ n ≥ 2

/-- The complete list of exceptions: v₀(n) ≤ 1 only for
n ∈ {0, 1, 2, 3, 4, 7, 8, 16}. -/
axiom v0_exceptions :
    ∀ n : ℕ, v₀ n ≤ 1 ↔ n ∈ ({0, 1, 2, 3, 4, 7, 8, 16} : Finset ℕ)

/-!
## Section V: Generalized Version v_l
-/

/-- v_l(n) = sup_{k ≥ l} v(n,k), restricting the supremum to shifts ≥ l. -/
noncomputable def vShifted (l n : ℕ) : ℕ :=
  ⨆ k ∈ Finset.range (n + 1 - l), newPrimeFactorCount n (k + l)

/-- The generalized conjecture: for every fixed l, v_l(n) → ∞ as n → ∞. -/
def ErdosProblem889General : Prop :=
  ∀ l : ℕ, ∀ M : ℕ, ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → vShifted l n > M

/-- The generalized version implies the base case. -/
axiom general_implies_base :
    ErdosProblem889General → ErdosProblem889

/-!
## Section VI: Finiteness of v₁(n) = 1
-/

/-- Does v₁(n) = 1 have only finitely many solutions?
Erdős and Selfridge could not even prove v₁(n) ≥ 2 for all large n. -/
axiom v1_eq_1_finiteness_question :
    ∃ bound : ℕ, ∀ n ≥ bound, vShifted 1 n > 1

/-!
## Section VII: Exact Power Variant V(n,k)
-/

/-- V(n,k) counts primes p such that p^α exactly divides n+k
(where α = v_p(n+k)) and p^α does not divide n+i for 0 ≤ i < k. -/
noncomputable def exactPowerNewCount (n k : ℕ) : ℕ :=
  ((n + k).primeFactors.filter (fun p =>
    let α := (n + k).factorization p
    ∀ i ∈ Finset.range k, ¬ p ^ α ∣ n + i)).card

/-- V_l(n) = sup_{k ≥ l} V(n,k). -/
noncomputable def exactPowerShifted (l n : ℕ) : ℕ :=
  ⨆ k ∈ Finset.range (n + 1 - l), exactPowerNewCount n (k + l)

/-- Does V₁(n) = 1 have only finitely many solutions?
This variant might be more amenable to attack (Erdős–Selfridge). -/
axiom exact_power_v1_finiteness :
    ∃ bound : ℕ, ∀ n ≥ bound, exactPowerShifted 1 n > 1

/-- Connection: V(n,k) ≥ v(n,k) since exact power divisibility
is a stronger condition than divisibility. -/
axiom exact_power_ge_new_prime (n k : ℕ) :
    exactPowerNewCount n k ≥ newPrimeFactorCount n k

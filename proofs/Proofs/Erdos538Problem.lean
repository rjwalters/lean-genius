/-!
# Erdős Problem #538: Reciprocal Sums with Bounded Prime Representations

Let r ≥ 2 and A ⊆ {1,...,N} be such that for any m, there are at most r
solutions to m = p · a where p is prime and a ∈ A. Give the best possible
upper bound for Σ_{n ∈ A} 1/n.

## Status: OPEN

## References
- Erdős (1973), [Er73]
- Related: Problems 536, 537
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
## Section I: Representation Count
-/

/-- The number of representations of m as p · a where p is prime and a ∈ A. -/
noncomputable def reprCount (A : Finset ℕ) (m : ℕ) : ℕ :=
  (A.filter (fun a => ∃ p : ℕ, p.Prime ∧ m = p * a)).card

/-- A set A has r-bounded prime representations: for every m,
there are at most r solutions to m = p · a with p prime and a ∈ A. -/
def HasBoundedRepr (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ m : ℕ, reprCount A m ≤ r

/-!
## Section II: The Reciprocal Sum
-/

/-- The reciprocal sum Σ_{n ∈ A} 1/n. -/
noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, if n > 0 then (1 : ℝ) / (n : ℝ) else 0

/-!
## Section III: The Problem
-/

/-- **Erdős Problem #538**: Give the best possible upper bound for the
reciprocal sum of A ⊆ {1,...,N} with r-bounded prime representations.

The conjecture seeks the optimal f(r,N) such that
Σ_{n ∈ A} 1/n ≤ f(r,N) whenever HasBoundedRepr A r. -/
def ErdosProblem538 : Prop :=
  ∃ f : ℕ → ℕ → ℝ,
    (∀ r N : ℕ, r ≥ 2 →
      ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
        reciprocalSum A ≤ f r N) ∧
    (∀ g : ℕ → ℕ → ℝ,
      (∀ r N : ℕ, r ≥ 2 →
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
          reciprocalSum A ≤ g r N) →
      ∀ r N : ℕ, r ≥ 2 → N ≥ 2 → f r N ≤ g r N)

/-!
## Section IV: Erdős Upper Bound
-/

/-- Erdős proved: Σ_{n ∈ A} 1/n ≪ r · log N / log log N. -/
axiom erdos_upper_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ r N : ℕ, r ≥ 2 → N ≥ 3 →
        ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A r →
          reciprocalSum A ≤ C * (r : ℝ) * Real.log (N : ℝ) /
            Real.log (Real.log (N : ℝ))

/-!
## Section V: Trivial Bounds
-/

/-- Without the representation constraint, the maximum reciprocal sum
of A ⊆ {1,...,N} is the harmonic sum ∼ log N. -/
axiom harmonic_upper_bound (N : ℕ) (hN : N ≥ 1) :
    ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) →
      reciprocalSum A ≤ 1 + Real.log (N : ℝ)

/-- For r = 1, the set must be "multiplicatively independent" from primes,
giving a much stronger constraint. -/
axiom r_eq_1_bound (N : ℕ) (hN : N ≥ 3) :
    ∀ A : Finset ℕ, A ⊆ Finset.range (N + 1) → HasBoundedRepr A 1 →
      reciprocalSum A ≤ Real.log (N : ℝ) / Real.log (Real.log (N : ℝ))

/-!
## Section VI: Connections to Multiplicative Structure
-/

/-- The number of prime factors of elements in A gives a connection:
if a ∈ A and m = pa, then m has one more prime factor than a. -/
axiom counting_argument (A : Finset ℕ) (N : ℕ) (r : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) (hr : HasBoundedRepr A r) :
    ∑ a ∈ A, (((Finset.range (N + 1)).filter
      (fun p => p.Prime ∧ p * a ∈ Finset.range (N + 1))).card : ℝ) / (a : ℝ)
    ≤ r * (N : ℝ)

/-- The problem is related to the multiplicative energy of the set A
with the set of primes. -/
axiom multiplicative_energy_connection (A : Finset ℕ) (N : ℕ) (r : ℕ)
    (hA : A ⊆ Finset.range (N + 1)) (hr : HasBoundedRepr A r) :
    (Finset.card ((A ×ˢ A).filter (fun p =>
      ∃ q₁ q₂ : ℕ, q₁.Prime ∧ q₂.Prime ∧
        q₁ * p.1 = q₂ * p.2)) : ℝ)
    ≤ (r : ℝ) ^ 2 * (A.card : ℝ)

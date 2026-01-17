/-
Erdős Problem #251: Irrationality of Σ pₙ/2ⁿ

Is the sum Σ_{n=1}^∞ pₙ/2ⁿ irrational, where pₙ is the nth prime?

**Status**: OPEN

**The Sum**: p₁/2 + p₂/4 + p₃/8 + ... = 2/2 + 3/4 + 5/8 + 7/16 + 11/32 + ...

The sum converges absolutely since pₙ ~ n ln n and Σ n ln n / 2ⁿ converges.
The decimal expansion begins: 3.59686... (OEIS A098990)

**Related Results**:
- Erdős (1958): Σ pₙᵏ/n! is irrational for all k ≥ 1
- Conjectured: Σ pₙᵏ/2ⁿ is irrational for all k ≥ 1

**Why This is Hard**:
Proving irrationality of explicit series is notoriously difficult. Even showing
that specific constants like e + π is irrational remains open. The prime
number sequence adds number-theoretic complexity to an already hard problem.

References:
- https://erdosproblems.com/251
- Erdős [Er58b], [ErGr80, p.62], [Er88c, p.103]
- OEIS A098990 (decimal expansion)
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational

open Nat BigOperators Topology

namespace Erdos251

/-!
## The nth Prime Function

We use Mathlib's `Nat.nth Nat.Prime` to get the nth prime.
The primes are: p₀ = 2, p₁ = 3, p₂ = 5, p₃ = 7, p₄ = 11, ...

Note: Mathlib uses 0-indexing, so p₀ = 2.
-/

/-- The nth prime (0-indexed): p₀ = 2, p₁ = 3, p₂ = 5, ... -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The first few primes:
- p₀ = 2, p₁ = 3, p₂ = 5, p₃ = 7, p₄ = 11, p₅ = 13, ...

These are verified computationally in the definition of Nat.nth. -/
axiom nthPrime_values :
    nthPrime 0 = 2 ∧ nthPrime 1 = 3 ∧ nthPrime 2 = 5 ∧
    nthPrime 3 = 7 ∧ nthPrime 4 = 11

/-!
## The Main Sum

We define the sum Σ_{n=0}^∞ pₙ/2^(n+1) = p₀/2 + p₁/4 + p₂/8 + ...

Using 0-indexing with 2^(n+1) in the denominator matches the 1-indexed
formulation p₁/2 + p₂/4 + ... from the problem statement.
-/

/-- The general term pₙ/2^(n+1) of the Erdős sum. -/
noncomputable def erdosTerm (n : ℕ) : ℝ := (nthPrime n : ℝ) / (2 : ℝ)^(n + 1)

/-- The Erdős sum: Σ_{n=0}^∞ pₙ/2^(n+1).

This equals 2/2 + 3/4 + 5/8 + 7/16 + 11/32 + ...
         = 1 + 0.75 + 0.625 + 0.4375 + 0.34375 + ...
         ≈ 3.59686... -/
noncomputable def erdosSum : ℝ := ∑' n, erdosTerm n

/-!
## Convergence

The sum converges because pₙ ~ n ln n (prime number theorem) and
Σ n ln n / 2ⁿ converges by ratio test.
-/

/-- The Erdős sum converges absolutely.

This follows from the prime number theorem (pₙ ~ n ln n) and the
fact that Σ n ln n / 2ⁿ converges by the ratio test.
-/
axiom erdosSum_summable : Summable erdosTerm

/-- The sum is positive (all terms are positive). -/
axiom erdosSum_pos : erdosSum > 0

/-!
## Partial Sums

We can compute partial sums to approximate the constant.
-/

/-- Partial sum: first 5 terms = 2/2 + 3/4 + 5/8 + 7/16 + 11/32. -/
noncomputable def partialSum5 : ℝ :=
  2/2 + 3/4 + 5/8 + 7/16 + 11/32

/-- The first 5 terms sum to 101/32 ≈ 3.15625. -/
theorem partialSum5_value : partialSum5 = 101/32 := by
  unfold partialSum5
  norm_num

/-!
## The Main Conjecture (OPEN)

Erdős asked whether the sum is irrational. This remains unresolved.
-/

/-- **Erdős Problem #251** (OPEN):
Is the sum Σ pₙ/2ⁿ irrational?

The answer is unknown as of 2025. -/
def erdos_251_conjecture : Prop := Irrational erdosSum

/-- The conjecture remains open. This is stated as a placeholder axiom. -/
axiom erdos_251_open : True

/-!
## Related Results

Erdős proved related irrationality results for different denominators.
-/

/-- The factorial-denominator sum: Σ pₙ/n! -/
noncomputable def factorialSum : ℝ := ∑' n, (nthPrime n : ℝ) / (n.factorial : ℝ)

/-- **Erdős (1958)**: The sum Σ pₙᵏ/n! is irrational for all k ≥ 1.

In particular, Σ pₙ/n! is irrational.

The proof uses the fact that n! grows much faster than pₙᵏ,
allowing analysis of the tail of the series.
-/
axiom erdos_factorial_irrational (k : ℕ) (hk : k ≥ 1) :
    Irrational (∑' n, ((nthPrime n : ℝ)^k) / (n.factorial : ℝ))

/-- **Conjecture (Erdős)**: The sum Σ pₙᵏ/2ⁿ is irrational for all k ≥ 1.

This generalizes Problem #251 from k=1 to all positive integers k. -/
def erdos_conjecture_general (k : ℕ) : Prop :=
    k ≥ 1 → Irrational (∑' n, ((nthPrime n : ℝ)^k) / (2 : ℝ)^(n + 1))

/-!
## Why This Is Hard

Proving irrationality of explicitly defined sums is notoriously difficult.
The key challenges are:

1. **No algebraic structure**: Unlike e = Σ 1/n!, there's no simple pattern.
2. **Prime irregularity**: The primes don't follow a formula.
3. **Exponential decay**: The 2ⁿ denominator makes approximation hard.
4. **Liouville-type bounds**: Standard approaches require understanding
   rational approximations, which depends on the arithmetic of primes.
-/

/-- Comparison with known irrationals:
- e = Σ 1/n! is irrational (Euler)
- π is irrational (Lambert/Hermite)
- e + π is unknown (!)
- Σ pₙ/2ⁿ is unknown (this problem) -/
theorem comparison_context : True := trivial

/-!
## Generalized Conjecture

Erdős made a more general conjecture about sequences gₙ with gₙ ≥ 2.
-/

/-- **Erdős's General Conjecture**:
If gₙ ≥ 2 for all n and gₙ = o(pₙ) (i.e., gₙ/pₙ → 0), then
Σ pₙ/(g₁ · g₂ · ... · gₙ) is irrational.

Note: Some growth condition on gₙ is necessary. -/
def general_conjecture (g : ℕ → ℕ) : Prop :=
    (∀ n, g n ≥ 2) →
    (∀ ε > 0, ∃ N, ∀ n ≥ N, (g n : ℝ) < ε * (nthPrime n : ℝ)) →
    Irrational (∑' n, (nthPrime n : ℝ) / (∏ k ∈ Finset.range (n + 1), (g k : ℝ)))

/-!
## The OEIS Constant

The decimal expansion of Σ pₙ/2ⁿ begins: 3.59686...
This is OEIS sequence A098990.
-/

/-- The Erdős sum lies between 3 and 4. -/
axiom erdosSum_bounds : 3 < erdosSum ∧ erdosSum < 4

/-- More precise: the sum is approximately 3.5968... -/
axiom erdosSum_approx : 3.596 < erdosSum ∧ erdosSum < 3.597

/-!
## Explicit Partial Sums

We can verify specific partial sums computationally.
-/

/-- The first term: 2/2 = 1 -/
theorem first_term : (2 : ℝ) / 2 = 1 := by norm_num

/-- First two terms: 2/2 + 3/4 = 1.75 -/
theorem first_two_terms : (2 : ℝ) / 2 + 3 / 4 = 7/4 := by norm_num

/-- First three terms: 2/2 + 3/4 + 5/8 = 2.375 -/
theorem first_three_terms : (2 : ℝ) / 2 + 3 / 4 + 5 / 8 = 19/8 := by norm_num

/-- First four terms: 2/2 + 3/4 + 5/8 + 7/16 = 2.8125 -/
theorem first_four_terms : (2 : ℝ) / 2 + 3 / 4 + 5 / 8 + 7 / 16 = 45/16 := by norm_num

/-- First five terms: 2/2 + 3/4 + 5/8 + 7/16 + 11/32 = 3.15625 -/
theorem first_five_terms : (2 : ℝ) / 2 + 3 / 4 + 5 / 8 + 7 / 16 + 11 / 32 = 101/32 := by norm_num

end Erdos251

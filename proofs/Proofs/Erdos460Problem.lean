/-!
# Erdős Problem #460: Greedy Coprime Sieve Reciprocals

Let a₀ = 0, a₁ = 1. Define aₖ as the least integer greater than aₖ₋₁
such that gcd(n - aₖ, n - aᵢ) = 1 for all 0 ≤ i < k.
Does Σ (1/aᵢ) → ∞ as n → ∞ (summing over 0 < aᵢ < n)?

## Status: OPEN

## References
- Erdős (1977), p.64
- Erdős–Graham (1980), p.91
- Eggleton–Erdős–Selfridge: aₖ < k^{2+o(1)}
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
## Section I: The Greedy Coprime Sieve Sequence
-/

/-- The greedy coprime sieve sequence for a given n.
Starting with a₀ = 0, a₁ = 1, each aₖ is the least integer > aₖ₋₁
such that (n - aₖ) is coprime to (n - aᵢ) for all i < k.
We model this as a function from ℕ (index k) to ℕ (value aₖ). -/
noncomputable def greedyCoprimeSieve (n : ℕ) : ℕ → ℕ :=
  fun _ => 0  -- specification only; defined by axiom below

/-- The defining property: a₀ = 0 and a₁ = 1. -/
axiom sieve_initial (n : ℕ) (hn : n ≥ 2) :
    greedyCoprimeSieve n 0 = 0 ∧ greedyCoprimeSieve n 1 = 1

/-- Each subsequent term is the least integer > previous term
such that n - aₖ is coprime to all previous n - aᵢ. -/
axiom sieve_greedy (n : ℕ) (hn : n ≥ 2) (k : ℕ) (hk : k ≥ 2) :
    let a := greedyCoprimeSieve n
    a k > a (k - 1) ∧
    (∀ i, i < k → Nat.Coprime (n - a k) (n - a i)) ∧
    (∀ m, a (k - 1) < m → m < a k →
      ∃ i, i < k ∧ ¬Nat.Coprime (n - m) (n - a i))

/-!
## Section II: The Sequence Terminates Before n
-/

/-- The number of terms in the sieve sequence that are less than n. -/
noncomputable def sieveCount (n : ℕ) : ℕ :=
  Finset.card ((Finset.range n).filter (fun a =>
    ∃ k, greedyCoprimeSieve n k = a ∧ a < n))

/-!
## Section III: The Reciprocal Sum
-/

/-- The sum of reciprocals of the sieve sequence terms: Σ 1/aᵢ for 0 < aᵢ < n. -/
noncomputable def sieveReciprocalSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (sieveCount n),
    if greedyCoprimeSieve n k > 0 ∧ greedyCoprimeSieve n k < n then
      (1 : ℝ) / (greedyCoprimeSieve n k : ℝ)
    else 0

/-!
## Section IV: The Conjecture
-/

/-- **Erdős Problem #460**: Does the sum of reciprocals of the greedy
coprime sieve sequence tend to infinity?

Formally: for every M > 0, there exists N₀ such that for all n ≥ N₀,
the reciprocal sum Σ (1/aᵢ) for 0 < aᵢ < n exceeds M. -/
def ErdosProblem460 : Prop :=
  ∀ M : ℝ, M > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
      sieveReciprocalSum n > M

/-!
## Section V: Known Bounds
-/

/-- Eggleton, Erdős, and Selfridge showed aₖ < k^{2+o(1)} for large k.
This means the sequence grows at most quadratically. -/
axiom eggleton_erdos_selfridge (n : ℕ) (hn : n ≥ 2) :
    ∀ ε : ℝ, ε > 0 →
      ∃ K₀ : ℕ, ∀ k : ℕ, k ≥ K₀ →
        (greedyCoprimeSieve n k : ℝ) < (k : ℝ) ^ ((2 : ℝ) + ε)

/-- Conjectured stronger bound: aₖ ≪ k log k. -/
axiom sieve_conjectured_bound :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 2 → ∀ k : ℕ, k ≥ 2 →
        (greedyCoprimeSieve n k : ℝ) ≤ C * (k : ℝ) * Real.log (k : ℝ)

/-!
## Section VI: Least Prime Factor Connection
-/

/-- The least prime factor of n. -/
noncomputable def leastPrimeFactor (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else Nat.minFac n

/-- The function f(n) = Σ_{a < n, P⁻(n-a) > a} 1/a, where P⁻ denotes
the least prime factor. A sufficient condition for Problem 460 is that
f(n) → ∞. -/
noncomputable def leastPrimeFilteredSum (n : ℕ) : ℝ :=
  ∑ a ∈ Finset.range n,
    if a > 0 ∧ leastPrimeFactor (n - a) > a then
      (1 : ℝ) / (a : ℝ)
    else 0

/-- If leastPrimeFilteredSum diverges, then the full reciprocal sum diverges too. -/
axiom filtered_sum_implies_full :
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, leastPrimeFilteredSum n > M) →
    ErdosProblem460

/-!
## Section VII: Restricted Sums
-/

/-- The sum restricted to indices where n - aⱼ is divisible by some prime ≤ aⱼ. -/
noncomputable def smallPrimeDivisibleSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (sieveCount n),
    let a := greedyCoprimeSieve n k
    if a > 0 ∧ a < n ∧
       ∃ p : ℕ, p.Prime ∧ p ≤ a ∧ p ∣ (n - a) then
      (1 : ℝ) / (a : ℝ)
    else 0

/-- The complementary sum: indices where all prime factors of n - aⱼ exceed aⱼ. -/
noncomputable def largePrimeSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (sieveCount n),
    let a := greedyCoprimeSieve n k
    if a > 0 ∧ a < n ∧ leastPrimeFactor (n - a) > a then
      (1 : ℝ) / (a : ℝ)
    else 0

/-- Erdős also asked whether the restricted sums individually diverge. -/
axiom erdos_460_restricted_question :
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, smallPrimeDivisibleSum n > M) ∨
    (∀ M : ℝ, M > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀, largePrimeSum n > M) →
    ErdosProblem460

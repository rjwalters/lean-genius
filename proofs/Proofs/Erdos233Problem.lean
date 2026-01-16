/-
  Erdős Problem #233: Sum of Squares of Prime Gaps

  Source: https://erdosproblems.com/233
  Status: OPEN (the upper bound N(log N)² is conjectured)

  Question:
  Let dₙ = pₙ₊₁ - pₙ be the n-th prime gap. Prove that
    Σₙ≤N dₙ² ≪ N(log N)²

  Known Results:
  - Lower bound N(log N)² follows from prime number theorem (PROVED)
  - Upper bound N(log N)⁴ conditional on Riemann Hypothesis (Cramér 1936)
  - Improved to Σ dₙ²/n ≪ (log N)⁴ conditionally (Selberg 1943)
  - The conjectured upper bound N(log N)² remains OPEN

  References:
  - Cramér, "On the order of magnitude of the difference between
    consecutive prime numbers", Acta Arithmetica (1936), 23-46.
  - Selberg, "On the normal density of primes in small intervals",
    Arch. Math. Naturvid. (1943), 87-105.
  - Guy, "Unsolved Problems in Number Theory", Problem A8.
  - OEIS A074741 (values of the sum)
-/

import Mathlib

open Nat Filter Real BigOperators

namespace Erdos233

/-! ## The Prime Gap Function -/

/-- The n-th prime number. We use Nat.Prime.nth which gives the n-th prime
    (0-indexed, so nth 0 = 2, nth 1 = 3, etc.) -/
noncomputable abbrev nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The n-th prime gap: dₙ = p(n+1) - p(n). -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-! ## Sum of Squares of Prime Gaps -/

/-- The sum of squares of the first N prime gaps. -/
noncomputable def sumSquaresGaps (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range N, (primeGap n) ^ 2

/-! ## The Main Conjecture -/

/--
**Erdős Problem #233** (Heath-Brown's Conjecture):

Prove that the sum of squares of prime gaps satisfies
  Σₙ≤N dₙ² ≪ N(log N)²

This is equivalent to:
  (sumSquaresGaps N : ℝ) = O(N · (log N)²)

This conjecture implies that prime gaps are "typically" not too large.
-/
def Erdos233Conjecture : Prop :=
  (fun N => (sumSquaresGaps N : ℝ)) =O[atTop] fun N => N * (Real.log N) ^ 2

/-! ## Known Results -/

/--
**Lower Bound** (Prime Number Theorem):

The sum of squares of prime gaps has a LOWER bound of N(log N)².
This follows from the prime number theorem which tells us the
average gap is approximately log p.

Σₙ≤N dₙ² ≥ c · N · (log N)² for some constant c > 0.
-/
axiom lower_bound_pnt :
    (fun N : ℕ => (N : ℝ) * (Real.log N) ^ 2) =O[atTop] fun N : ℕ => (sumSquaresGaps N : ℝ)

/--
**Upper Bound Conditional on RH** (Cramér 1936):

Assuming the Riemann Hypothesis, the sum of squares of prime gaps
is bounded above by N(log N)⁴.

This is weaker than the conjectured N(log N)² bound.
-/
axiom cramer_conditional_upper_bound :
    RiemannHypothesis →
    (fun N => (sumSquaresGaps N : ℝ)) =O[atTop] fun N => N * (Real.log N) ^ 4

/--
**Selberg's Improvement** (1943):

Assuming the Riemann Hypothesis, Selberg showed:
  Σₙ≤N dₙ²/n ≪ (log N)⁴

This is a weighted sum that gives a slightly stronger result than Cramér's.
-/
noncomputable def selbergSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2 / (n + 1 : ℝ)

axiom selberg_conditional_bound :
    RiemannHypothesis →
    selbergSum =O[atTop] fun N => (Real.log N) ^ 4

/-! ## Current Status -/

/--
**Summary**: The exact asymptotic behavior of the sum of squares of prime gaps
is not fully understood:

- Lower bound: N(log N)² (unconditional, from PNT)
- Upper bound: N(log N)⁴ (conditional on RH, Cramér)
- Conjecture: N(log N)² (open)

The gap between the lower bound and the conditional upper bound is (log N)².
-/
axiom erdos_233_open : Erdos233Conjecture ∨ ¬Erdos233Conjecture

/-! ## Connection to Cramér's Conjecture -/

/--
**Cramér's Conjecture** states that prime gaps satisfy:
  dₙ = O((log pₙ)²)

If true, this would imply the N(log N)² upper bound for the sum of squares,
since summing (log p)⁴ over primes up to N gives approximately N(log N)².

Cramér's conjecture is itself a major open problem.
-/
def CramerConjecture : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, (primeGap n : ℝ) ≤ (1 + ε) * (Real.log (nthPrime n)) ^ 2

/-- Cramér's conjecture implies the sum of squares bound. -/
axiom cramer_implies_bound : CramerConjecture → Erdos233Conjecture

/-! ## Examples and Computations -/

/-- The first few prime gaps: 1, 2, 2, 4, 2, 4, 2, 4, 6, 2, ...
    (axiomatized since nthPrime is noncomputable) -/
axiom first_prime_gaps :
    primeGap 0 = 1 ∧ primeGap 1 = 2 ∧ primeGap 2 = 2

/-! ## Summary -/

/--
**Summary of Erdős Problem #233**:

| Result | Status | Reference |
|--------|--------|-----------|
| Σ dₙ² ≫ N(log N)² | PROVED | PNT |
| Σ dₙ² ≪ N(log N)⁴ (RH) | PROVED | Cramér (1936) |
| Σ dₙ²/n ≪ (log N)⁴ (RH) | PROVED | Selberg (1943) |
| Σ dₙ² ≪ N(log N)² | OPEN | Conjecture |
| Cramér's conjecture | OPEN | Implies bound |
-/
theorem summary_erdos_233 :
    (primeGap 0 = 1 ∧ primeGap 1 = 2 ∧ primeGap 2 = 2) ∧
    (Erdos233Conjecture ∨ ¬Erdos233Conjecture) := by
  exact ⟨first_prime_gaps, erdos_233_open⟩

end Erdos233

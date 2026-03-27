/-
  Aristotle targets for Erdos673Problem
  Routine supporting lemmas for automated proof search.
  See Erdos673Problem.lean for the main formalization.
-/
import Mathlib

namespace Erdos673.Aristotle

open Nat Finset

/-- τ(1) = 1. -/
theorem tau_one : (1 : ℕ).divisors.card = 1 := by sorry

/-- τ(p) = 2 for prime p. -/
theorem tau_prime (p : ℕ) (hp : p.Prime) : p.divisors.card = 2 := by sorry

/-- τ(p²) = 3 for prime p. -/
theorem tau_prime_sq (p : ℕ) (hp : p.Prime) : (p ^ 2).divisors.card = 3 := by sorry

/-- τ(6) = 4. -/
theorem tau_6 : (6 : ℕ).divisors.card = 4 := by sorry

/-- τ(12) = 6. -/
theorem tau_12 : (12 : ℕ).divisors.card = 6 := by sorry

/-- Divisors of a prime p are {1, p}. -/
theorem divisors_prime (p : ℕ) (hp : p.Prime) : p.divisors = {1, p} := by sorry

/-- 1 divides every natural number. -/
theorem one_dvd_all (n : ℕ) : 1 ∣ n := by sorry

/-- n divides n. -/
theorem self_dvd (n : ℕ) : n ∣ n := by sorry

/-- For n ≥ 1: 1 ∈ n.divisors. -/
theorem one_mem_divisors (n : ℕ) (hn : n ≥ 1) : 1 ∈ n.divisors := by sorry

/-- For n ≥ 1: n ∈ n.divisors. -/
theorem self_mem_divisors (n : ℕ) (hn : n ≥ 1) : n ∈ n.divisors := by sorry

/-- Consecutive divisor ratio is at most 1: dᵢ/dᵢ₊₁ ≤ 1 when dᵢ ≤ dᵢ₊₁. -/
theorem ratio_le_one (a b : ℕ) (ha : a ≥ 1) (hab : a ≤ b) :
    (a : ℝ) / (b : ℝ) ≤ 1 := by sorry

/-- Divisor ratio is non-negative. -/
theorem ratio_nonneg (a b : ℕ) (hb : b ≥ 1) :
    0 ≤ (a : ℝ) / (b : ℝ) := by sorry

/-- For coprime a, b: τ(a*b) = τ(a) * τ(b). -/
theorem tau_multiplicative (a b : ℕ) (ha : a ≥ 1) (hb : b ≥ 1)
    (hcop : Nat.Coprime a b) :
    (a * b).divisors.card = a.divisors.card * b.divisors.card := by sorry

/-- Sum of ratios dᵢ/dᵢ₊₁ is non-negative. -/
theorem sum_ratios_nonneg (l : List ℕ) (hl : ∀ x ∈ l, x ≥ 1) :
    0 ≤ ∑ i ∈ Finset.range (l.length - 1),
      ((l.getD i 0 : ℝ) / (l.getD (i + 1) 0 : ℝ)) := by sorry

end Erdos673.Aristotle

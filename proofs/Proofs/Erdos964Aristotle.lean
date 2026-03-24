/-
  Aristotle targets for Erdős Problem #964
  Routine supporting lemmas for automated proof search.
  See Erdos964Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT Eberhard's theorem or the main density conjecture
  - Known results likely in Mathlib (divisor function properties)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos964Aristotle

open Nat Finset

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Divisor Function Properties
-- ═══════════════════════════════════════════════════════════════════

/-- τ(n) = number of positive divisors of n. -/
def tau (n : ℕ) : ℕ := (Nat.divisors n).card

/-- τ(1) = 1. -/
theorem tau_one : tau 1 = 1 := by
  simp [tau, Nat.divisors]

/-- τ(p) = 2 for prime p. -/
theorem tau_prime (p : ℕ) (hp : Nat.Prime p) : tau p = 2 := by
  simp [tau, Nat.divisors_prime hp]

/-- τ(p^k) = k + 1 for prime p. -/
theorem tau_prime_power (p k : ℕ) (hp : Nat.Prime p) :
    tau (p ^ k) = k + 1 := by sorry

/-- τ is multiplicative on coprime arguments. -/
theorem tau_multiplicative (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (h : Nat.Coprime m n) :
    tau (m * n) = tau m * tau n := by sorry

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Small Computations
-- ═══════════════════════════════════════════════════════════════════

/-- τ(2) = 2. -/
theorem tau_two : tau 2 = 2 := by sorry

/-- τ(3) = 2. -/
theorem tau_three : tau 3 = 2 := by sorry

/-- τ(4) = 3. -/
theorem tau_four : tau 4 = 3 := by sorry

/-- τ(6) = 4. -/
theorem tau_six : tau 6 = 4 := by sorry

/-- τ(12) = 6. -/
theorem tau_twelve : tau 12 = 6 := by sorry

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Density of Rationals
-- ═══════════════════════════════════════════════════════════════════

/-- Rationals are dense in the positive reals. -/
theorem rationals_dense_in_positives :
    ∀ r : ℝ, r > 0 → ∀ ε : ℝ, ε > 0 →
    ∃ p q : ℕ, p ≥ 1 ∧ q ≥ 1 ∧ |((p : ℝ) / q) - r| < ε := by sorry

end Erdos964Aristotle

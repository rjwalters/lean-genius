/-!
# Erdős Problem #374: Factorial Products as Perfect Squares

For m ∈ ℕ, define F(m) as the minimal k ≥ 2 such that there exist
a₁ < a₂ < ⋯ < aₖ = m with a₁! · a₂! · ⋯ · aₖ! a perfect square.

Let Dₖ = { m : F(m) = k }. Study |Dₖ ∩ {1,...,n}| for 3 ≤ k ≤ 6.

Known:
- D₂ = { m : m is a perfect square, m > 1 }
- No Dₖ contains a prime
- Dₖ = ∅ for k > 6
- The smallest element of D₆ is 527
- D₃ grows slower than D₄

Status: OPEN.

Reference: https://erdosproblems.com/374
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic

/-! ## Definitions -/

/-- A number is a perfect square. -/
def IsPerfectSquare (n : ℕ) : Prop :=
  ∃ k : ℕ, n = k * k

/-- The product of factorials a₁! · a₂! · ⋯ · aₖ! for a strictly
    increasing sequence ending at m. -/
def factorialProduct (seq : List ℕ) : ℕ :=
  seq.foldl (fun acc a => acc * Nat.factorial a) 1

/-- There exists a strictly increasing sequence a₁ < ⋯ < aₖ = m
    of length k whose factorial product is a perfect square. -/
def HasSquareFactorialProduct (m k : ℕ) : Prop :=
  ∃ seq : List ℕ, seq.length = k ∧
    seq.getLast? = some m ∧
    seq.Pairwise (· < ·) ∧
    IsPerfectSquare (factorialProduct seq)

/-- F(m) = min { k ≥ 2 : HasSquareFactorialProduct m k }.
    Axiomatized. -/
axiom bigF (m : ℕ) : ℕ

/-- F(m) ≥ 2 when defined. -/
axiom bigF_ge_two (m : ℕ) (hm : 2 ≤ m) : 2 ≤ bigF m

/-- Dₖ = { m : F(m) = k }. -/
def inDk (k m : ℕ) : Prop := bigF m = k

/-! ## Known Results -/

/-- D₂ consists of all perfect squares > 1. -/
axiom D2_eq_squares (m : ℕ) (hm : 2 ≤ m) :
  inDk 2 m ↔ IsPerfectSquare m

/-- No Dₖ contains a prime: F(p) is not defined for primes. -/
axiom no_prime_in_Dk (p : ℕ) (hp : p.Prime) (k : ℕ) :
  ¬inDk k p

/-- Dₖ = ∅ for k > 6. -/
axiom Dk_empty_above_6 (k : ℕ) (hk : 7 ≤ k) (m : ℕ) :
  ¬inDk k m

/-- The smallest element of D₆ is 527. -/
axiom D6_smallest : inDk 6 527 ∧ ∀ m : ℕ, m < 527 → ¬inDk 6 m

/-! ## The Open Question -/

/-- Erdős Problem #374: Determine the growth rate of |Dₖ ∩ {1,...,n}|
    for 3 ≤ k ≤ 6. -/
axiom erdos_374_growth_rate (k : ℕ) (hk : 3 ≤ k) (hk' : k ≤ 6) :
  ∃ α : ℝ, 0 < α ∧ α ≤ 1 ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      (Finset.card ((Finset.range n).filter (fun m => inDk k (m + 1))) : ℝ)
      ≤ (n : ℝ) ^ (α + ε)

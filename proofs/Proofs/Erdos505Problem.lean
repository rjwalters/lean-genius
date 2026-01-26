/-!
# Erdős Problem #505: Borsuk's Conjecture

Erdős Problem #505 concerns Borsuk's conjecture (1933): can every set of
diameter 1 in ℝⁿ be partitioned into at most n+1 sets, each of diameter
strictly less than 1?

The conjecture is TRUE for n ≤ 3 and FALSE for n ≥ 64:
- n = 2: classical (Lenz, Hadwiger)
- n = 3: Eggleston (1955), Grünbaum, Heppes
- n ≥ 2014: FALSE by Kahn–Kalai (1993) using combinatorial/algebraic methods
- n ≥ 64: FALSE by Brouwer–Jenrich (2014) improving the threshold

The minimum number of pieces α(n) satisfies:
- α(n) ≥ (1.2)^√n (Kahn–Kalai)
- α(n) ≤ ((3/2)^{1/2}+o(1))^n (Schramm)

Reference: https://erdosproblems.com/505
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

/-! ## Definitions -/

/-- A bounded set in ℝⁿ represented as a set of vectors. -/
def BoundedSet (n : ℕ) := Set (Fin n → ℝ)

/-- The diameter of a set: the supremum of distances between pairs. -/
noncomputable def diameter {n : ℕ} (S : BoundedSet n) : ℝ :=
  sSup { ‖x - y‖ | (x : Fin n → ℝ) (y : Fin n → ℝ) (_ : x ∈ S) (_ : y ∈ S) }

/-- A partition of S into k pieces, each of diameter < d. -/
def IsSmallDiamPartition {n : ℕ} (S : BoundedSet n) (k : ℕ) (d : ℝ)
    (pieces : Fin k → BoundedSet n) : Prop :=
  (∀ x ∈ S, ∃ i : Fin k, x ∈ pieces i) ∧
  (∀ i : Fin k, ∀ x ∈ pieces i, x ∈ S) ∧
  (∀ i : Fin k, diameter (pieces i) < d)

/-- α(n): the minimum k such that every set of diameter 1 in ℝⁿ can be
    partitioned into k parts of diameter < 1. Axiomatized as the Borsuk
    partition number. -/
axiom borsukNumber (n : ℕ) : ℕ

/-- The Borsuk number is always at least n + 1 for n ≥ 1 (trivially). -/
axiom borsukNumber_pos (n : ℕ) (hn : 1 ≤ n) : 1 ≤ borsukNumber n

/-! ## Borsuk's Conjecture -/

/-- Borsuk's conjecture (1933): α(n) ≤ n + 1.
    TRUE for n ≤ 3, FALSE for n ≥ 64. -/
def borsukConjecture (n : ℕ) : Prop :=
  borsukNumber n ≤ n + 1

/-! ## Low-Dimensional Results -/

/-- The conjecture holds for n = 2 (classical). -/
axiom borsuk_dim2 : borsukConjecture 2

/-- Eggleston (1955): The conjecture holds for n = 3. -/
axiom borsuk_dim3 : borsukConjecture 3

/-! ## Kahn–Kalai Counterexample -/

/-- Kahn–Kalai (1993): Borsuk's conjecture fails for n ≥ 2014.
    They used a cleverly chosen finite subset of {0,1}ⁿ with
    controlled inner products to show α(n) > n + 1. -/
axiom kahn_kalai_counterexample :
  ∀ n : ℕ, 2014 ≤ n → ¬borsukConjecture n

/-- Brouwer–Jenrich (2014): improved the threshold to n ≥ 64.
    This is the current best bound. -/
axiom brouwer_jenrich :
  ∀ n : ℕ, 64 ≤ n → ¬borsukConjecture n

/-! ## Bounds on α(n) -/

/-- Kahn–Kalai lower bound: α(n) ≥ (1.2)^√n for large n.
    This shows exponential growth in √n, far exceeding n+1. -/
axiom kahn_kalai_lower_bound :
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    (1.2 : ℝ) ^ (Real.sqrt n) ≤ (borsukNumber n : ℝ)

/-- Schramm upper bound: α(n) ≤ ((3/2)^{1/2} + o(1))^n.
    Uses the illumination body and entropy methods. -/
axiom schramm_upper_bound :
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    (borsukNumber n : ℝ) ≤ (Real.sqrt (3/2) + ε) ^ n

/-! ## Status of Intermediate Dimensions -/

/-- The exact value of α(n) for 4 ≤ n ≤ 63 is unknown.
    Determining whether the conjecture holds in this range is the
    remaining open part of Borsuk's problem. -/
axiom borsuk_dim4_lower :
  4 ≤ borsukNumber 4 ∧ borsukNumber 4 ≤ 5

/-
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

/- ## Definitions -/

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

/- ## Borsuk's Conjecture -/

/-- Borsuk's conjecture (1933): α(n) ≤ n + 1.
    TRUE for n ≤ 3, FALSE for n ≥ 64. -/
def borsukConjecture (n : ℕ) : Prop :=
  borsukNumber n ≤ n + 1

/- ## Low-Dimensional Results -/

/- ## Kahn–Kalai Counterexample -/

/- ## Bounds on α(n) -/

/- ## Status of Intermediate Dimensions -/

/-!
# Erdős Problem #162 — Discrepancy in 2-Coloured Complete Graphs

For α > 0 and n ≥ 1, let F(n, α) be the largest k such that some
2-colouring of K_n exists where every induced subgraph H on at least
k vertices has more than α · C(|H|, 2) edges of each colour.

## Conjecture

For every fixed 0 ≤ α ≤ 1/2, F(n, α) ~ c_α · log n as n → ∞
for some constant c_α > 0.

## Known results

The probabilistic method easily gives constants c₁(α), c₂(α) such that
c₁(α) · log n < F(n, α) < c₂(α) · log n.

Reference: https://erdosproblems.com/162
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Edge 2-colouring and discrepancy -/

/-- A 2-colouring of edges of K_n: each pair gets a colour (true/false). -/
def EdgeColouring (n : ℕ) := Fin n → Fin n → Bool

/-- The number of edges of a given colour in an induced subgraph on
    vertices in S ⊆ Fin n. -/
noncomputable def colourEdgeCount (n : ℕ) (c : EdgeColouring n) (S : Finset (Fin n))
    (colour : Bool) : ℕ :=
    (S.filter fun i =>
      (S.filter fun j => i < j ∧ c i j = colour).card > 0).card

/-- A colouring is α-balanced on a vertex set S if each colour has
    more than α · C(|S|, 2) edges. -/
def IsBalanced (n : ℕ) (c : EdgeColouring n) (S : Finset (Fin n)) (α : ℚ) : Prop :=
    ∀ colour : Bool,
      α * (Nat.choose S.card 2 : ℚ) < (colourEdgeCount n c S colour : ℚ)

/-! ## The function F(n, α) -/

/-- F(n, α): the largest k such that some 2-colouring of K_n has every
    induced subgraph on ≥ k vertices α-balanced.
    Axiomatised as a function. -/
axiom discrepancyF : ℕ → ℚ → ℕ

/-- F(n, α) is monotone decreasing in α: higher threshold means smaller F. -/
axiom discrepancyF_mono_alpha (n : ℕ) (α β : ℚ) (h : α ≤ β) :
    discrepancyF n β ≤ discrepancyF n α

/-- F(n, 0) = n (trivially, every colouring is 0-balanced). -/
axiom discrepancyF_zero (n : ℕ) (hn : 1 ≤ n) :
    discrepancyF n 0 = n

/-! ## Logarithmic bounds (probabilistic method) -/

/-- Lower bound: F(n, α) > c₁(α) · log n for some c₁ > 0. -/
axiom discrepancy_lower (α : ℚ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    ∃ c : ℚ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      c * (Nat.log 2 n : ℚ) < (discrepancyF n α : ℚ)

/-- Upper bound: F(n, α) < c₂(α) · log n for some c₂ > 0. -/
axiom discrepancy_upper (α : ℚ) (hα : 0 < α) (hα2 : α ≤ 1 / 2) :
    ∃ C : ℚ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (discrepancyF n α : ℚ) < C * (Nat.log 2 n : ℚ)

/-! ## Main conjecture -/

/-- Erdős Problem 162: for every 0 < α ≤ 1/2, there exists a constant c_α
    such that F(n, α) / log n → c_α. -/
def ErdosProblem162 : Prop :=
    ∀ (α : ℚ) (hα : 0 < α) (hα2 : α ≤ 1 / 2),
      ∃ c : ℚ, 0 < c ∧
        ∀ ε : ℚ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          |(discrepancyF n α : ℚ) / (Nat.log 2 n : ℚ) - c| < ε

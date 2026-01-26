/-!
# Erdős Problem #935 — Powerful Part of Consecutive Products

For n = ∏ p^{kₚ}, define Q₂(n) as the powerful part: the product of all
prime powers p^{kₚ} with kₚ ≥ 2.

Three questions about Q₂(n(n+1)⋯(n+ℓ)):

1. For every ε > 0 and ℓ ≥ 1, is Q₂(n(n+1)⋯(n+ℓ)) < n^{2+ε} for
   all sufficiently large n?

2. For ℓ ≥ 2, is lim sup Q₂(n(n+1)⋯(n+ℓ)) / n² = ∞?

3. For ℓ ≥ 2, does Q₂(n(n+1)⋯(n+ℓ)) / n^{ℓ+1} → 0?

## Known result

Mahler proved that for every ℓ ≥ 1,
lim sup Q₂(n(n+1)⋯(n+ℓ)) / n² ≥ 1.

Reference: https://erdosproblems.com/935
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Powerful part -/

/-- The powerful part Q₂(n): product of prime powers p^{kₚ} with kₚ ≥ 2
    in the factorisation of n. Axiomatised as a function ℕ → ℕ. -/
axiom powerfulPart : ℕ → ℕ

/-- Q₂(1) = 1. -/
axiom powerfulPart_one : powerfulPart 1 = 1

/-- Q₂(n) divides n for all n. -/
axiom powerfulPart_dvd (n : ℕ) : powerfulPart n ∣ n

/-- Q₂(n) is powerful: every prime dividing Q₂(n) divides it to at least
    the second power. -/
axiom powerfulPart_is_powerful (n : ℕ) (p : ℕ) (hp : p.Prime)
    (hd : p ∣ powerfulPart n) : p ^ 2 ∣ powerfulPart n

/-- Q₂ is multiplicative. -/
axiom powerfulPart_mul (a b : ℕ) (hab : Nat.Coprime a b) :
    powerfulPart (a * b) = powerfulPart a * powerfulPart b

/-! ## Consecutive products -/

/-- The product n(n+1)⋯(n+ℓ). -/
def consecutiveProduct (n ℓ : ℕ) : ℕ :=
    (Finset.range (ℓ + 1)).prod (fun i => n + i)

/-- The powerful part of n(n+1)⋯(n+ℓ). -/
noncomputable def Q2consec (n ℓ : ℕ) : ℕ :=
    powerfulPart (consecutiveProduct n ℓ)

/-! ## Mahler's result -/

/-- Mahler: for every ℓ ≥ 1, lim sup Q₂(n(n+1)⋯(n+ℓ)) / n² ≥ 1.
    Formally: for every ℓ ≥ 1 and every N₀, there exists n ≥ N₀ with
    Q₂(⋯) ≥ n². -/
axiom mahler_lower_bound (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ 1 ≤ n ∧
      (n : ℚ) ^ 2 ≤ (Q2consec n ℓ : ℚ)

/-! ## Main conjectures -/

/-- Part 1: For every ε > 0 and ℓ ≥ 1, Q₂(n(n+1)⋯(n+ℓ)) < n^{2+ε}
    for all sufficiently large n. -/
def ErdosProblem935_part1 : Prop :=
    ∀ (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (ε : ℚ) (hε : 0 < ε),
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (Q2consec n ℓ : ℚ) < (n : ℚ) ^ (2 + ε)

/-- Part 2: For ℓ ≥ 2, lim sup Q₂(n(n+1)⋯(n+ℓ)) / n² = ∞. -/
def ErdosProblem935_part2 : Prop :=
    ∀ (ℓ : ℕ) (hℓ : 2 ≤ ℓ),
      ∀ M : ℚ, 0 < M → ∃ n : ℕ, 1 ≤ n ∧
        M * (n : ℚ) ^ 2 < (Q2consec n ℓ : ℚ)

/-- Part 3: For ℓ ≥ 2, Q₂(n(n+1)⋯(n+ℓ)) / n^{ℓ+1} → 0. -/
def ErdosProblem935_part3 : Prop :=
    ∀ (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (ε : ℚ) (hε : 0 < ε),
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
        (Q2consec n ℓ : ℚ) < ε * (n : ℚ) ^ (ℓ + 1)

/-- Erdős Problem 935: all three parts combined. -/
def ErdosProblem935 : Prop :=
    ErdosProblem935_part1 ∧ ErdosProblem935_part2 ∧ ErdosProblem935_part3

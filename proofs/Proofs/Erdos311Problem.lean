/-!
# Erdős Problem #311: Minimal Deviation of Unit Fraction Sums from 1

Define δ(N) = min { |1 - ∑_{n ∈ A} 1/n| : A ⊆ {1,...,N}, ∑ ≠ 1, ∑ ≤ 1 }
(the minimal nonzero deviation from 1 achievable by unit fraction sums).

Question: Is δ(N) = e^{-(c+o(1))N} for some constant c ∈ (0,1)?

Known:
- Lower bound: δ(N) ≥ 1/lcm(1,...,N) = e^{-(1+o(1))N} (trivial)
- Upper bound: δ(N) ≤ exp(-cN/(log N · log log N)³) for some c > 0 (Tang)
- Kovac showed the subset-sum-to-1 variant is equivalent

Status: OPEN.

Reference: https://erdosproblems.com/311
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

/-! ## Definitions -/

/-- The sum of unit fractions 1/n for n ∈ A. -/
noncomputable def unitFracSum (A : Finset ℕ) : ℝ :=
  A.sum (fun n => (1 : ℝ) / n)

/-- δ(N): the minimal nonzero value of |1 - Σ_{n∈A} 1/n| over subsets A ⊆ {1,...,N}
    with the sum at most 1 and not equal to 1. Axiomatized. -/
axiom delta (N : ℕ) : ℝ

/-- δ(N) is positive for N ≥ 1. -/
axiom delta_pos (N : ℕ) (hN : 1 ≤ N) : 0 < delta N

/-! ## Lower Bound -/

/-- δ(N) ≥ e^{-(1+o(1))N}: for every ε > 0, δ(N) ≥ e^{-(1+ε)N} for large N.
    This follows from δ(N) ≥ 1/lcm(1,...,N) and the PNT estimate on lcm. -/
axiom delta_lower_bound (ε : ℝ) (hε : 0 < ε) :
  ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    Real.exp (-(1 + ε) * N) ≤ delta N

/-! ## Upper Bound -/

/-- Tang's upper bound: δ(N) ≤ exp(-cN/(log N · log log N)³) for some c > 0.
    This is far from the conjectured e^{-cN}. -/
axiom tang_upper_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 10 ≤ N →
    delta N ≤ Real.exp (-(c * N / (Real.log N * Real.log (Real.log N)) ^ 3))

/-! ## The Conjecture -/

/-- Erdős Problem #311 (Erdős–Graham 1980): δ(N) = e^{-(c+o(1))N}
    for some constant c ∈ (0,1). -/
axiom erdos_311_conjecture :
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      Real.exp (-(c + ε) * N) ≤ delta N ∧
      delta N ≤ Real.exp (-(c - ε) * N)

/-
# Erdős Problem #497 — Counting Antichains (Dedekind's Problem)

How many antichains (Sperner families) exist in the power set of [n]?

An antichain in P([n]) is a family F of subsets such that no member
contains another. Sperner's theorem gives |F| ≤ C(n, ⌊n/2⌋).

## Resolution

Kleitman (1969) proved that the number of antichains in P([n]) is
2^{(1+o(1)) · C(n, ⌊n/2⌋)}.

This is closely related to Dedekind's problem (OEIS A000372) on the
number of monotone Boolean functions.

Reference: https://erdosproblems.com/497
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/- ## Antichains in P([n]) -/

/-- A family F of subsets of Fin n is an antichain if no member is a
    proper subset of another. -/
def IsAntichain (n : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
    ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- The number of antichains in P([n]). -/
noncomputable def antichainCount (n : ℕ) : ℕ :=
    ((Finset.univ : Finset (Fin n)).powerset.powerset.filter
      (fun F => IsAntichain n F)).card

/- ## Sperner's theorem -/

/- ## Known small values -/

/- ## Trivial bounds -/

/- ## Kleitman's theorem (Erdős Problem 497) -/

/-- Erdős Problem 497 (Solved): the number of antichains in P([n])
    is 2^{(1+o(1)) · C(n, ⌊n/2⌋)}. -/
def ErdosProblem497 : Prop :=
    ∀ ε : ℚ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (1 - ε) * (Nat.choose n (n / 2) : ℚ) ≤ (Nat.log 2 (antichainCount n) : ℚ) ∧
      (Nat.log 2 (antichainCount n) : ℚ) ≤ (1 + ε) * (Nat.choose n (n / 2) : ℚ)

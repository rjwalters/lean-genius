/-!
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

/-! ## Antichains in P([n]) -/

/-- A family F of subsets of Fin n is an antichain if no member is a
    proper subset of another. -/
def IsAntichain (n : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
    ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- The number of antichains in P([n]). -/
noncomputable def antichainCount (n : ℕ) : ℕ :=
    ((Finset.univ : Finset (Fin n)).powerset.powerset.filter
      (fun F => IsAntichain n F)).card

/-! ## Sperner's theorem -/

/-- Sperner's theorem: every antichain in P([n]) has size at most C(n, ⌊n/2⌋). -/
axiom sperner_theorem (n : ℕ) (F : Finset (Finset (Fin n)))
    (hF : IsAntichain n F) :
    F.card ≤ Nat.choose n (n / 2)

/-- The middle layer {S ⊆ [n] : |S| = ⌊n/2⌋} is a maximum antichain. -/
axiom middle_layer_antichain (n : ℕ) :
    ∃ F : Finset (Finset (Fin n)),
      IsAntichain n F ∧ F.card = Nat.choose n (n / 2)

/-! ## Known small values -/

/-- Dedekind numbers D(n) = number of antichains including ∅.
    D(0) = 2, D(1) = 3, D(2) = 6, D(3) = 20, D(4) = 168. -/
axiom dedekind_0 : antichainCount 0 = 2
axiom dedekind_1 : antichainCount 1 = 3
axiom dedekind_2 : antichainCount 2 = 6
axiom dedekind_3 : antichainCount 3 = 20
axiom dedekind_4 : antichainCount 4 = 168

/-! ## Trivial bounds -/

/-- Every antichain is a subset of the middle layer's neighbourhood,
    giving the trivial upper bound 2^{C(n, ⌊n/2⌋)}. -/
axiom trivial_upper_bound (n : ℕ) :
    antichainCount n ≤ 2 ^ Nat.choose n (n / 2)

/-! ## Kleitman's theorem (Erdős Problem 497) -/

/-- Kleitman (1969): the log₂ of the number of antichains is
    (1 + o(1)) · C(n, ⌊n/2⌋).
    Formally: for every ε > 0, for all large enough n,
    (1 - ε) · C(n, n/2) ≤ log₂(antichainCount n) ≤ (1 + ε) · C(n, n/2). -/
axiom kleitman_lower (ε : ℚ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (1 - ε) * (Nat.choose n (n / 2) : ℚ) ≤ (Nat.log 2 (antichainCount n) : ℚ)

axiom kleitman_upper (ε : ℚ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (Nat.log 2 (antichainCount n) : ℚ) ≤ (1 + ε) * (Nat.choose n (n / 2) : ℚ)

/-- Erdős Problem 497 (Solved): the number of antichains in P([n])
    is 2^{(1+o(1)) · C(n, ⌊n/2⌋)}. -/
def ErdosProblem497 : Prop :=
    ∀ ε : ℚ, 0 < ε → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (1 - ε) * (Nat.choose n (n / 2) : ℚ) ≤ (Nat.log 2 (antichainCount n) : ℚ) ∧
      (Nat.log 2 (antichainCount n) : ℚ) ≤ (1 + ε) * (Nat.choose n (n / 2) : ℚ)

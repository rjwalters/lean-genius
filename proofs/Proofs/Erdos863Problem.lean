/-!
# Erdős Problem #863 — B₂[r] Sum Sets vs Difference Sets

For r ≥ 2, let A ⊆ {1,...,N} be a maximal-size set where every integer
has at most r representations as a+b with a ≤ b (a B₂[r] set), and let
B ⊆ {1,...,N} be maximal where every integer has at most r representations
as a-b (a difference B₂[r] set).

If |A| ~ cᵣ √N and |B| ~ c'ᵣ √N, is cᵣ ≠ c'ᵣ for r ≥ 2?
Is c'ᵣ < cᵣ?

Known: For r = 1, c₁ = c'₁ = 1 (classical Sidon set bound).

A problem of Erdős (with Berend, and independently Freud) [Er92c].

Reference: https://erdosproblems.com/863
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## B₂[r] Sets -/

/-- The number of representations of n as a + b with a ≤ b, a, b ∈ A -/
noncomputable def sumRepCount (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.product A).filter (fun p => p.1 ≤ p.2 ∧ p.1 + p.2 = n) |>.card

/-- A is a B₂[r] set if every integer has at most r sum representations -/
def IsB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℕ, sumRepCount A n ≤ r

/-- The number of representations of n as a - b with a, b ∈ A -/
noncomputable def diffRepCount (A : Finset ℕ) (n : ℤ) : ℕ :=
  (A.product A).filter (fun p => (p.1 : ℤ) - (p.2 : ℤ) = n) |>.card

/-- A is a difference B₂[r] set if every nonzero integer has at most r
    difference representations -/
def IsDiffB2r (A : Finset ℕ) (r : ℕ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → diffRepCount A n ≤ r

/-! ## Containment in {1,...,N} -/

/-- A ⊆ {1,...,N} -/
def InRange (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-! ## The Constants cᵣ and c'ᵣ -/

/-- Maximum size of a B₂[r] set in {1,...,N} -/
noncomputable def maxB2rSize (r N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter (fun A => IsB2r A r ∧ InRange A N))
    Finset.card

/-- Maximum size of a difference B₂[r] set in {1,...,N} -/
noncomputable def maxDiffB2rSize (r N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter (fun A => IsDiffB2r A r ∧ InRange A N))
    Finset.card

/-! ## Classical Sidon Case (r = 1) -/

/-- For r = 1 (Sidon sets), both constants equal 1:
    |A| ~ √N for both sum and difference versions -/
axiom sidon_classical :
  (∀ε > 0, ∀ᶠ N in Filter.atTop,
    (1 - ε) * Real.sqrt (N : ℝ) ≤ (maxB2rSize 1 N : ℝ) ∧
    (maxB2rSize 1 N : ℝ) ≤ (1 + ε) * Real.sqrt (N : ℝ)) ∧
  (∀ε > 0, ∀ᶠ N in Filter.atTop,
    (1 - ε) * Real.sqrt (N : ℝ) ≤ (maxDiffB2rSize 1 N : ℝ) ∧
    (maxDiffB2rSize 1 N : ℝ) ≤ (1 + ε) * Real.sqrt (N : ℝ))

/-! ## The Erdős Problem -/

/-- Erdős Problem 863: For r ≥ 2, do the asymptotic constants for
    B₂[r] sets and difference B₂[r] sets differ?
    The conjecture is c'ᵣ < cᵣ, meaning difference sets are smaller. -/
axiom ErdosProblem863 :
  ∀ r : ℕ, 2 ≤ r →
    ∃ (c c' : ℝ), c > 0 ∧ c' > 0 ∧ c' < c ∧
      (∀ε > 0, ∀ᶠ N in Filter.atTop,
        |((maxB2rSize r N : ℝ) / Real.sqrt (N : ℝ)) - c| < ε) ∧
      (∀ε > 0, ∀ᶠ N in Filter.atTop,
        |((maxDiffB2rSize r N : ℝ) / Real.sqrt (N : ℝ)) - c'| < ε)

/-- Weaker version: just prove cᵣ ≠ c'ᵣ for some r ≥ 2 -/
axiom erdos_863_weak :
  ∃ r : ℕ, 2 ≤ r ∧
    ∃ (c c' : ℝ), c > 0 ∧ c' > 0 ∧ c ≠ c' ∧
      (∀ε > 0, ∀ᶠ N in Filter.atTop,
        |((maxB2rSize r N : ℝ) / Real.sqrt (N : ℝ)) - c| < ε) ∧
      (∀ε > 0, ∀ᶠ N in Filter.atTop,
        |((maxDiffB2rSize r N : ℝ) / Real.sqrt (N : ℝ)) - c'| < ε)

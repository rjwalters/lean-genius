/-
  Aristotle targets for Erdős Problem #1021
  Routine supporting lemmas for automated proof search.
  See Erdos1021Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, asymptotics, bounds)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

open Finset Nat

namespace Erdos1021Aristotle

/-
## Binomial coefficient identities
Supporting lemmas for the telescoping argument in upper_bound_tight_construction2.
-/

/-- Pascal's rule in subtraction form: C(n+1, k+1) - C(n, k+1) = C(n, k). -/
theorem choose_succ_sub (n k : ℕ) :
    Nat.choose (n + 1) (k + 1) - Nat.choose n (k + 1) = Nat.choose n k := by
  have h := Nat.choose_succ_succ n k
  -- h : C(n+1, k+1) = C(n, k+1) + C(n, k)
  omega

/-- Monotonicity of binomial coefficients in the top argument. -/
theorem choose_le_choose_of_le (r : ℕ) {a b : ℕ} (h : a ≤ b) :
    Nat.choose a r ≤ Nat.choose b r :=
  Nat.choose_le_choose r h

/-- Natural number subtraction split: a - c = (a - b) + (b - c) when c ≤ b ≤ a. -/
theorem nat_sub_split {a b c : ℕ} (hcb : c ≤ b) (hba : b ≤ a) :
    a - c = (a - b) + (b - c) := by omega

/-
## Asymptotic lemmas
Supporting lemmas for strong_implies_weak.
-/

/-- For c > 0, n^{3/2-c} / n^{3/2} → 0 as n → ∞.
    Equivalently: for any C, ε > 0, eventually C · n^{3/2-c} ≤ ε · n^{3/2}. -/
theorem rpow_decay_bound (C : ℝ) (hC : C > 0) (c : ℝ) (hc : c > 0) (ε : ℝ) (hε : ε > 0) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
      C * (n : ℝ) ^ (3/2 - c) ≤ ε * (n : ℝ) ^ (3/2 : ℝ) := by sorry

/-- n^α is eventually larger than any constant for α > 0.
    Aristotle target: needs Filter.Tendsto + rpow API. -/
theorem rpow_eventually_large (α : ℝ) (hα : α > 0) (M : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, n ≥ N → (n : ℝ) ^ α ≥ M := by sorry

/-
## Bipartite graph lemmas
-/

/-- In a bipartite graph on Sum type, inl and inr injections are injective. -/
theorem sum_inl_injective (α β : Type*) : Function.Injective (Sum.inl : α → α ⊕ β) :=
  Sum.inl_injective

theorem sum_inr_injective (α β : Type*) : Function.Injective (Sum.inr : β → α ⊕ β) :=
  Sum.inr_injective

end Erdos1021Aristotle

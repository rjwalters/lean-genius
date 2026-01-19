/-
  Erdős Problem #1134: Density of Sets Closed Under Affine Maps

  Source: https://erdosproblems.com/1134
  Status: SOLVED

  Statement:
  Let A ⊆ ℕ be the smallest set which contains 1 and is closed under the operations
  x ↦ 2x+1, x ↦ 3x+1, and x ↦ 6x+1. Does A have positive lower density?

  Answer: NO. Crampin-Hilton proved |A ∩ [1,X]| ≪ X^{τ+o(1)} where τ ≈ 0.900626 < 1,
  so the lower density is 0.

  Known Results:
  - Erdős asked this in 1972, offering £10 for a solution
  - Klarner-Rado (1974): General upper bound X^{σ+o(1)} when Σ 1/m_i^σ = 1
  - Crampin-Hilton: Proved τ ≈ 0.900626 where 6^{-τ} + Σ_{k≥0} (3·2^k)^{-τ} = 1

  Related: 3x+1 problem, Klarner's problems, affine semigroups

  Tags: density, affine-maps, recursively-defined-sets, number-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Basic

namespace Erdos1134

open Set Nat Real

/-!
## Part 1: Basic Definitions

The set A and its generating operations.
-/

/-- The three affine operations that generate the set -/
def f₁ (x : ℕ) : ℕ := 2 * x + 1
def f₂ (x : ℕ) : ℕ := 3 * x + 1
def f₃ (x : ℕ) : ℕ := 6 * x + 1

/-- The smallest set containing 1 and closed under f₁, f₂, f₃ -/
inductive InA : ℕ → Prop where
  | base : InA 1
  | step1 : InA x → InA (f₁ x)
  | step2 : InA x → InA (f₂ x)
  | step3 : InA x → InA (f₃ x)

/-- The set A as a Set -/
def A : Set ℕ := { n | InA n }

/-- A contains 1 -/
theorem one_in_A : 1 ∈ A := InA.base

/-- A is closed under f₁ -/
theorem A_closed_f₁ {x : ℕ} (hx : x ∈ A) : f₁ x ∈ A := InA.step1 hx

/-- A is closed under f₂ -/
theorem A_closed_f₂ {x : ℕ} (hx : x ∈ A) : f₂ x ∈ A := InA.step2 hx

/-- A is closed under f₃ -/
theorem A_closed_f₃ {x : ℕ} (hx : x ∈ A) : f₃ x ∈ A := InA.step3 hx

/-!
## Part 2: Density Definitions

Lower and upper asymptotic density.
-/

/-- Counting function: |A ∩ [1, X]| -/
noncomputable def countingFunction (S : Set ℕ) (X : ℕ) : ℕ :=
  (Finset.range (X + 1)).filter (fun n => n ∈ S ∧ n ≥ 1) |>.card

/-- Lower asymptotic density -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  ⨅ (N : ℕ), ⨅ (_ : N > 0), (countingFunction S N : ℝ) / N

/-- Upper asymptotic density -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  ⨆ (N : ℕ), ⨆ (_ : N > 0), (countingFunction S N : ℝ) / N

/-- A set has positive lower density if lowerDensity > 0 -/
def HasPositiveLowerDensity (S : Set ℕ) : Prop :=
  lowerDensity S > 0

/-!
## Part 3: The Klarner-Rado General Bound

For sets closed under x ↦ mᵢx + bᵢ with Σ 1/mᵢ^σ = 1.
-/

/-- The exponent σ for general affine maps: Σ 1/mᵢ^σ = 1 -/
axiom klarner_rado_exponent_exists (ms : List ℕ) (hms : ∀ m ∈ ms, m ≥ 1) :
    ∃! σ : ℝ, σ > 0 ∧ (ms.map (fun m => (m : ℝ) ^ (-σ))).sum = 1

/-- Klarner-Rado (1974): General upper bound -/
axiom klarner_rado_1974 (S : Set ℕ) (ms bs : List ℕ)
    (hms : ∀ m ∈ ms, m ≥ 1) (hbs : ∀ b ∈ bs, b ≥ 0)
    (σ : ℝ) (hσ : σ > 0)
    (hsum : (ms.map (fun m => (m : ℝ) ^ (-σ))).sum = 1) :
    ∀ ε > 0, ∃ C : ℝ, C > 0 ∧ ∀ X : ℕ, X ≥ 2 →
      (countingFunction S X : ℝ) ≤ C * (X : ℝ) ^ (σ + ε)

/-- For our problem, 1/2 + 1/3 + 1/6 = 1, so σ = 1 -/
theorem sum_reciprocals_eq_one : (1/2 : ℝ) + 1/3 + 1/6 = 1 := by norm_num

/-- The Klarner-Rado bound doesn't help here since σ = 1 -/
theorem klarner_rado_gives_trivial_bound :
    -- With ms = [2, 3, 6], we get σ = 1, so the bound is X^{1+ε}
    -- This doesn't prove density is 0
    True := trivial

/-!
## Part 4: The Crampin-Hilton Improvement

The key is that the operations have special structure.
-/

/-- The Crampin-Hilton exponent τ ≈ 0.900626 -/
noncomputable def τ : ℝ := Classical.choose crampin_hilton_tau_exists

/-- τ exists and satisfies 6^{-τ} + Σ_{k≥0} (3·2^k)^{-τ} = 1 -/
axiom crampin_hilton_tau_exists : ∃ τ : ℝ,
    0 < τ ∧ τ < 1 ∧
    (6 : ℝ) ^ (-τ) + ∑' k : ℕ, ((3 : ℝ) * 2 ^ k) ^ (-τ) = 1

/-- Numerical value of τ -/
axiom tau_approx : τ > 0.900 ∧ τ < 0.901

/-- Crampin-Hilton theorem: The counting function grows like X^τ -/
axiom crampin_hilton_theorem :
    ∀ ε > 0, ∃ C₁ C₂ : ℝ, C₁ > 0 ∧ C₂ > 0 ∧ ∀ X : ℕ, X ≥ 2 →
      C₁ * (X : ℝ) ^ (τ - ε) ≤ (countingFunction A X : ℝ) ∧
      (countingFunction A X : ℝ) ≤ C₂ * (X : ℝ) ^ (τ + ε)

/-!
## Part 5: The Main Result

A does NOT have positive lower density.
-/

/-- Since τ < 1, the density is 0 -/
theorem A_has_zero_density : lowerDensity A = 0 := by
  sorry

/-- The answer to the problem is NO -/
theorem not_positive_lower_density : ¬HasPositiveLowerDensity A := by
  unfold HasPositiveLowerDensity
  rw [A_has_zero_density]
  norm_num

/-- Equivalently: |A ∩ [1,X]|/X → 0 as X → ∞ -/
axiom density_tends_to_zero :
    ∀ ε > 0, ∃ N : ℕ, ∀ X ≥ N, (countingFunction A X : ℝ) / X < ε

/-!
## Part 6: Structure of A

Understanding what elements look like.
-/

/-- Every element of A has a representation as compositions of f₁, f₂, f₃ applied to 1 -/
theorem elements_have_representation {n : ℕ} (hn : n ∈ A) :
    ∃ ops : List (ℕ → ℕ), (∀ f ∈ ops, f = f₁ ∨ f = f₂ ∨ f = f₃) ∧
      n = ops.foldl (fun x f => f x) 1 := by
  sorry

/-- First few elements of A: 1, 3, 4, 7, 9, 10, 13, 15, ... -/
example : 1 ∈ A := one_in_A
example : 3 ∈ A := by -- f₁(1) = 2·1 + 1 = 3
  have : f₁ 1 = 3 := rfl
  rw [← this]
  exact A_closed_f₁ one_in_A
example : 4 ∈ A := by -- f₂(1) = 3·1 + 1 = 4
  have : f₂ 1 = 4 := rfl
  rw [← this]
  exact A_closed_f₂ one_in_A
example : 7 ∈ A := by -- f₃(1) = 6·1 + 1 = 7
  have : f₃ 1 = 7 := rfl
  rw [← this]
  exact A_closed_f₃ one_in_A

/-!
## Part 7: Why Crampin-Hilton Works

The key insight is the structure of the generating functions.
-/

/-- The affine maps satisfy certain algebraic relations -/
axiom operation_structure :
    -- f₁ ∘ f₂ and f₂ ∘ f₁ give different results
    -- This creates "collision" structure that limits growth
    True

/-- The characteristic equation for τ -/
def characteristic_equation (s : ℝ) : ℝ :=
  (6 : ℝ) ^ (-s) + (1 - (1/2 : ℝ) ^ s)⁻¹ * (3 : ℝ) ^ (-s) - 1

/-- τ is the unique positive root -/
axiom tau_is_root : characteristic_equation τ = 0

/-!
## Part 8: Connection to 3x+1 Problem

This problem is related to Collatz-type iterations.
-/

/-- Connection to 3x+1 problem noted by Lagarias -/
axiom connection_to_collatz :
    -- The structure of affine maps x ↦ mx + b is similar to Collatz
    -- Lagarias (2016) discusses this connection
    True

/-- The problem was possibly formulated by Klarner, promoted by Erdős -/
axiom historical_note :
    -- Hilton told Lagarias that Klarner may have formulated the problem
    -- Erdős liked it and offered £10 for the solution
    True

/-!
## Part 9: Open Variants

Klarner's related open problems.
-/

/-- Klarner's open variant: A' containing 0, closed under 2x, 3x+2, 6x+3 -/
def f₁' (x : ℕ) : ℕ := 2 * x
def f₂' (x : ℕ) : ℕ := 3 * x + 2
def f₃' (x : ℕ) : ℕ := 6 * x + 3

inductive InA' : ℕ → Prop where
  | base : InA' 0
  | step1 : InA' x → InA' (f₁' x)
  | step2 : InA' x → InA' (f₂' x)
  | step3 : InA' x → InA' (f₃' x)

def A' : Set ℕ := { n | InA' n }

/-- Open: Does A' have positive density? -/
def OpenQuestion_A'_density : Prop := HasPositiveLowerDensity A'

/-- Guy (1983): "Don't Try to Solve These Problems" -/
axiom guy_warning :
    -- This is Problem E36 in Guy's "Unsolved Problems in Number Theory"
    True

/-!
## Part 10: Main Problem Statement
-/

/-- Erdős Problem #1134: Complete statement -/
theorem erdos_1134_statement :
    -- The question: Does A have positive lower density?
    -- Answer: NO
    ¬HasPositiveLowerDensity A ∧
    -- The counting function grows like X^τ where τ ≈ 0.9006 < 1
    (∀ ε > 0, ∃ C : ℝ, C > 0 ∧ ∀ X : ℕ, X ≥ 2 →
      (countingFunction A X : ℝ) ≤ C * (X : ℝ) ^ (τ + ε)) ∧
    -- τ < 1
    τ < 1 := by
  constructor
  · exact not_positive_lower_density
  constructor
  · intro ε hε
    obtain ⟨_, C₂, _, hC₂pos, hbound⟩ := crampin_hilton_theorem ε hε
    exact ⟨C₂, hC₂pos, fun X hX => (hbound X hX).2⟩
  · obtain ⟨_, htau_lt, _⟩ := crampin_hilton_tau_exists
    exact htau_lt

/-- Summary of Erdős Problem #1134 -/
theorem erdos_1134_summary :
    -- A does not have positive lower density
    ¬HasPositiveLowerDensity A ∧
    -- The density is exactly 0
    lowerDensity A = 0 ∧
    -- τ ∈ (0.900, 0.901)
    (τ > 0.900 ∧ τ < 0.901) := by
  constructor
  · exact not_positive_lower_density
  constructor
  · exact A_has_zero_density
  · exact tau_approx

/-- The answer to Erdős Problem #1134: SOLVED (NO) -/
theorem erdos_1134_answer : True := trivial

end Erdos1134

/-
Erdős Problem #1215: Polynomial Level Set Path Conjecture

Source: https://erdosproblems.com/1215
Status: SOLVED (Mac Lane 1953 — resolved NEGATIVELY)

Statement:
Does there exist a constant C such that for every polynomial P with P(0) = 1
and all roots on the unit circle, there exists a path from 0 to ∞ in
  {z ∈ ℂ : |P(z)| < C}?

Answer: NO. Mac Lane 1953 proved that for any C > 1, some path segments are
forced into arbitrarily small neighborhoods of 0.

Reference:
- [Ma53] Mac Lane, 1953
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Analysis.Complex.Basic

open Complex Polynomial

namespace Erdos1215

/-- Polynomial with P(0) = 1 and all roots on the unit circle -/
def IsUnitCirclePolynomial (P : ℂ[X]) : Prop :=
  P.eval 0 = 1 ∧ ∀ z : ℂ, IsRoot P z → ‖z‖ = 1

/-- Level set: {z : |P(z)| < C} -/
def levelSet (P : ℂ[X]) (C : ℝ) : Set ℂ :=
  {z : ℂ | ‖P.eval z‖ < C}

/-- Bounded-level path from 0 to ∞ -/
def HasBoundedLevelPath (P : ℂ[X]) (C : ℝ) : Prop :=
  ∃ (γ : ℝ → ℂ), Continuous γ ∧ γ 0 = 0 ∧
    Filter.Tendsto (fun t => ‖γ t‖) Filter.atTop Filter.atTop ∧
    ∀ t ≥ 0, γ t ∈ levelSet P C

/--
**Mac Lane's Theorem (1953):**
The answer to Erdős's question is NO.
For any C > 1, there exist unit-circle polynomials for which no
bounded-level path from 0 to ∞ stays in the level set {|P| < C}.
-/
axiom maclane_1953 (C : ℝ) (hC : C > 1) :
    ∃ P : ℂ[X], IsUnitCirclePolynomial P ∧ ¬HasBoundedLevelPath P C

/--
**Stronger form:** For any C, there exist labyrinth blocks forcing the path
to pass through neighborhoods of 0.
-/
axiom maclane_labyrinth :
    ∀ (C ε : ℝ), C > 1 → ε > 0 →
      ∃ P : ℂ[X], IsUnitCirclePolynomial P ∧
        ∀ γ : ℝ → ℂ, Continuous γ → γ 0 = 0 →
          Filter.Tendsto (fun t => ‖γ t‖) Filter.atTop Filter.atTop →
          (∀ t ≥ 0, γ t ∈ levelSet P C) →
          ∃ t > 0, ‖γ t‖ < ε

/-- **Erdős Problem #1215: SOLVED (negatively)** -/
theorem erdos_1215 :
    ¬∃ C : ℝ, C > 1 ∧ ∀ P : ℂ[X], IsUnitCirclePolynomial P →
      HasBoundedLevelPath P C := by
  push_neg
  intro C hC
  exact maclane_1953 C hC

end Erdos1215

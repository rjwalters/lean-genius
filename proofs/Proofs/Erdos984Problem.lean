/-
  Erdős Problem #984: 2-Coloring with Controlled Monochromatic Progressions

  Source: https://erdosproblems.com/984
  Status: SOLVED

  Statement:
  Can ℕ be 2-colored such that if {a, a+d, ..., a+(k-1)d} is a k-term
  monochromatic arithmetic progression, then k ≪_ε a^ε for all ε > 0?

  Answer: YES. Zach Hunter proved this is achievable.

  Known Results:
  - Spencer (1975): Achievable with 3 colors using h(a) (inverse van der Waerden function)
  - Erdős: Claimed k ≪ a^{1-c} for some c > 0 with 2 colors
  - Hunter: Proved the full result for 2 colors

  Related: Van der Waerden's theorem, Ramsey theory on integers

  Tags: arithmetic-progressions, ramsey-theory, additive-combinatorics
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

namespace Erdos984

open Nat Real

/-
## Part 1: Basic Definitions

Colorings and arithmetic progressions in ℕ.
-/

/-- A 2-coloring of ℕ (true = color 1, false = color 2) -/
def Coloring := ℕ → Bool

/-- An arithmetic progression with first term a, common difference d, and k terms -/
def ArithProg (a d k : ℕ) : Finset ℕ :=
  Finset.image (fun i => a + i * d) (Finset.range k)

/-- Check if all elements of a set have the same color -/
def IsMonochromatic (χ : Coloring) (S : Finset ℕ) : Prop :=
  ∃ c : Bool, ∀ n ∈ S, χ n = c

/-- Check if an arithmetic progression is monochromatic -/
def MonochromaticAP (χ : Coloring) (a d k : ℕ) : Prop :=
  IsMonochromatic χ (ArithProg a d k)

/-
## Part 2: The Growth Condition

The condition k ≪_ε a^ε means for all ε > 0, k ≤ C_ε · a^ε for some constant C_ε.
-/

/-- A function f grows slower than a^ε for all ε > 0 -/
def GrowsSlowerThanAnyPower (f : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, C > 0 ∧ ∀ a : ℕ, 0 < a → (f a : ℝ) ≤ C * (a : ℝ) ^ ε

/-- A coloring satisfies the Spencer-Erdős condition -/
def SatisfiesCondition (χ : Coloring) : Prop :=
  ∀ a d k : ℕ, 0 < a → 0 < d → 2 ≤ k →
    MonochromaticAP χ a d k →
    GrowsSlowerThanAnyPower (fun _ => k)

/-
## Part 3: Van der Waerden's Theorem Connection

Van der Waerden's theorem guarantees monochromatic APs exist in any finite coloring.
-/

/-- Van der Waerden's theorem: any r-coloring of a sufficiently long initial
    segment of ℕ contains a monochromatic k-term AP -/
/-
## Part 4: Spencer's 3-Coloring Result

Spencer proved the result holds with 3 colors.
-/

/-- A 3-coloring of ℕ -/
def Coloring3 := ℕ → Fin 3

/-- Monochromatic AP under 3-coloring -/
def MonochromaticAP3 (χ : Coloring3) (a d k : ℕ) : Prop :=
  ∃ c : Fin 3, ∀ i < k, χ (a + i * d) = c

/-- Spencer's theorem: 3-coloring with slowly growing bound -/
axiom spencer_1975 :
    ∃ χ : Coloring3, ∀ a d k : ℕ, 0 < a → 0 < d → 2 ≤ k →
      MonochromaticAP3 χ a d k →
      GrowsSlowerThanAnyPower (fun _ => k)

/-
## Part 5: Erdős's Partial Result

Erdős showed k ≪ a^{1-c} for some c > 0.
-/

/-- Erdős's weaker bound: k ≤ C · a^{1-c} -/
def ErdosWeakBound (χ : Coloring) (c C : ℝ) : Prop :=
  c > 0 ∧ C > 0 ∧
  ∀ a d k : ℕ, 0 < a → 0 < d → 2 ≤ k →
    MonochromaticAP χ a d k →
    (k : ℝ) ≤ C * (a : ℝ) ^ (1 - c)

/-- Erdős's construction -/
axiom erdos_partial_construction :
    ∃ χ : Coloring, ∃ c C : ℝ, ErdosWeakBound χ c C

/-
## Part 6: Hunter's Complete Solution

Zach Hunter proved the full result with 2 colors.
-/

/-- Hunter's theorem: 2-coloring achieving k ≪_ε a^ε -/
axiom hunter_theorem :
    ∃ χ : Coloring, SatisfiesCondition χ

/-
## Part 7: The Chromatic Number Perspective

How many colors are needed for various bounds?
-/

/-- For f(a) = a^ε (any ε > 0), 2 colors suffice -/
/-- 1 color is never sufficient (van der Waerden) -/
theorem one_color_insufficient :
    ¬∃ χ : ℕ → Fin 1, ∀ k : ℕ, 3 ≤ k →
      ¬∃ a d : ℕ, 0 < d ∧ ∀ i < k, χ (a + i * d) = χ a := by
  push_neg
  intro χ
  -- Any 1-coloring is trivially monochromatic everywhere
  use 3
  constructor
  · norm_num
  · use 0, 1
    constructor
    · norm_num
    · intro i _
      -- All values are Fin 1, so all equal
      simp [Fin.eq_zero]

/-
## Part 8: Explicit Bounds

Known bounds on the constants.
-/

/-- The optimal exponent in Erdős's construction -/
/-
## Part 9: Summary
-/

/-- **Erdős Problem #984: Summary**

Combines the main results:
1. Hunter's 2-coloring with k ≪_ε a^ε (the answer is YES)
2. Spencer's 3-coloring with slowly growing bound
3. Erdős's partial k ≪ a^{1-c} construction
-/
theorem erdos_984_summary :
    -- The problem is solved affirmatively (Hunter)
    (∃ χ : Coloring, SatisfiesCondition χ) ∧
    -- Spencer: 3 colors achieve inverse vdW bound
    (∃ χ : Coloring3, ∀ a d k : ℕ, 0 < a → 0 < d → 2 ≤ k →
      MonochromaticAP3 χ a d k →
      GrowsSlowerThanAnyPower (fun _ => k)) ∧
    -- Erdős partial: k ≪ a^{1-c}
    (∃ χ : Coloring, ∃ c C : ℝ, ErdosWeakBound χ c C) := by
  exact ⟨hunter_theorem, spencer_1975, erdos_partial_construction⟩

end Erdos984

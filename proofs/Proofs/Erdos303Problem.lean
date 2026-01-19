/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 902cbc85-4aed-4819-918b-8fbbbf60f71a

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem unitFractionEq_iff_alt (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    UnitFractionEq a b c ↔ UnitFractionEqAlt a b c

- theorem monochromatic_iff_alt (𝓒 : ℤ → α) (a b c : ℤ) :
    Monochromatic 𝓒 a b c ↔ MonochromaticAlt 𝓒 a b c

- theorem infinitely_many_solutions :
    ∀ n : ℤ, n ≥ 2 → UnitFractionEq n (n + 1) (n * (n + 1))
-/

/-
  Erdős Problem #303: Monochromatic Unit Fraction Solutions

  **Problem**: Is it true that in any finite colouring of the integers there
  exists a monochromatic solution to 1/a = 1/b + 1/c with distinct a, b, c?

  **Status**: SOLVED - TRUE

  **Solution**: Brown and Rödl (1991) proved this affirmatively.

  **Context**: This is a Ramsey-theoretic result about unit fractions.
  The equation 1/a = 1/b + 1/c is equivalent to bc = a(b + c), which
  constrains the relationship between a, b, c.

  The density version (Erdős #302) asks about sets of positive density.
  This colouring version is the Ramsey-theoretic analog.

  Reference: https://erdosproblems.com/303
  [BrRo91] Brown, Tom C. and Rödl, Voijtech,
           "Monochromatic solutions to equations with unit fractions"
           Bull. Austral. Math. Soc. (1991), 387-392.

  Source: Adapted from Google DeepMind Formal Conjectures project
-/

import Mathlib


open Set

namespace Erdos303

/-
## The Unit Fraction Equation

The equation 1/a = 1/b + 1/c relates three nonzero integers.
Multiplying through by abc gives: bc = a(b + c).
-/

/-- The unit fraction equation: 1/a = 1/b + 1/c.
    This is equivalent to bc = a(b + c) when a, b, c are nonzero. -/
def UnitFractionEq (a b c : ℤ) : Prop :=
  (1 / a : ℝ) = 1 / b + 1 / c

/-- Alternative formulation: bc = a(b + c). -/
def UnitFractionEqAlt (a b c : ℤ) : Prop :=
  b * c = a * (b + c)

/-- The two formulations are equivalent for nonzero integers. -/
theorem unitFractionEq_iff_alt (a b c : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    UnitFractionEq a b c ↔ UnitFractionEqAlt a b c := by
  -- The proof involves field_simp and algebraic manipulation
  -- From 1/a = 1/b + 1/c, multiply by abc to get bc = a(b+c)
  -- By definition of UnitFractionEq, we have $1/a = 1/b + 1/c$.
  simp [Erdos303.UnitFractionEq, Erdos303.UnitFractionEqAlt];
  -- By multiplying both sides of the equation by $a * b * c$, we can eliminate the denominators and obtain the equivalent equation $b * c = a * (b + c)$.
  field_simp [ha, hb, hc];
  norm_cast ; ring

/-
## Examples of Unit Fraction Solutions

Some concrete solutions to 1/a = 1/b + 1/c:
- 1/2 = 1/3 + 1/6: a=2, b=3, c=6
- 1/3 = 1/4 + 1/12: a=3, b=4, c=12
- 1/n = 1/(n+1) + 1/(n(n+1)) for any n ≥ 2
-/

/-- Example: 1/2 = 1/3 + 1/6 -/
theorem example_2_3_6 : UnitFractionEq 2 3 6 := by
  simp only [UnitFractionEq]
  norm_num

/-- Example: 1/3 = 1/4 + 1/12 -/
theorem example_3_4_12 : UnitFractionEq 3 4 12 := by
  simp only [UnitFractionEq]
  norm_num

/-- Example: 1/4 = 1/5 + 1/20 -/
theorem example_4_5_20 : UnitFractionEq 4 5 20 := by
  simp only [UnitFractionEq]
  norm_num

/-- Example: 1/6 = 1/7 + 1/42 -/
theorem example_6_7_42 : UnitFractionEq 6 7 42 := by
  simp only [UnitFractionEq]
  norm_num

/-
## Finite Colourings

A finite colouring of ℤ is a function 𝓒 : ℤ → C where C is a finite type.
We say a, b, c are monochromatic if they all have the same colour.
-/

/-- A finite colouring of the integers: a function with finite range. -/
def IsFiniteColouring (𝓒 : ℤ → α) : Prop := (Set.range 𝓒).Finite

/-- Three integers are monochromatic under colouring 𝓒 if they share a colour. -/
def Monochromatic (𝓒 : ℤ → α) (a b c : ℤ) : Prop :=
  𝓒 a = 𝓒 b ∧ 𝓒 b = 𝓒 c

/-- Alternative: the image of {a, b, c} under 𝓒 is a singleton. -/
def MonochromaticAlt (𝓒 : ℤ → α) (a b c : ℤ) : Prop :=
  (𝓒 '' {a, b, c}).Subsingleton

/-- The two monochromatic definitions are equivalent. -/
theorem monochromatic_iff_alt (𝓒 : ℤ → α) (a b c : ℤ) :
    Monochromatic 𝓒 a b c ↔ MonochromaticAlt 𝓒 a b c := by
  -- Equal colours iff image is singleton
  simp [Erdos303.Monochromatic, Erdos303.MonochromaticAlt];
  aesop_cat

/-
## The Main Theorem (Brown-Rödl 1991)

In any finite colouring of ℤ, there exist distinct a, b, c with
1/a = 1/b + 1/c that are all the same colour.
-/

/-- A valid solution: distinct nonzero integers satisfying the unit fraction equation. -/
def ValidSolution (a b c : ℤ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ UnitFractionEq a b c

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos303.brownRodl_theorem', 'harmonicSorry970858']-/
/-- **Erdős Problem #303 (SOLVED)**: Brown-Rödl Theorem.

In any finite colouring of the integers, there exists a monochromatic
solution to 1/a = 1/b + 1/c with distinct nonzero a, b, c.

This was proved by Brown and Rödl in 1991. -/
axiom brownRodl_theorem :
  ∀ (𝓒 : ℤ → ℤ), IsFiniteColouring 𝓒 →
    ∃ (a b c : ℤ), ValidSolution a b c ∧ Monochromatic 𝓒 a b c

/-- Alternative formulation matching formal-conjectures statement. -/
def erdos303Statement : Prop :=
  ∀ (𝓒 : ℤ → ℤ), (Set.range 𝓒).Finite →
    ∃ (a b c : ℤ),
      [a, b, c, 0].Nodup ∧
      (1/a : ℝ) = 1/b + 1/c ∧
      (𝓒 '' {a, b, c}).Subsingleton

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unexpected axioms were added during verification: ['Erdos303.erdos303_true', 'harmonicSorry537023']-/
/-- The statement is true. -/
axiom erdos303_true : erdos303Statement

/-
## Why the Theorem is True: Proof Sketch

The Brown-Rödl proof uses Ramsey theory:

1. Consider the family of all solutions to 1/a = 1/b + 1/c.
   There are infinitely many solutions of the form:
   - 1/n = 1/(n+1) + 1/(n(n+1)) for any n ≥ 2.

2. Fix a finite colouring with k colours.

3. By a Ramsey-theoretic argument (using van der Waerden or similar),
   among sufficiently many solutions, some three must share a colour.

4. The key is showing that the solution space has enough structure
   to force monochromatic solutions via pigeonhole/Ramsey arguments.
-/

/-- Infinitely many solutions exist of the form 1/n = 1/(n+1) + 1/(n(n+1)).
    Verification: 1/(n+1) + 1/(n(n+1)) = n/(n(n+1)) + 1/(n(n+1)) = (n+1)/(n(n+1)) = 1/n. ✓ -/
theorem infinitely_many_solutions :
    ∀ n : ℤ, n ≥ 2 → UnitFractionEq n (n + 1) (n * (n + 1)) := by
  intro n hn
  -- Technical proof involving field_simp and ring
  unfold Erdos303.UnitFractionEq;
  field_simp;
  push_cast; ring;

/-- The solutions n, (n+1), n(n+1) are distinct for n ≥ 2. -/
theorem solution_distinct (n : ℤ) (hn : n ≥ 2) :
    n ≠ n + 1 ∧ n + 1 ≠ n * (n + 1) ∧ n ≠ n * (n + 1) := by
  constructor
  · omega
  constructor
  · -- n+1 ≠ n(n+1) means n+1 ≠ (n+1)*n, i.e., 1 ≠ n
    intro h
    have h1 : n * (n + 1) = n + 1 := h.symm
    have h2 : n * (n + 1) - (n + 1) = 0 := by omega
    have h3 : (n - 1) * (n + 1) = 0 := by ring_nf; linarith
    have : n - 1 = 0 ∨ n + 1 = 0 := Int.mul_eq_zero.mp h3
    omega
  · -- n ≠ n(n+1) means n ≠ n*(n+1), i.e., 1 ≠ n+1
    intro h
    have h1 : n * (n + 1) = n := h.symm
    have h2 : n * (n + 1) - n = 0 := by omega
    have h3 : n * n = 0 := by ring_nf; linarith
    have : n = 0 := by
      cases Int.mul_eq_zero.mp h3 with
      | inl h => exact h
      | inr h => exact h
    omega

/-
## Connection to the Density Version (Erdős #302)

Problem #302 asks the density version: does every set of positive upper
density contain a solution to 1/a = 1/b + 1/c?

The colouring version (this problem) is the Ramsey-theoretic analog.
By Furstenberg's correspondence principle, density results often imply
colouring results, but not always vice versa.
-/

/-- The density version would state that any set A ⊆ ℤ with positive
    upper density contains a solution. This is Erdős Problem #302. -/
def densityVersion : Prop :=
  ∀ A : Set ℤ, (∃ d : ℝ, d > 0 ∧ ∀ N : ℕ, N > 0 →
    ((A ∩ Finset.Icc (-N : ℤ) N).toFinite.toFinset.card : ℝ) / (2 * N + 1) ≥ d) →
  ∃ a b c : ℤ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ ValidSolution a b c

/-
## The General Pattern

For any n ≥ 2, we have the solution (n, n+1, n(n+1)):
- n = 2: (2, 3, 6) gives 1/2 = 1/3 + 1/6
- n = 3: (3, 4, 12) gives 1/3 = 1/4 + 1/12
- n = 4: (4, 5, 20) gives 1/4 = 1/5 + 1/20
- n = 5: (5, 6, 30) gives 1/5 = 1/6 + 1/30
- n = 6: (6, 7, 42) gives 1/6 = 1/7 + 1/42

These infinitely many solutions guarantee that in any finite colouring,
by pigeonhole, infinitely many share the same colour, and the Ramsey
argument shows a monochromatic triple can be found among them.
-/

end Erdos303
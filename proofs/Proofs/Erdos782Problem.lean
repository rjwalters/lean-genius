/-
Erdős Problem #782: Quasi-Progressions and Cubes in the Squares

**Problem Statement (OPEN)**

**Question 1 (Quasi-Progressions):**
Do the perfect squares contain arbitrarily long quasi-progressions?
A quasi-progression has bounded gaps: x₁ < ... < xₖ with d ≤ xᵢ₊₁ - xᵢ ≤ d + C for some d, C.

**Question 2 (Cubes in Squares):**
Do the squares contain arbitrarily large combinatorial cubes?
A cube: a + {∑ᵢ∈I bᵢ : I ⊆ {1,...,k}} = {a + ε₁b₁ + ... + εₖbₖ : εᵢ ∈ {0,1}}.

**Known Results:**
- Squares contain no 4-term arithmetic progressions (classical)
- Affirmative Q1 implies affirmative Q2
- Solymosi (2007): conjectured Q2 has negative answer
- Cilleruelo-Granville (2007): Q2 negative under Bombieri-Lang

**Status:** OPEN

**Reference:** Brown, Erdős, Freedman [BEF90]

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open Set Nat Finset

namespace Erdos782

/-!
# Part 1: Basic Definitions

Define the set of perfect squares and arithmetic progressions.
-/

-- The set of perfect squares
def Squares : Set ℕ := {n | ∃ k : ℕ, n = k^2}

-- A number is a perfect square
def IsSquare (n : ℕ) : Prop := n ∈ Squares

-- Membership characterization
theorem isSquare_iff (n : ℕ) : IsSquare n ↔ ∃ k, n = k^2 := Iff.rfl

-- Small examples
example : IsSquare 0 := ⟨0, rfl⟩
example : IsSquare 1 := ⟨1, rfl⟩
example : IsSquare 4 := ⟨2, rfl⟩
example : IsSquare 9 := ⟨3, rfl⟩

/-!
# Part 2: Arithmetic Progressions in Squares

Classical result: squares don't contain 4-term APs.
-/

-- An arithmetic progression of length k starting at a with step d
def ArithProg (a d k : ℕ) : Fin k → ℕ := fun i => a + i.val * d

-- A set contains an arithmetic progression of length k
def ContainsAP (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : Fin k, ArithProg a d k i ∈ S

-- Classical: squares contain length-3 APs
-- Example: 1, 25, 49 is an AP with d=24 (1=1², 25=5², 49=7²)
-- Actually: 1, 25, 49 has d=24 but 25-1=24, 49-25=24 ✓
axiom squares_contain_3AP : ContainsAP Squares 3

-- Fermat's theorem: x⁴ + y⁴ = z⁴ has no solutions (implies no 4-AP)
-- Actually: x², y², z², w² in AP means (y²-x²) = (z²-y²) = (w²-z²)
-- This leads to Fermat-type equations with no solutions

-- Classical: squares don't contain 4-term APs
axiom no_4AP_in_squares : ¬ContainsAP Squares 4

/-!
# Part 3: Quasi-Progressions

A quasi-progression has bounded gaps: d ≤ gap ≤ d + C.
-/

-- A sequence is a C-quasi-progression with step ~d
def IsQuasiProg (C : ℕ) (x : ℕ → ℕ) (k d : ℕ) : Prop :=
  d > 0 ∧ (∀ i < k - 1, x i < x (i + 1)) ∧
  (∀ i < k - 1, d ≤ x (i + 1) - x i ∧ x (i + 1) - x i ≤ d + C)

-- A set contains a C-quasi-progression of length k
def ContainsQuasiProg (S : Set ℕ) (C k : ℕ) : Prop :=
  ∃ x : ℕ → ℕ, ∃ d : ℕ, IsQuasiProg C x k d ∧ (∀ i < k, x i ∈ S)

-- Question 1: Do squares contain arbitrarily long quasi-progressions?
def Question1 : Prop :=
  ∃ C : ℕ, ∀ k : ℕ, ContainsQuasiProg Squares C k

-- Alternative formulation: for each k, there exists C(k)
def Question1Weak : Prop :=
  ∀ k : ℕ, ∃ C : ℕ, ContainsQuasiProg Squares C k

-- The weak version is trivially true for each fixed k
-- The strong version (uniform C) is the real question

/-!
# Part 4: Combinatorial Cubes

A k-cube is {a + ∑_{i ∈ I} bᵢ : I ⊆ {1,...,k}}.
-/

-- The vertices of a k-dimensional combinatorial cube
-- Given base a and steps b₁, ..., bₖ, vertices are a + ∑ εᵢbᵢ
def CubeVertices (k : ℕ) (a : ℕ) (b : Fin k → ℕ) : Set ℕ :=
  {n | ∃ S : Finset (Fin k), n = a + S.sum b}

-- A cube is non-trivial if all bᵢ > 0
def IsNontrivialCube (k : ℕ) (a : ℕ) (b : Fin k → ℕ) : Prop :=
  ∀ i, b i > 0

-- A set contains a k-cube
def ContainsCube (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a : ℕ, ∃ b : Fin k → ℕ, IsNontrivialCube k a b ∧
    CubeVertices k a b ⊆ S

-- Question 2: Do squares contain arbitrarily large cubes?
def Question2 : Prop :=
  ∀ k : ℕ, ContainsCube Squares k

-- 2-cube example: {a, a+b₁, a+b₂, a+b₁+b₂} all squares
-- This means finding a, b₁, b₂ with all four being squares

/-!
# Part 5: Relationship Between Questions

An affirmative answer to Q1 implies affirmative to Q2.
-/

-- If squares have arbitrarily long quasi-progressions with uniform C,
-- then they contain arbitrarily large cubes
axiom question1_implies_question2 : Question1 → Question2

-- Contrapositive: if Q2 is false, so is Q1
theorem no_cubes_implies_no_quasiprog : ¬Question2 → ¬Question1 := by
  intro hq2 hq1
  exact hq2 (question1_implies_question2 hq1)

/-!
# Part 6: Solymosi's Conjecture

Solymosi (2007) conjectured that Q2 has a negative answer.
-/

-- Solymosi's conjecture: Q2 is false
def SolymosiConjecture : Prop := ¬Question2

-- Equivalently: there exists k such that squares contain no k-cube
def SolymosiConjectureAlt : Prop :=
  ∃ k : ℕ, ¬ContainsCube Squares k

-- These are equivalent
theorem solymosi_equiv : SolymosiConjecture ↔ SolymosiConjectureAlt := by
  constructor
  · intro h
    by_contra hall
    push_neg at hall
    exact h hall
  · intro ⟨k, hk⟩ hq2
    exact hk (hq2 k)

/-!
# Part 7: Cilleruelo-Granville Conditional Result

Under the Bombieri-Lang conjecture, Q2 has a negative answer.
-/

-- The Bombieri-Lang conjecture (simplified statement)
-- For varieties of general type over ℚ, rational points are not Zariski dense
def BombieriLangConjecture : Prop := True  -- Placeholder; actual statement is complex

-- Under Bombieri-Lang, squares contain no large cubes
axiom cilleruelo_granville :
  BombieriLangConjecture → ∃ k : ℕ, ¬ContainsCube Squares k

-- This gives a conditional answer to Q2
theorem conditional_q2_negative (hBL : BombieriLangConjecture) : ¬Question2 := by
  intro hq2
  obtain ⟨k, hk⟩ := cilleruelo_granville hBL
  exact hk (hq2 k)

/-!
# Part 8: Small Cases

Analyze small cubes in squares.
-/

-- 1-cube: {a, a+b} both squares (sum of two squares structure)
-- This is possible: {0, 1} or {1, 4} won't work, but...
-- Actually {16, 25} = {4², 5²} with b = 9 works

-- 2-cube: {a, a+b₁, a+b₂, a+b₁+b₂} all squares
-- More constrained

-- Checking if small cubes exist
def Has2Cube : Prop := ContainsCube Squares 2

-- Has3Cube would be even harder
def Has3Cube : Prop := ContainsCube Squares 3

/-!
# Part 9: Density Considerations

Squares are sparse: |{n² ≤ x}| = √x.
-/

-- Number of squares up to n
noncomputable def numSquaresUpTo (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter IsSquare |>.card

-- Asymptotic: numSquaresUpTo(n) ~ √n
-- This sparsity is why finding structures in squares is hard

-- Quasi-progressions of length k need ~k elements in interval of length ~k*d
-- If d is small, interval has ~√(k*d) squares, need k of them
-- This constrains what's possible

/-!
# Part 10: Problem Status

The problem remains OPEN.
-/

-- The problem is open
def erdos_782_status : String := "OPEN"

-- Main formal statements
theorem erdos_782_question1 :
    Question1 ↔ ∃ C : ℕ, ∀ k : ℕ, ContainsQuasiProg Squares C k := by
  rfl

theorem erdos_782_question2 :
    Question2 ↔ ∀ k : ℕ, ContainsCube Squares k := by
  rfl

-- Combined problem status
def ErdosProblem782 : Prop := Question1 ∨ ¬Question1  -- Either answer is open

/-!
# Summary

**Problem:** Two questions about structure in perfect squares:
1. Do squares contain arbitrarily long quasi-progressions (with uniform bound C)?
2. Do squares contain arbitrarily large combinatorial cubes?

**Known:**
- Squares have 3-term APs but no 4-term APs
- Q1 affirmative implies Q2 affirmative
- Solymosi conjectures Q2 is negative
- Cilleruelo-Granville: Q2 negative under Bombieri-Lang

**Unknown:**
- Answers to both Q1 and Q2
- Whether Q2 negative implies Q1 negative (likely yes)

**Difficulty:** Combines additive combinatorics with algebraic geometry.
-/

end Erdos782

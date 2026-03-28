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

/-
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

/-
# Part 2: Arithmetic Progressions in Squares

Classical result: squares don't contain 4-term APs.
-/

-- An arithmetic progression of length k starting at a with step d
def ArithProg (a d k : ℕ) : Fin k → ℕ := fun i => a + i.val * d

-- A set contains an arithmetic progression of length k
def ContainsAP (S : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : Fin k, ArithProg a d k i ∈ S

/-- Squares contain a 3-term AP: {1, 25, 49} = {1², 5², 7²} with d = 24.
    Proof by explicit construction. -/
theorem squares_contain_3AP : ContainsAP Squares 3 := by
  refine ⟨1, 24, by omega, fun i => ?_⟩
  simp only [ArithProg, Squares, Set.mem_setOf_eq]
  fin_cases i
  · exact ⟨1, by norm_num⟩   -- 1 + 0*24 = 1 = 1²
  · exact ⟨5, by norm_num⟩   -- 1 + 1*24 = 25 = 5²
  · exact ⟨7, by norm_num⟩   -- 1 + 2*24 = 49 = 7²

-- Fermat's theorem: x⁴ + y⁴ = z⁴ has no solutions (implies no 4-AP)
-- Actually: x², y², z², w² in AP means (y²-x²) = (z²-y²) = (w²-z²)
-- This leads to Fermat-type equations with no solutions

-- Classical: squares don't contain 4-term APs
axiom no_4AP_in_squares : ¬ContainsAP Squares 4

/-
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

-- The strong version (uniform C) is the real question.
-- The weak version is trivially true: consecutive squares (i+1)² form quasi-progs.

/-- Q1 (uniform C) implies Q1Weak (C may depend on k). -/
theorem question1_implies_question1Weak : Question1 → Question1Weak :=
  fun ⟨C, hC⟩ k => ⟨C, hC k⟩

/-- The weak formulation is trivially true: consecutive squares {1²,2²,...,k²}
    form a quasi-progression with d=3, C=2k. Gaps are (i+2)²-(i+1)²=2i+3,
    ranging from 3 to 2k-1. -/
theorem question1Weak_true : Question1Weak := by
  intro k
  use 2 * k, fun i => (i + 1) ^ 2, 3
  refine ⟨⟨by omega, ?_, ?_⟩, ?_⟩
  · -- Strictly increasing: (i+1)² < (i+2)²
    intro i _
    nlinarith
  · -- Gaps bounded: 3 ≤ (i+2)²-(i+1)² ≤ 3+2k
    intro i hi
    have hgap : (i + 1 + 1) ^ 2 = (i + 1) ^ 2 + (2 * i + 3) := by ring
    constructor <;> omega
  · -- All elements are squares
    intro i _
    exact ⟨i + 1, rfl⟩

/-
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

/-
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

/-
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

/-
# Part 7: Cilleruelo-Granville Conditional Result

Under the Bombieri-Lang conjecture, Q2 has a negative answer.
-/

/-- **Bombieri-Lang Conjecture (simplified):** For algebraic varieties of
    general type defined over ℚ, the set of rational points is not
    Zariski dense. Formalized as: for all d ≥ 2, the rational points on
    "generic" degree-d hypersurfaces in ℙⁿ are contained in finitely
    many proper subvarieties. We use `opaque` rather than `axiom` since
    this merely names an unspecified Prop (it does not assert truth or
    falsity); the full algebraic geometry machinery is beyond Mathlib. -/
opaque BombieriLangConjecture : Prop := True

-- Under Bombieri-Lang, squares contain no large cubes
axiom cilleruelo_granville :
  BombieriLangConjecture → ∃ k : ℕ, ¬ContainsCube Squares k

-- This gives a conditional answer to Q2
theorem conditional_q2_negative (hBL : BombieriLangConjecture) : ¬Question2 := by
  intro hq2
  obtain ⟨k, hk⟩ := cilleruelo_granville hBL
  exact hk (hq2 k)

/-
# Part 8: Small Cases

Analyze small cubes in squares.
-/

-- 1-cube example: {0, 1} = {0², 1²} with b₀ = 1
-- 2-cube example: {0, 9, 16, 25} = {0², 3², 4², 5²} via 3² + 4² = 5²
--   (a = 0, b₀ = 9, b₁ = 16, using the Pythagorean triple)
-- 3-cube would require 8 squares in combinatorial cube structure — hard

def Has2Cube : Prop := ContainsCube Squares 2
def Has3Cube : Prop := ContainsCube Squares 3

/-- The Pythagorean triple 3² + 4² = 5² gives a 2-cube in the squares:
    {0, 9, 16, 25} = {0², 3², 4², 5²} with a = 0, b₀ = 9, b₁ = 16.
    Proof by exhaustive case analysis over all 4 subsets of Fin 2. -/
theorem squares_contain_2cube : Has2Cube := by
  refine ⟨0, ![9, 16], fun i => by fin_cases i <;> simp, fun n ⟨S, rfl⟩ => ?_⟩
  simp only [zero_add, Squares, Set.mem_setOf_eq]
  by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
  · -- S = {0, 1}: sum = 9 + 16 = 25 = 5²
    have : S = Finset.univ := by ext x; fin_cases x <;> simp [*]
    subst this; simp [Fin.sum_univ_two]; exact ⟨5, by norm_num⟩
  · -- S = {0}: sum = 9 = 3²
    have : S = {0} := by ext x; fin_cases x <;> simp [*]
    subst this; simp; exact ⟨3, by norm_num⟩
  · -- S = {1}: sum = 16 = 4²
    have : S = {(1 : Fin 2)} := by ext x; fin_cases x <;> simp [*]
    subst this; simp; exact ⟨4, by norm_num⟩
  · -- S = ∅: sum = 0 = 0²
    have : S = ∅ := by ext x; fin_cases x <;> simp [*]
    subst this; simp; exact ⟨0, by norm_num⟩

/-
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

/-
# Part 10: Problem Status

The problem remains OPEN.
-/

-- Main formal statements
theorem erdos_782_question1 :
    Question1 ↔ ∃ C : ℕ, ∀ k : ℕ, ContainsQuasiProg Squares C k := by
  rfl

theorem erdos_782_question2 :
    Question2 ↔ ∀ k : ℕ, ContainsCube Squares k := by
  rfl

/-
# Summary

**Problem Status: OPEN**

**Proved Theorems (0 sorries)**:
- squares_contain_3AP: {1, 25, 49} = {1², 5², 7²} is a 3-term AP (d=24) [was axiom]
- squares_contain_2cube: {0, 9, 16, 25} = {0², 3², 4², 5²} is a 2-cube (Pythagorean triple)
- question1Weak_true: consecutive squares form quasi-progressions (Q1Weak trivially true)
- question1_implies_question1Weak: Q1 → Q1Weak (quantifier swap)
- no_cubes_implies_no_quasiprog: ¬Q2 → ¬Q1 (contrapositive)
- conditional_q2_negative: Bombieri-Lang → ¬Q2
- solymosi_equiv: Solymosi conjecture equivalence
- erdos_782_question1/question2: definitional unfoldings

**Axioms (3)**:
- no_4AP_in_squares: classical — reducible to `not_fermat_42` from Mathlib.FLT.Four
- question1_implies_question2: combinatorial (Ramsey-type argument)
- cilleruelo_granville: conditional result [CiGr07]

**Opaque Constants (1)**:
- BombieriLangConjecture: open conjecture in algebraic geometry (opaque Prop, not an axiom)

**Key Improvements**:
- Eliminated `squares_contain_3AP` axiom by explicit construction
- Proved `squares_contain_2cube`: Pythagorean triple gives concrete 2-cube in squares
- Converted `BombieriLangConjecture` from axiom to opaque (not a mathematical assumption)
- Proved Q1Weak (weak quasi-progression existence) via consecutive squares construction

**Next target**: `no_4AP_in_squares` can be proved via Mathlib's `not_fermat_42`
(a⁴+b⁴≠c² for nonzero a,b). The reduction: from 2q²=p²+r² and 2r²=q²+s²,
parameterize via Pythagorean triples (α,β,q) and (γ,δ,r) with αβ=γδ,
then derive a solution to x⁴+y⁴=z² contradicting `not_fermat_42`.

References:
- Brown, Erdős, Freedman [BEF90]: posed the problem
- Solymosi [So07]: conjectured Q2 negative
- Cilleruelo, Granville [CiGr07]: Q2 negative under Bombieri-Lang
-/

end Erdos782

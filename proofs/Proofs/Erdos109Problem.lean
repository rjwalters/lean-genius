/-
Erdős Problem #109: The Erdős Sumset Conjecture

Source: https://erdosproblems.com/109
Status: SOLVED (Moreira-Richter-Robertson 2019)

Statement:
Any A ⊆ ℕ of positive upper density contains a sumset B + C where both B and C are infinite.

This is known as the "Erdős Sumset Conjecture."

History:
- Erdős: Conjectured this result
- Moreira-Richter-Robertson (2019): PROVED the conjecture in Annals of Mathematics

Key insight: Sets of positive density are "additively rich" enough to contain
structured infinite sumsets, despite the possibility of irregular distribution.

Related to Problem #656.

Reference: Moreira, Richter, Robertson (2019) "A proof of a sumset conjecture of Erdős"
           Ann. of Math. (2) 189(2):605-652
-/

import Mathlib

open Set Finset Filter BigOperators

namespace Erdos109

/-! ## Density Definitions -/

/-- The counting function: number of elements of A in {1,...,N}. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- The upper density of a set A ⊆ ℕ. -/
noncomputable def upperDensity (A : Set ℕ) : ℝ :=
  Filter.limsup (fun N => (countingFn A N : ℝ) / N) Filter.atTop

/-- A set has positive upper density. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < upperDensity A

/-- The lower density of a set A ⊆ ℕ. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N => (countingFn A N : ℝ) / N) Filter.atTop

/-- A set has positive lower density (stronger than positive upper density). -/
def HasPositiveLowerDensity (A : Set ℕ) : Prop :=
  0 < lowerDensity A

/-- Lower density is at most upper density. -/
theorem lowerDensity_le_upperDensity (A : Set ℕ) :
    lowerDensity A ≤ upperDensity A := by
  unfold lowerDensity upperDensity
  -- liminf ≤ limsup for any bounded sequence
  sorry

/-- Positive lower density implies positive upper density. -/
theorem posLowerDensity_implies_posUpperDensity (A : Set ℕ) :
    HasPositiveLowerDensity A → HasPositiveUpperDensity A := by
  intro h
  unfold HasPositiveUpperDensity
  calc 0 < lowerDensity A := h
       _ ≤ upperDensity A := lowerDensity_le_upperDensity A

/-! ## Sumset Definition -/

/-- The sumset B + C: all sums b + c with b ∈ B and c ∈ C. -/
def Sumset (B C : Set ℕ) : Set ℕ :=
  { n | ∃ b ∈ B, ∃ c ∈ C, n = b + c }

notation:65 B " +ₛ " C => Sumset B C

/-- Basic property: zero is in B + C if both contain zero. -/
theorem zero_mem_sumset (B C : Set ℕ) (hB : 0 ∈ B) (hC : 0 ∈ C) :
    0 ∈ B +ₛ C := by
  use 0, hB, 0, hC

/-- Sumset is commutative. -/
theorem sumset_comm (B C : Set ℕ) : (B +ₛ C) = (C +ₛ B) := by
  ext n
  simp only [Sumset, Set.mem_setOf_eq]
  constructor
  · intro ⟨x, hx, y, hy, h⟩
    exact ⟨y, hy, x, hx, by omega⟩
  · intro ⟨x, hx, y, hy, h⟩
    exact ⟨y, hy, x, hx, by omega⟩

/-! ## The Erdős Sumset Conjecture -/

/--
**Erdős Sumset Conjecture** (PROVED by Moreira-Richter-Robertson 2019):

Any A ⊆ ℕ of positive upper density contains a sumset B + C
where both B and C are infinite.

This was a longstanding conjecture of Erdős that connects density
and additive structure.
-/
def ErdosSumsetConjecture : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ A

/--
**Moreira-Richter-Robertson Theorem (2019)**:
The Erdős Sumset Conjecture is true.

This was proved in "A proof of a sumset conjecture of Erdős"
published in Annals of Mathematics in 2019.
-/
axiom moreira_richter_robertson : ErdosSumsetConjecture

/-- The conjecture is resolved. -/
theorem erdos_109_solved : ErdosSumsetConjecture := moreira_richter_robertson

/-! ## Consequences and Related Results -/

/-- A set containing an infinite sumset B + C is necessarily infinite. -/
theorem sumset_infinite_implies_superset_infinite (A B C : Set ℕ)
    (hB : B.Infinite) (hC : C.Infinite) (h : (B +ₛ C) ⊆ A) :
    A.Infinite := by
  apply Set.Infinite.mono h
  -- B + C is infinite if both B and C are infinite
  by_contra hfin
  push_neg at hfin
  -- If B + C is finite, then for any fixed b ∈ B, the set {b + c : c ∈ C} is finite
  -- But this set has the same cardinality as C, contradiction
  obtain ⟨b, hb⟩ := hB.nonempty
  have hinf : Set.Infinite { n | ∃ c ∈ C, n = b + c } := by
    -- The map c ↦ b + c is an injection from C to this set
    -- Since C is infinite, so is this set
    sorry
  have hsub : { n | ∃ c ∈ C, n = b + c } ⊆ (B +ₛ C) := by
    intro n ⟨c, hc, hn⟩
    simp only [Sumset, Set.mem_setOf_eq]
    exact ⟨b, hb, c, hc, hn⟩
  exact hinf (hfin.subset hsub)

/-- Corollary: Sets of positive upper density are infinite. -/
theorem posUpperDensity_infinite (A : Set ℕ) (h : HasPositiveUpperDensity A) :
    A.Infinite := by
  obtain ⟨B, C, hB, hC, hsub⟩ := moreira_richter_robertson A h
  exact sumset_infinite_implies_superset_infinite A B C hB hC hsub

/-! ## Strengthenings -/

/--
**Stronger Form** (also proved):
The sets B and C can be chosen to have arbitrarily large gaps between
consecutive elements. This shows the sumset structure is quite robust.
-/
def StrongerSumsetConjecture : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∀ f : ℕ → ℕ, (∀ n, f n > 0) →
      ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ A ∧
        (∀ b₁ b₂, b₁ ∈ B → b₂ ∈ B → b₁ < b₂ → b₂ - b₁ ≥ f b₁)

/--
**Connection to Szemerédi's Theorem**:
Sets of positive density contain arbitrarily long arithmetic progressions.
The sumset conjecture is a different kind of additive structure result.
-/
theorem szemer_compared :
    -- Szemerédi: positive density → contains k-APs for all k
    -- Erdős: positive density → contains infinite sumset B + C
    -- These are complementary results about additive structure
    True := trivial

/-! ## Examples -/

/-- The natural numbers have density 1 and trivially satisfy the conjecture. -/
example : HasPositiveUpperDensity (Set.univ : Set ℕ) := by
  unfold HasPositiveUpperDensity upperDensity countingFn
  simp only [Set.univ_inter]
  -- The density of ℕ is 1
  sorry

/-- The even numbers have density 1/2 and satisfy the conjecture. -/
def evenNumbers : Set ℕ := { n | Even n }

theorem even_has_pos_density : HasPositiveUpperDensity evenNumbers := by
  sorry

/-- For even numbers, we can take B = C = {0, 2, 4, ...}. -/
theorem even_sumset_example :
    ∃ B C : Set ℕ, B.Infinite ∧ C.Infinite ∧ (B +ₛ C) ⊆ evenNumbers := by
  use evenNumbers, evenNumbers
  refine ⟨?_, ?_, ?_⟩
  · -- Even numbers are infinite (2n for n ∈ ℕ)
    sorry
  · -- Same as above
    sorry
  · -- evenNumbers + evenNumbers ⊆ evenNumbers
    intro n hn
    simp only [Sumset, Set.mem_setOf_eq] at hn
    obtain ⟨b, ⟨kb, hb⟩, c, ⟨kc, hc⟩, hn⟩ := hn
    simp only [evenNumbers, Set.mem_setOf_eq, Even]
    use kb + kc
    linarith

/-! ## Proof Techniques

The Moreira-Richter-Robertson proof uses:
1. Ergodic theory and measure-preserving systems
2. Furstenberg correspondence principle
3. IP-sets and recurrence along polynomial sequences
4. Sophisticated combinatorial arguments

The proof is highly non-trivial and represents a major achievement in
combinatorial ergodic theory.
-/

/-! ## Summary

**Problem Status: SOLVED**

Erdős Problem #109 asked whether every set A ⊆ ℕ of positive upper density
contains a sumset B + C with both B and C infinite.

**Answer: YES** (Moreira-Richter-Robertson 2019)

**Key Results**:
1. Proved in Annals of Mathematics 2019
2. Uses ergodic theory and Furstenberg correspondence
3. Establishes a fundamental connection between density and additive structure

**Related Problems**:
- Problem #656: Related sumset questions
- Szemerédi's theorem: Different additive structure (arithmetic progressions)

References:
- Moreira, Richter, Robertson (2019): "A proof of a sumset conjecture of Erdős"
  Ann. of Math. (2) 189(2):605-652
-/

end Erdos109

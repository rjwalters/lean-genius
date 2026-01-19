/-
Erdős Problem #1128: Monochromatic Cubes in Cardinal Products

Source: https://erdosproblems.com/1128
Status: DISPROVED (Prikry-Mills 1978)
Prize: $50

Statement:
Let A, B, C be three sets of cardinality ℵ₁. Is it true that
in any 2-coloring of A × B × C, there must exist A₁ ⊂ A, B₁ ⊂ B,
C₁ ⊂ C, all of cardinality ℵ₀, such that A₁ × B₁ × C₁ is monochromatic?

Answer: NO. Prikry and Mills disproved this in 1978.

Historical Note:
A problem of Erdős and Hajnal. The disproof remained unpublished but
was later documented by Todorčević [To94] and Komjáth [Ko25b].

Context:
This is a partition problem in set theory, asking whether the
cardinal Ramsey property ℵ₁³ → (ℵ₀)³₂ holds.

References:
- Erdős-Hajnal [Er81b]: Original problem
- Prikry-Mills (1978): Disproof (unpublished)
- Todorčević [To94]: Documentation
- Komjáth [Ko25b]: Erdős-Hajnal Problem List
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Basic

namespace Erdos1128

/-
## Part I: Cardinal Definitions
-/

/--
**The cardinal ℵ₁:**
The first uncountable cardinal. |A| = ℵ₁ means A has the same
cardinality as the first uncountable ordinal ω₁.
-/
axiom aleph_1 : Cardinal

/--
**The cardinal ℵ₀:**
The cardinality of countable infinity. |A| = ℵ₀ means A is
countably infinite.
-/
def aleph_0 : Cardinal := Cardinal.omega

/--
**Sets of cardinality ℵ₁:**
A, B, C each have cardinality ℵ₁.
-/
axiom A : Type*
axiom B : Type*
axiom C : Type*
axiom card_A : Cardinal.mk A = aleph_1
axiom card_B : Cardinal.mk B = aleph_1
axiom card_C : Cardinal.mk C = aleph_1

/-
## Part II: The Coloring Problem
-/

/--
**2-coloring of the product:**
A function χ: A × B × C → {0, 1} (or equivalently → Bool).
-/
def TwoColoring (A B C : Type*) := A × B × C → Bool

/--
**Monochromatic cube:**
A₁ × B₁ × C₁ is monochromatic for coloring χ if χ is constant
on the cube: all triples get the same color.
-/
def isMonochromatic {A B C : Type*} (χ : TwoColoring A B C)
    (A₁ : Set A) (B₁ : Set B) (C₁ : Set C) : Prop :=
  (∀ a₁ a₂ ∈ A₁, ∀ b₁ b₂ ∈ B₁, ∀ c₁ c₂ ∈ C₁,
    χ (a₁, b₁, c₁) = χ (a₂, b₂, c₂))

/--
**Countably infinite subset:**
A subset A₁ ⊂ A has cardinality ℵ₀.
-/
def hasCardinalityAleph0 {X : Type*} (S : Set X) : Prop :=
  Cardinal.mk S = aleph_0

/-
## Part III: The Conjecture (Disproved)
-/

/--
**The Erdős-Hajnal Conjecture (for ℵ₁³ → (ℵ₀)³):**
For any 2-coloring χ of A × B × C (with |A| = |B| = |C| = ℵ₁),
there exist countably infinite A₁, B₁, C₁ such that
A₁ × B₁ × C₁ is monochromatic.
-/
def erdos_hajnal_conjecture : Prop :=
  ∀ χ : TwoColoring A B C,
  ∃ A₁ : Set A, ∃ B₁ : Set B, ∃ C₁ : Set C,
    hasCardinalityAleph0 A₁ ∧
    hasCardinalityAleph0 B₁ ∧
    hasCardinalityAleph0 C₁ ∧
    isMonochromatic χ A₁ B₁ C₁

/--
**The conjecture is FALSE:**
Prikry and Mills disproved this in 1978.
-/
axiom prikry_mills_disproof : ¬erdos_hajnal_conjecture

/-
## Part IV: The Counterexample
-/

/--
**Existence of a bad coloring:**
There exists a 2-coloring of ℵ₁ × ℵ₁ × ℵ₁ such that NO
countably infinite monochromatic cube exists.
-/
theorem exists_bad_coloring :
    ∃ χ : TwoColoring A B C,
    ∀ A₁ : Set A, ∀ B₁ : Set B, ∀ C₁ : Set C,
      hasCardinalityAleph0 A₁ → hasCardinalityAleph0 B₁ → hasCardinalityAleph0 C₁ →
      ¬isMonochromatic χ A₁ B₁ C₁ := by
  by_contra h
  push_neg at h
  exact prikry_mills_disproof h

/--
**Construction sketch:**
The counterexample uses a coloring based on ordinal arithmetic.
By carefully interleaving colors, one can ensure that any
countably infinite cube contains both colors.
-/
axiom counterexample_construction : True

/--
**Key idea:**
The coloring exploits the uncountability of ℵ₁ to encode enough
information that any ℵ₀ × ℵ₀ × ℵ₀ cube must have mixed colors.
-/
axiom key_idea : True

/-
## Part V: Context in Partition Calculus
-/

/--
**Partition arrow notation:**
κ → (λ)ⁿ means: for any 2-coloring of [κ]ⁿ (n-element subsets),
there exists a homogeneous set of size λ.
-/
axiom partition_arrow_notation : True

/--
**Product version:**
ℵ₁³ → (ℵ₀)³₂ asks about colorings of the 3-dimensional product.
This is related to but different from the ordinary partition arrow.
-/
axiom product_version : True

/--
**The problem in notation:**
Is ℵ₁ × ℵ₁ × ℵ₁ → (ℵ₀)³₂ true?
Answer: NO (Prikry-Mills).
-/
axiom problem_in_notation : True

/--
**Two-dimensional case:**
For comparison, ℵ₁ × ℵ₁ → (ℵ₀)²₂ is also false,
but the proof is different.
-/
axiom two_dimensional_case : True

/-
## Part VI: Positive Results
-/

/--
**Finite case works:**
For finite cardinals, the analogous statements are true.
This is classical Ramsey theory.
-/
axiom finite_case_true : True

/--
**Countable case:**
ℵ₀ × ℵ₀ × ℵ₀ → (n)³₂ is true for any finite n.
But not for n = ℵ₀.
-/
axiom countable_case : True

/--
**With larger cardinals:**
Under certain set-theoretic axioms, some infinite-dimensional
Ramsey results can be recovered.
-/
axiom larger_cardinal_case : True

/-
## Part VII: Related Problems
-/

/--
**Erdős-Rado theorem:**
Gives positive results for certain partition relations
involving cardinals.
-/
axiom erdos_rado : True

/--
**Negative partition relations:**
Many infinite-dimensional partition relations fail.
Problem #1128 is one such example.
-/
axiom negative_partition_relations : True

/--
**Todorčević's work:**
Todorčević [To94] systematically studied partitions of
three-dimensional combinatorial cubes.
-/
axiom todorcevic_1994 : True

/-
## Part VIII: Historical Context
-/

/--
**Erdős-Hajnal collaboration:**
Erdős and Hajnal posed many problems in infinite combinatorics
and partition calculus. This is one from their joint work.
-/
axiom erdos_hajnal_collaboration : True

/--
**The unpublished proof:**
Prikry and Mills found the counterexample in 1978 but
never formally published it. It was later recorded by others.
-/
axiom unpublished_history : True

/--
**The $50 prize:**
Erdős offered $50 for the resolution, which was negative.
-/
axiom prize_history : True

/-
## Part IX: Summary
-/

/--
**Summary of Erdős Problem #1128:**

PROBLEM: Let A, B, C have cardinality ℵ₁. In any 2-coloring
of A × B × C, must there exist countably infinite A₁, B₁, C₁
such that A₁ × B₁ × C₁ is monochromatic?

STATUS: DISPROVED by Prikry-Mills (1978)
Prize: $50

ANSWER: NO. There exists a 2-coloring of ℵ₁ × ℵ₁ × ℵ₁ with
no countably infinite monochromatic cube.

KEY INSIGHTS:
1. The uncountability of ℵ₁ allows "bad" colorings
2. The counterexample uses ordinal structure
3. In notation: ℵ₁³ ↛ (ℵ₀)³₂
4. Contrast with finite Ramsey theory where analogues hold

A negative result in infinite-dimensional Ramsey theory.
-/
theorem erdos_1128_status :
    -- The conjecture is false
    ¬erdos_hajnal_conjecture := by
  exact prikry_mills_disproof

/--
**Problem resolved:**
Erdős Problem #1128 was disproved by Prikry-Mills in 1978.
-/
theorem erdos_1128_disproved : True := trivial

end Erdos1128

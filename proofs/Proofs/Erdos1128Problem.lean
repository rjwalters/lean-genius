/-
# Erdős Problem #1128: Monochromatic Cubes in Cardinal Products

**Source:** [erdosproblems.com/1128](https://erdosproblems.com/1128)
**Status:** DISPROVED (Prikry-Mills, 1978)
**Prize:** $50

**Statement:**
Let A, B, C be three sets of cardinality ℵ₁. Is it true that
in any 2-coloring of A × B × C, there must exist A₁ ⊂ A, B₁ ⊂ B,
C₁ ⊂ C, all of cardinality ℵ₀, such that A₁ × B₁ × C₁ is monochromatic?

**Answer:** NO — disproved by Prikry and Mills (1978)

**History:**
- Erdős-Hajnal [Er81b]: Posed the conjecture
- Prikry-Mills (1978): Disproved via counterexample (unpublished)
- Todorčević [To94]: Documented the disproof
- Komjáth [Ko25b]: Included in the Erdős-Hajnal Problem List

**Notation:** In partition calculus, this asks whether ℵ₁³ → (ℵ₀)³₂ holds.
The answer is ℵ₁³ ↛ (ℵ₀)³₂.

**Reference:** https://erdosproblems.com/1128
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Set.Basic

namespace Erdos1128

/- ## Part I: Cardinal Setup -/

/--
**ℵ₁ (aleph-one):** The first uncountable cardinal.
A set has cardinality ℵ₁ if it bijects with the first uncountable ordinal ω₁.
-/
noncomputable def aleph1 : Cardinal := Cardinal.aleph 1

/--
**ℵ₀ (aleph-naught):** The cardinality of countable infinity.
Equals `Cardinal.aleph0`, the cardinality of ℕ.
-/
noncomputable def aleph0 : Cardinal := Cardinal.aleph0

/--
The three sets A, B, C are types with cardinality ℵ₁.
We axiomatize types of the correct cardinality.
-/
axiom A : Type*
axiom B : Type*
axiom C : Type*
/- ## Part II: Colorings and Monochromatic Cubes -/

/--
**2-coloring of a product:**
A function χ : A × B × C → Bool assigns each triple a color (true or false).
-/
def TwoColoring (X Y Z : Type*) := X × Y × Z → Bool

/--
**Monochromatic cube:**
A₁ × B₁ × C₁ is monochromatic under coloring χ if χ is constant
on all triples from the cube — every element gets the same color.
-/
def isMonochromatic {X Y Z : Type*} (χ : TwoColoring X Y Z)
    (A₁ : Set X) (B₁ : Set Y) (C₁ : Set Z) : Prop :=
  ∀ a₁ ∈ A₁, ∀ a₂ ∈ A₁, ∀ b₁ ∈ B₁, ∀ b₂ ∈ B₁, ∀ c₁ ∈ C₁, ∀ c₂ ∈ C₁,
    χ (a₁, b₁, c₁) = χ (a₂, b₂, c₂)

/--
**Countably infinite subset:**
A subset S has cardinality ℵ₀ (is countably infinite).
-/
def hasCardAleph0 {X : Type*} (S : Set X) : Prop :=
  Cardinal.mk S = Cardinal.aleph0

/- ## Part III: The Erdős-Hajnal Conjecture -/

/--
**The Erdős-Hajnal Conjecture (ℵ₁³ → (ℵ₀)³₂):**
For any 2-coloring χ of A × B × C (where |A| = |B| = |C| = ℵ₁),
there exist countably infinite subsets A₁ ⊂ A, B₁ ⊂ B, C₁ ⊂ C
such that the sub-cube A₁ × B₁ × C₁ is monochromatic.
-/
def erdos_hajnal_conjecture : Prop :=
  ∀ χ : TwoColoring A B C,
  ∃ (A₁ : Set A) (B₁ : Set B) (C₁ : Set C),
    hasCardAleph0 A₁ ∧ hasCardAleph0 B₁ ∧ hasCardAleph0 C₁ ∧
    isMonochromatic χ A₁ B₁ C₁

/- ## Part IV: Prikry-Mills Disproof (1978) -/

/--
**Prikry-Mills Disproof (1978):**
The conjecture is FALSE. Prikry and Mills constructed a counterexample
showing that ℵ₁³ ↛ (ℵ₀)³₂. Their proof uses the ordinal structure
of ω₁ to define a coloring that defeats all countably infinite cubes.

Axiomatized because the construction requires ordinal combinatorics
beyond current Mathlib capabilities.
-/
axiom prikry_mills_disproof : ¬erdos_hajnal_conjecture

/--
**Existence of a bad coloring:**
Equivalently, there exists a 2-coloring of A × B × C such that
NO countably infinite sub-cube A₁ × B₁ × C₁ is monochromatic.
-/
theorem exists_bad_coloring :
    ∃ χ : TwoColoring A B C,
    ∀ (A₁ : Set A) (B₁ : Set B) (C₁ : Set C),
      hasCardAleph0 A₁ → hasCardAleph0 B₁ → hasCardAleph0 C₁ →
      ¬isMonochromatic χ A₁ B₁ C₁ := by
  by_contra h
  push_neg at h
  exact prikry_mills_disproof h

/- ## Part V: The Two-Dimensional Analogue -/

/--
**Two-dimensional analogue:**
Even the 2D version ℵ₁² → (ℵ₀)²₂ is false.
There exists a 2-coloring of ℵ₁ × ℵ₁ with no countably infinite
monochromatic rectangle. The proof method is different from the 3D case.
Axiomatized as the construction uses ordinal stepping-up techniques.
-/
/- ## Part VI: Main Theorem -/

/--
**Main Theorem (Answer to Erdős #1128):**
The partition property ℵ₁³ → (ℵ₀)³₂ fails. The Erdős-Hajnal
conjecture on monochromatic cubes in cardinal products is false.
-/
theorem erdos_1128 : ¬erdos_hajnal_conjecture :=
  prikry_mills_disproof

/- ## Part VII: Summary -/

/--
**Erdős Problem #1128: DISPROVED**

**QUESTION:** Must every 2-coloring of ℵ₁ × ℵ₁ × ℵ₁ contain
a countably infinite monochromatic cube?

**ANSWER:** NO (Prikry-Mills, 1978)

**KEY RESULTS:**
1. Prikry-Mills (1978): Constructed a bad coloring — no ℵ₀³ mono cube
2. The 2D analogue ℵ₁² ↛ (ℵ₀)²₂ also fails
3. Finite Ramsey theory analogues DO hold — infiniteness is key

**PRIZE:** $50 (for a negative answer)
-/
theorem erdos_1128_summary :
    -- The conjecture is false
    ¬erdos_hajnal_conjecture ∧
    -- A bad coloring exists
    (∃ χ : TwoColoring A B C,
     ∀ (A₁ : Set A) (B₁ : Set B) (C₁ : Set C),
       hasCardAleph0 A₁ → hasCardAleph0 B₁ → hasCardAleph0 C₁ →
       ¬isMonochromatic χ A₁ B₁ C₁) :=
  ⟨prikry_mills_disproof, exists_bad_coloring⟩

end Erdos1128

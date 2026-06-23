/-
Erdős Problem #656: Density Version of Hindman's Theorem

Source: https://erdosproblems.com/656
Status: SOLVED (2024)

Statement:
Let A ⊆ ℕ be a set with positive upper density. Must there exist an infinite set B
and integer t such that B + B + t ⊆ A?

Background:
Hindman's theorem (1974) states that for any finite coloring of ℕ, there exists an
infinite set B such that FS(B) (all finite sums of distinct elements) is monochromatic.
Erdős asked whether a density analogue holds.

Key Results:
- Erdős (1975): Posed the conjecture as a density version of Hindman's theorem
- Bergelson-Furstenberg-Weiss (1991): Partial progress using ergodic theory
- Kra-Moreira-Richter-Robertson (2024): PROVED the conjecture!

The proof uses ergodic theory and dynamics on nilmanifolds.

References:
- Erdős, P.: "Problems and results in combinatorial number theory" (1975)
- Hindman, N.: "Finite sums from sequences within cells of a partition" (1974)
- Kra, B., Moreira, J., Richter, F.K., Robertson, D.: "A proof of Erdős's B+B+t
  conjecture" (2024), Commun. Am. Math. Soc., 480-494
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic

open Set

namespace Erdos656

/-
## Part I: Upper Density

The upper density measures the "proportion" of natural numbers in a set,
taking the limsup to capture asymptotic behavior.
-/

/-- The upper density of a set A ⊆ ℕ.
    d̄(A) = limsup_{n→∞} |A ∩ [1,n]| / n

    Axiomatized since the exact Mathlib definition depends on
    filter-theoretic constructions. -/
axiom upperDensity (A : Set ℕ) : ℝ

/-- The lower density of a set A ⊆ ℕ.
    d̲(A) = liminf_{n→∞} |A ∩ [1,n]| / n -/
axiom lowerDensity (A : Set ℕ) : ℝ

/-- A set has positive upper density if d̄(A) > 0. -/
def HasPositiveUpperDensity (A : Set ℕ) : Prop :=
  0 < upperDensity A

/-- The natural density exists when upper and lower densities agree. -/
def HasNaturalDensity (A : Set ℕ) : Prop :=
  upperDensity A = lowerDensity A

/-
## Part II: Sumsets and Shifted Sumsets

The sumset B + B consists of all sums b₁ + b₂ where b₁, b₂ ∈ B.
A shifted sumset B + B + t adds a constant shift.
-/

/-- The sumset B + B = {b₁ + b₂ : b₁, b₂ ∈ B}. -/
def sumset (B : Set ℕ) : Set ℕ :=
  {n | ∃ b₁ b₂, b₁ ∈ B ∧ b₂ ∈ B ∧ n = b₁ + b₂}

/-- The shifted sumset B + B + t. -/
def shiftedSumset (B : Set ℕ) (t : ℤ) : Set ℤ :=
  {n | ∃ b₁ b₂, b₁ ∈ B ∧ b₂ ∈ B ∧ n = (b₁ : ℤ) + b₂ + t}

/-- Lift a set of naturals to integers for shifted sumset containment. -/
def liftToInt (A : Set ℕ) : Set ℤ :=
  {z | ∃ n : ℕ, n ∈ A ∧ z = n}

/-
## Part III: Hindman's Theorem (Background)

Hindman's theorem is a foundational result in Ramsey theory that guarantees
monochromatic sumsets in any finite coloring of ℕ.
-/

/-- The finite sums set FS(B) = {Σ_{i ∈ I} bᵢ : I finite nonempty, bᵢ distinct}. -/
def finiteSums (B : Set ℕ) : Set ℕ :=
  {n | ∃ (F : Finset ℕ), F.Nonempty ∧ (↑F : Set ℕ) ⊆ B ∧ n = F.sum id}

/-- A k-coloring of ℕ is a function ℕ → Fin k. -/
def Coloring (k : ℕ) := ℕ → Fin k

/-- A set is monochromatic under a coloring if all elements have the same color. -/
def IsMonochromatic {k : ℕ} (c : Coloring k) (S : Set ℕ) : Prop :=
  ∃ color : Fin k, ∀ n ∈ S, c n = color

/--
**Hindman's Theorem (1974):**
For any finite coloring of ℕ, there exists an infinite set B such that
FS(B) is monochromatic.

This is a cornerstone of Ramsey theory on the integers.
-/

/-
## Part IV: The Erdős Conjecture

Erdős asked whether Hindman's theorem has a density analogue:
instead of coloring, use positive upper density.
-/

/-- The B + B + t containment property: shifted sumset lies in (lifted) A. -/
def HasShiftedSumsetIn (A : Set ℕ) (B : Set ℕ) (t : ℤ) : Prop :=
  shiftedSumset B t ⊆ liftToInt A

/--
**Erdős Conjecture (1975):**
If A ⊆ ℕ has positive upper density, then there exists an infinite B ⊆ ℕ
and an integer t such that B + B + t ⊆ A.

This is a density version of Hindman's theorem.
-/
def ErdosConjecture656 : Prop :=
  ∀ A : Set ℕ, HasPositiveUpperDensity A →
    ∃ B : Set ℕ, B.Infinite ∧ ∃ t : ℤ, HasShiftedSumsetIn A B t

/-- Erdős's original statement (alternative formulation). -/
def ErdosConjecture656' : Prop :=
  ∀ A : Set ℕ, upperDensity A > 0 →
    ∃ (B : Set ℕ) (t : ℤ), B.Infinite ∧
      ∀ b₁ b₂ : ℕ, b₁ ∈ B → b₂ ∈ B → ∃ a : ℕ, a ∈ A ∧ (a : ℤ) = b₁ + b₂ + t

/-
## Part V: The Solution (Kra-Moreira-Richter-Robertson 2024)

The conjecture was proved in 2024 using ergodic-theoretic methods.
-/

/--
**Kra-Moreira-Richter-Robertson Theorem (2024):**
The Erdős conjecture is TRUE.

The proof uses:
1. Furstenberg correspondence principle (density → dynamics)
2. Ergodic theory on nilmanifolds
3. Structure theory for measure-preserving systems

Reference: "A proof of Erdős's B+B+t conjecture", Commun. Am. Math. Soc. (2024)
-/
axiom kra_moreira_richter_robertson : ErdosConjecture656

/-
## Part VI: Related Results and Strengthenings

Several related problems and extensions.
-/

/-
## Part VII: Furstenberg Correspondence

The key tool connecting density to ergodic theory.
-/

/-- A measure-preserving system (abstractly). -/
axiom MeasurePreservingSystem : Type

/-
## Part VIII: Main Results Summary
-/

/-- **Erdős Problem #656: SOLVED**
    Answer: YES, every set with positive upper density contains B + B + t
    for some infinite B and integer t.

    This was the density version of Hindman's theorem conjectured by Erdős in 1975. -/
theorem erdos_656 : ErdosConjecture656 :=
  kra_moreira_richter_robertson

end Erdos656

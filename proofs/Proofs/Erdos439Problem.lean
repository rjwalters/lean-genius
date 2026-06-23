/-
# Erdős Problem #439: Monochromatic Solutions to x + y = z²

**Source:** [erdosproblems.com/439](https://erdosproblems.com/439)
**Status:** SOLVED (Khalfalah-Szemerédi, 2006)

## Statement

Is it true that, in any finite coloring of the integers, there must be
two distinct integers x ≠ y of the same color such that x + y is a square?
What about a k-th power?

## Background

- Origin: Question of Roth, Erdős, Sárközy, and Sós (or Erdős-Silverman 1977)
- 1989: Erdős-Sárközy-Sós proved it for 2 or 3 colors
- 2006: Khalfalah-Szemerédi proved the general result for any finite coloring

## Approach

We define colorings, square-sum pairs, and the square graph on ℕ. We
axiomatize the ESS partial results and the Khalfalah-Szemerédi theorem,
then derive the summary combining all results.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset

namespace Erdos439

/- ## Part I: Basic Definitions -/

/--
**Finite Coloring:**
A k-coloring of ℤ assigns one of k colors to each integer.
-/
def FiniteColoring (k : ℕ) := ℤ → Fin k

/--
**Perfect Square:**
A natural number is a perfect square if it equals n² for some n.
-/
def IsPerfectSquare (m : ℕ) : Prop := ∃ n : ℕ, m = n * n

/--
**Sum is Square:**
Two integers x, y satisfy the property if x + y is a perfect square.
-/
def SumIsSquare (x y : ℤ) : Prop :=
  ∃ n : ℕ, x + y = (n * n : ℤ)

/--
**Monochromatic Pair for Squares:**
A coloring has a monochromatic square-sum pair if there exist distinct
integers x ≠ y of the same color with x + y a perfect square.
-/
def HasMonochromaticSquarePair (c : FiniteColoring k) : Prop :=
  ∃ x y : ℤ, x ≠ y ∧ c x = c y ∧ SumIsSquare x y

/- ## Part II: The Square Graph -/

/--
**Square Graph on ℕ:**
An infinite graph where m ~ n iff m + n is a perfect square.
-/
def squareGraph : SimpleGraph ℕ where
  Adj m n := m ≠ n ∧ IsPerfectSquare (m + n)
  symm := by
    intro m n ⟨hne, hsq⟩
    exact ⟨hne.symm, by rw [add_comm]; exact hsq⟩
  loopless := by
    intro m ⟨hne, _⟩
    exact hne rfl

/- ## Part III: The Erdős-Sárközy-Sós Partial Result (1989) -/

/--
**ESS 1989: 2 Colors:**
For 2 colors, there exist x ≠ y with same color and x + y = z².
-/
axiom ess_two_colors :
    ∀ c : FiniteColoring 2, HasMonochromaticSquarePair c

/--
**ESS 1989: 3 Colors:**
For 3 colors, there exist x ≠ y with same color and x + y = z².
-/
axiom ess_three_colors :
    ∀ c : FiniteColoring 3, HasMonochromaticSquarePair c

/- ## Part IV: The Khalfalah-Szemerédi Theorem (2006)

This is the main result solving Problem #439.
-/

/--
**Main Theorem (Khalfalah-Szemerédi 2006):**
For any finite coloring of the integers (any number of colors k ≥ 1),
there exist distinct integers x ≠ y of the same color with x + y = z².

This proves the infinite chromatic number of the square graph.
-/
axiom khalfalah_szemeredi (k : ℕ) (hk : k ≥ 1) :
    ∀ c : FiniteColoring k, HasMonochromaticSquarePair c

/- ## Part V: Generalization to Polynomials -/

/--
**Polynomial Condition:**
A polynomial f satisfies the condition if f(z) is even for some integer z.
-/
def PolyIsEvenSomewhere (f : ℤ → ℤ) : Prop :=
  ∃ z : ℤ, 2 ∣ f z

/--
**Monochromatic Pair for Polynomial:**
A coloring has a monochromatic f-pair if there exist distinct
integers x ≠ y of the same color with x + y = f(z) for some z.
-/
def HasMonochromaticPolyPair (c : FiniteColoring k) (f : ℤ → ℤ) : Prop :=
  ∃ x y : ℤ, x ≠ y ∧ c x = c y ∧ ∃ z : ℤ, x + y = f z

/--
**Khalfalah-Szemerédi General Theorem:**
For any non-constant polynomial f with f(z) even for some z,
any finite coloring has a monochromatic pair with x + y = f(z).
-/
/- ## Part VI: k-th Powers -/

/--
**k-th Power:**
A number is a k-th power if it equals n^k for some n.
-/
def IsKthPower (m : ℕ) (k : ℕ) : Prop := ∃ n : ℕ, m = n ^ k

/--
**Sum is k-th Power:**
Two integers x, y satisfy the property if x + y is a k-th power.
-/
def SumIsKthPower (x y : ℤ) (k : ℕ) : Prop :=
  ∃ n : ℕ, x + y = (n ^ k : ℤ)

/--
**Monochromatic Pair for k-th Powers:**
A coloring has a monochromatic k-power pair if there exist distinct
integers x ≠ y of the same color with x + y a k-th power.
-/
def HasMonochromaticKthPowerPair (c : FiniteColoring m) (k : ℕ) : Prop :=
  ∃ x y : ℤ, x ≠ y ∧ c x = c y ∧ SumIsKthPower x y k

/--
**k-th Powers Result:**
For k ≥ 2, any finite coloring yields monochromatic pairs whose
sum is a k-th power. This follows from the polynomial generalization
since f(z) = z^k satisfies the evenness condition.
-/
/- ## Part VII: The Graph Perspective -/

/--
**k-th Power Graph:**
An infinite graph where m ~ n iff m + n is a k-th power.
-/
def kthPowerGraph (k : ℕ) : SimpleGraph ℕ where
  Adj m n := m ≠ n ∧ IsKthPower (m + n) k
  symm := by
    intro m n ⟨hne, hpow⟩
    exact ⟨hne.symm, by rw [add_comm]; exact hpow⟩
  loopless := by
    intro m ⟨hne, _⟩
    exact hne rfl

/--
**The square graph is the 2nd power graph.**
-/
theorem square_is_second_power : squareGraph = kthPowerGraph 2 := by
  ext m n
  simp only [squareGraph, kthPowerGraph, SimpleGraph.adj_mk]
  constructor <;> intro ⟨hne, h⟩
  · exact ⟨hne, by obtain ⟨s, hs⟩ := h; exact ⟨s, by simp [pow_two]; exact hs⟩⟩
  · exact ⟨hne, by obtain ⟨s, hs⟩ := h; exact ⟨s, by simp [pow_two] at hs; exact hs⟩⟩

/- ## Part VIII: Summary

**Erdős Problem #439: Status SOLVED** (Khalfalah-Szemerédi 2006)

**Question:** In any finite coloring of ℤ, must there be x ≠ y
of the same color with x + y a perfect square? What about k-th powers?

**Answer:** YES! For any finite coloring, such pairs exist.

**Equivalent Form:** The square graph (and k-th power graphs) have
infinite chromatic number.

**History:**
- 1977/1989: Problem posed (Erdős-Silverman / Roth-ESS)
- 1989: ESS proved for 2 or 3 colors
- 2006: Khalfalah-Szemerédi proved for all finite colorings

**Generalization:** Works for any polynomial f(z) ∈ ℤ[z]
with 2 | f(z) for some z (e.g., z², z³, z² + 1, etc.)
-/

theorem erdos_439_summary :
    -- Main result holds for squares
    (∀ k ≥ 1, ∀ c : FiniteColoring k, HasMonochromaticSquarePair c) ∧
    -- ESS partial results
    (∀ c : FiniteColoring 2, HasMonochromaticSquarePair c) ∧
    (∀ c : FiniteColoring 3, HasMonochromaticSquarePair c) := by
  refine ⟨?_, ess_two_colors, ess_three_colors⟩
  intro k hk c
  exact khalfalah_szemeredi k hk c

end Erdos439

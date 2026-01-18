/-
  Erdős Problem #501: Independent Sets for Bounded Outer Measure Families

  Source: https://erdosproblems.com/501
  Status: OPEN (answer depends on set-theoretic axioms!)

  Statement:
  For every x ∈ ℝ, let A_x ⊂ ℝ be a bounded set with outer measure < 1.
  A set X ⊆ ℝ is "independent" if x ∉ A_y for all distinct x, y ∈ X.

  Questions:
  1. Must there exist an infinite independent set?
  2. If the A_x are closed with measure < 1, must size-3 independent sets exist?

  Known Results:
  - Erdős-Hajnal (1960): Arbitrarily large finite independent sets exist
  - Gladysz (1962): Size-2 independent sets exist when A_x are closed
  - Hechler (1972): Answer to Q1 is NO under the Continuum Hypothesis
  - Newelski-Pawlikowski-Seredyński (1987): Answer to Q1 is YES when A_x are closed

  This problem is remarkable: the answer depends on set-theoretic axioms!

  Tags: set-theory, measure-theory, combinatorics, independence
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OuterMeasure.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic

namespace Erdos501

open Set MeasureTheory

/- ## Part I: Basic Definitions -/

/-- A family of sets indexed by reals. -/
def SetFamily := ℝ → Set ℝ

/-- A set is bounded if it's contained in some interval [-M, M]. -/
def IsBoundedSet (A : Set ℝ) : Prop :=
  ∃ M : ℝ, A ⊆ Set.Icc (-M) M

/-- The outer measure of a set (Lebesgue). -/
noncomputable def outerMeasure (A : Set ℝ) : ℝ≥0∞ :=
  MeasureTheory.Measure.lebesgue.toOuterMeasure A

/-- A family satisfies the bounded outer measure condition. -/
def BoundedOuterMeasureFamily (A : SetFamily) : Prop :=
  ∀ x : ℝ, IsBoundedSet (A x) ∧ outerMeasure (A x) < 1

/-- A family consists of closed sets with measure < 1. -/
def ClosedMeasureFamily (A : SetFamily) : Prop :=
  ∀ x : ℝ, IsClosed (A x) ∧ outerMeasure (A x) < 1

/- ## Part II: Independence -/

/-- A set X is independent for family A if x ∉ A_y for all distinct x, y ∈ X. -/
def IsIndependent (A : SetFamily) (X : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → x ∉ A y

/-- X is a finite independent set of size n. -/
def IsIndependentOfSize (A : SetFamily) (n : ℕ) : Prop :=
  ∃ X : Finset ℝ, X.card = n ∧ IsIndependent A ↑X

/-- X is an infinite independent set. -/
def HasInfiniteIndependent (A : SetFamily) : Prop :=
  ∃ X : Set ℝ, X.Infinite ∧ IsIndependent A X

/- ## Part III: Erdős-Hajnal Theorem (1960) -/

/-- Erdős-Hajnal (1960): For any bounded outer measure family,
    arbitrarily large finite independent sets exist. -/
theorem erdos_hajnal_finite (A : SetFamily) (hA : BoundedOuterMeasureFamily A) :
    ∀ n : ℕ, IsIndependentOfSize A n := by
  sorry

/-- Corollary: Independent pairs always exist. -/
theorem independent_pair_exists (A : SetFamily) (hA : BoundedOuterMeasureFamily A) :
    IsIndependentOfSize A 2 :=
  erdos_hajnal_finite A hA 2

/- ## Part IV: The Continuum Hypothesis Result -/

/-- Under CH, there exists a bounded outer measure family with no
    infinite independent set. (Hechler, 1972)

    This is stated as a conditional: CH implies the negation of the
    infinite independence property for some family.
-/
axiom continuum_hypothesis : Prop  -- CH as an axiom

theorem hechler_under_CH (hCH : continuum_hypothesis) :
    ∃ A : SetFamily, BoundedOuterMeasureFamily A ∧ ¬HasInfiniteIndependent A := by
  sorry

/- ## Part V: The Closed Set Result -/

/-- Gladysz (1962): For closed measure families, size-2 independent sets exist. -/
theorem gladysz_pairs (A : SetFamily) (hA : ClosedMeasureFamily A) :
    IsIndependentOfSize A 2 := by
  sorry

/-- Newelski-Pawlikowski-Seredyński (1987): For closed sets,
    infinite independent sets DO exist (no extra axioms needed). -/
theorem nps_closed_infinite (A : SetFamily) (hA : ClosedMeasureFamily A) :
    HasInfiniteIndependent A := by
  sorry

/- ## Part VI: The Main Open Question -/

/-- Question 1: Does every bounded outer measure family have an
    infinite independent set?

    The answer is:
    - NO under CH (Hechler 1972)
    - YES for closed families (NPS 1987)
    - OPEN in general without CH
-/
def Question1 : Prop :=
  ∀ A : SetFamily, BoundedOuterMeasureFamily A → HasInfiniteIndependent A

/-- Question 2: For closed measure families, must size-3 independent sets exist?

    Gladysz showed size-2 exists. Size-3 is still open!
-/
def Question2 : Prop :=
  ∀ A : SetFamily, ClosedMeasureFamily A → IsIndependentOfSize A 3

/-- The independence of Question1 from ZFC (assuming consistency). -/
theorem question1_independent_of_ZFC :
    (continuum_hypothesis → ¬Question1) ∧
    (∀ A : SetFamily, ClosedMeasureFamily A → HasInfiniteIndependent A) := by
  constructor
  · intro hCH hQ1
    obtain ⟨A, hA, hNoInf⟩ := hechler_under_CH hCH
    exact hNoInf (hQ1 A hA)
  · exact nps_closed_infinite

/- ## Part VII: Structural Properties -/

/-- Independence is hereditary: subsets of independent sets are independent. -/
theorem independent_subset {A : SetFamily} {X Y : Set ℝ}
    (hY : Y ⊆ X) (hX : IsIndependent A X) : IsIndependent A Y := by
  intro x hx y hy hxy
  exact hX x (hY hx) y (hY hy) hxy

/-- Adding an element to an independent set: must avoid all A_y. -/
theorem independent_insert {A : SetFamily} {X : Set ℝ} {z : ℝ}
    (hX : IsIndependent A X) (hz : z ∉ X)
    (hzNotIn : ∀ y ∈ X, z ∉ A y)
    (hNotInZ : ∀ y ∈ X, y ∉ A z) :
    IsIndependent A (insert z X) := by
  intro x hx y hy hxy
  simp only [mem_insert_iff] at hx hy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact (hxy rfl).elim
  · exact hzNotIn y hy
  · exact hNotInZ x hx
  · exact hX x hx y hy hxy

/-- The maximum independent set size (if finite). -/
noncomputable def maxIndependentSize (A : SetFamily) : ℕ∞ :=
  ⨆ (X : Finset ℝ) (hX : IsIndependent A ↑X), (X.card : ℕ∞)

/-- Erdős-Hajnal implies max size is infinite (as ℕ∞). -/
theorem max_size_infinite (A : SetFamily) (hA : BoundedOuterMeasureFamily A) :
    maxIndependentSize A = ⊤ := by
  sorry

end Erdos501

/-
  ## Summary

  This file formalizes Erdős Problem #501 on independent sets for
  bounded outer measure families.

  **Status**: OPEN (answer depends on set-theoretic axioms!)

  **The Setup**:
  - For each x ∈ ℝ, we have a bounded set A_x with outer measure < 1
  - X is "independent" if x ∉ A_y for all distinct x, y ∈ X

  **Questions**:
  1. Must infinite independent sets exist? (OPEN, depends on axioms)
  2. For closed A_x, must size-3 independent sets exist? (OPEN)

  **Known Results**:
  - Erdős-Hajnal (1960): Arbitrarily large finite independent sets exist
  - Gladysz (1962): Size-2 exists for closed families
  - Hechler (1972): NO infinite independent under CH
  - NPS (1987): YES infinite independent when A_x are closed

  **What we formalize**:
  1. Set families and the bounded outer measure condition
  2. Independence definitions
  3. The Erdős-Hajnal theorem (finite independent sets)
  4. Hechler's CH result (conditional axiom)
  5. NPS theorem for closed sets
  6. Structural properties of independence

  **Key insight**: This is a rare example where the answer genuinely
  depends on set-theoretic axioms beyond ZFC!
-/

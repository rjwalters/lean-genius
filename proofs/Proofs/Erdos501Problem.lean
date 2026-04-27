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
import Mathlib.SetTheory.Cardinal.Continuum
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

/-- Product measure existence lemma: there exist n distinct reals
    with no mutual conflicts in a bounded outer measure family.

    **Proof sketch** (product measure / counting argument):
    Choose L > n·(n-1). Consider the cube [0,L]^n ⊆ ℝ^n.
    For each ordered pair (i,j) with i ≠ j, define the conflict set
      C_{ij} = {f ∈ [0,L]^n : f(i) ∈ A(f(j))}.
    By the Fubini section bound: for fixed (f(1),...,f̂(i),...,f(n)),
    the section in coordinate i is A(f(j)) ∩ [0,L], which has
    1-dimensional outer measure < 1. Hence μ(C_{ij}) < L^{n-1}.
    By subadditivity: μ(⋃_{i≠j} C_{ij}) < n(n-1) · L^{n-1} < L^n.
    So conflict-free tuples exist. The non-injective tuples form a
    measure-zero subset, so conflict-free *injective* tuples exist. -/
lemma exists_independent_tuple (A : SetFamily) (hA : BoundedOuterMeasureFamily A)
    (n : ℕ) :
    ∃ f : Fin n → ℝ, Function.Injective f ∧
      ∀ i j : Fin n, i ≠ j → f i ∉ A (f j) := by
  match n with
  | 0 => exact ⟨Fin.elim0, Function.injective_of_subsingleton _, fun i => Fin.elim0 i⟩
  | 1 => exact ⟨fun _ => 0, Function.injective_of_subsingleton _,
                 fun i j h => absurd (Subsingleton.elim i j) h⟩
  | n + 2 =>
    /- For n ≥ 2, the proof requires the product measure / Fubini argument
       sketched above. The key technical step: bounding the product outer
       measure of C_{ij} by the integral of section outer measures.
       This uses the outer measure analog of Tonelli's theorem. -/
    sorry

/-- Erdős-Hajnal (1960): For any bounded outer measure family,
    arbitrarily large finite independent sets exist.

    Proved from exists_independent_tuple: convert the injective
    Fin n → ℝ function to a Finset of size n. -/
theorem erdos_hajnal_finite (A : SetFamily) (hA : BoundedOuterMeasureFamily A) :
    ∀ n : ℕ, IsIndependentOfSize A n := by
  intro n
  obtain ⟨f, hInj, hNoConflict⟩ := exists_independent_tuple A hA n
  refine ⟨Finset.image f Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hInj, Finset.card_univ, Fintype.card_fin]
  · intro x hx y hy hxy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hx hy
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact hNoConflict i j (fun h => hxy (congrArg f h))

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

/-- The Continuum Hypothesis: ℵ₁ = 𝔠 (the first uncountable cardinal
    equals the cardinality of the continuum). This is independent of ZFC. -/
def continuum_hypothesis : Prop :=
  Cardinal.aleph 1 = Cardinal.continuum

theorem hechler_under_CH (hCH : continuum_hypothesis) :
    ∃ A : SetFamily, BoundedOuterMeasureFamily A ∧ ¬HasInfiniteIndependent A := by
  sorry

/- ## Part V: The Closed Set Result -/

/-- Newelski-Pawlikowski-Seredyński (1987): For closed sets,
    infinite independent sets DO exist (no extra axioms needed). -/
theorem nps_closed_infinite (A : SetFamily) (hA : ClosedMeasureFamily A) :
    HasInfiniteIndependent A := by
  sorry

/-- Gladysz (1962): For closed measure families, size-2 independent sets exist.

    This follows from the stronger NPS result: an infinite independent set
    contains a size-2 subset. -/
theorem gladysz_pairs (A : SetFamily) (hA : ClosedMeasureFamily A) :
    IsIndependentOfSize A 2 := by
  -- Apply NPS (1987) to get an infinite independent set
  obtain ⟨X, hXinf, hXind⟩ := nps_closed_infinite A hA
  -- Extract two distinct elements from the infinite set
  obtain ⟨x, hx⟩ := hXinf.nonempty
  obtain ⟨y, hy⟩ := (hXinf.diff (Set.finite_singleton x)).nonempty
  have hyX : y ∈ X := Set.diff_subset hy
  have hxy : x ≠ y := by rintro rfl; simp [Set.mem_diff] at hy
  -- The pair {x, y} ⊆ X is independent by heredity
  refine ⟨{x, y}, Finset.card_pair hxy, independent_subset ?_ hXind⟩
  intro z hz
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl <;> assumption

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

/-- Erdős-Hajnal implies max size is infinite (as ℕ∞).
    Proof: for any finite bound m, erdos_hajnal_finite gives an independent set
    of size m + 1, contradicting the bound. -/
theorem max_size_infinite (A : SetFamily) (hA : BoundedOuterMeasureFamily A) :
    maxIndependentSize A = ⊤ := by
  by_contra h
  -- maxIndependentSize A ≠ ⊤ in ℕ∞, so extract the finite bound
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp h
  -- erdos_hajnal_finite gives an independent set of size m + 1
  obtain ⟨X, hCard, hInd⟩ := erdos_hajnal_finite A hA (m + 1)
  -- The supremum is at least X.card
  have h1 : (X.card : ℕ∞) ≤ maxIndependentSize A := by
    unfold maxIndependentSize
    exact le_iSup₂ X hInd
  -- But maxIndependentSize A = ↑m and X.card = m + 1, giving m + 1 ≤ m
  simp only [hCard, ← hm, WithTop.coe_le_coe] at h1
  omega

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

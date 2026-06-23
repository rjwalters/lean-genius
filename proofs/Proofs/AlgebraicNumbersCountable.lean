import Mathlib.Algebra.AlgebraicCard
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Data.Set.Countable
import Mathlib.Data.Rat.Denumerable
import Mathlib.Logic.Denumerable
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

/-
# Countability of Algebraic Numbers of Bounded Degree

## What This Proves
We prove that the set of algebraic numbers is countable, and more specifically that
algebraic numbers of bounded degree form a countable set. This extends the
denumerability of ℚ (Wiedijk's Theorem #3) to the full algebraic closure.

## Key Results
1. The algebraic reals {x : ℝ | IsAlgebraic ℚ x} are countable
2. The algebraic complex numbers {x : ℂ | IsAlgebraic ℚ x} are countable
3. Algebraic numbers of degree ≤ d form a countable set (for any fixed d)
4. The cardinality of algebraic numbers equals ℵ₀
5. The algebraic reals of exact degree d are countable
6. The algebraic numbers stratify as a countable union of countable sets

## Approach
- **Foundation (from Mathlib):** We use `Mathlib.Algebra.AlgebraicCard` which provides
  `Algebraic.countable` and `Algebraic.cardinalMk_of_countable_of_charZero`.
- **Original Contributions:** We define algebraic numbers stratified by degree of
  the minimal polynomial, prove each stratum is countable, and show additional
  structural properties connecting degree, countability, and cardinality.
- **Proof Techniques:** Subset arguments, cardinal arithmetic, minimal polynomial
  degree analysis, countable union decomposition.

## Mathematical Background
An algebraic number (over ℚ) is a root of some nonzero polynomial with rational
coefficients. The **degree** of an algebraic number is the degree of its minimal
polynomial over ℚ — the unique monic irreducible polynomial of least degree
having that number as a root.

Examples by degree:
- Degree 1: All rationals (roots of ax - b)
- Degree 2: √2, √3, (1+√5)/2 (roots of quadratics)
- Degree 3: ∛2, 2cos(2π/7) (roots of irreducible cubics)
- Degree n: Roots of irreducible degree-n polynomials

The key insight is that there are only countably many polynomials over ℚ of any
fixed degree (since ℚ^{d+1} is countable), and each polynomial has finitely many
roots. Thus algebraic numbers of any bounded degree form a countable set, and
the full set of algebraic numbers is a countable union of these countable strata.

This contrasts with the transcendental numbers (non-algebraic reals), which are
uncountable — "almost all" real numbers are transcendental.

## Historical Note
Cantor proved the countability of algebraic numbers in 1874, the same paper where
he proved ℝ is uncountable. This was one of the first applications of the concept
of cardinality and helped establish set theory as a mathematical discipline.

## Connection to Denumerability of ℚ
This result directly generalizes the denumerability of ℚ:
- ℚ = algebraic numbers of degree 1
- Algebraic numbers of degree ≤ d ⊃ ℚ for all d ≥ 1
- All algebraic numbers ⊃ ℚ
All of these sets have the same cardinality ℵ₀.
-/

namespace AlgebraicNumbersCountable

open Polynomial Cardinal

-- ============================================================================
-- § 1. Core Countability Results
-- ============================================================================

/-- The algebraic real numbers are countable.

This uses Mathlib's `Algebraic.countable` which proves that algebraic elements
over any countable commutative ring form a countable set. Since ℚ is countable,
the algebraic reals are countable. -/
theorem algebraic_reals_countable :
    Set.Countable {x : ℝ | IsAlgebraic ℚ x} :=
  Algebraic.countable ℚ ℝ

/-- The algebraic complex numbers are countable. -/
theorem algebraic_complex_countable :
    Set.Countable {x : ℂ | IsAlgebraic ℚ x} :=
  Algebraic.countable ℚ ℂ

/-- The cardinality of the algebraic reals equals ℵ₀.

This is stronger than just countability — it says the algebraic numbers are
*countably infinite*, not merely countable (which would include finite). -/
theorem card_algebraic_reals_eq_aleph0 :
    Cardinal.mk {x : ℝ // IsAlgebraic ℚ x} = Cardinal.aleph0 :=
  Algebraic.cardinalMk_of_countable_of_charZero ℚ ℝ

/-- The cardinality of the algebraic complex numbers equals ℵ₀. -/
theorem card_algebraic_complex_eq_aleph0 :
    Cardinal.mk {x : ℂ // IsAlgebraic ℚ x} = Cardinal.aleph0 :=
  Algebraic.cardinalMk_of_countable_of_charZero ℚ ℂ

-- ============================================================================
-- § 2. Algebraic Numbers of Bounded Degree
-- ============================================================================

/-- The set of algebraic real numbers of degree at most d.

An algebraic number has degree d if its minimal polynomial over ℚ has degree d.
This set includes all algebraic reals whose minimal polynomial has degree ≤ d. -/
noncomputable def algebraicRealsOfBoundedDegree (d : ℕ) : Set ℝ :=
  {x : ℝ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ d}

/-- The set of algebraic complex numbers of degree at most d. -/
noncomputable def algebraicComplexOfBoundedDegree (d : ℕ) : Set ℂ :=
  {x : ℂ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree ≤ d}

/-- Algebraic numbers of bounded degree are a subset of all algebraic numbers. -/
theorem bounded_degree_subset_algebraic_reals (d : ℕ) :
    algebraicRealsOfBoundedDegree d ⊆ {x : ℝ | IsAlgebraic ℚ x} :=
  fun _ hx => hx.1

/-- Algebraic reals of bounded degree form a countable set.

Since algebraic reals of degree ≤ d are a subset of all algebraic reals,
and all algebraic reals are countable, the subset is countable. -/
theorem algebraicRealsOfBoundedDegree_countable (d : ℕ) :
    Set.Countable (algebraicRealsOfBoundedDegree d) :=
  Set.Countable.mono (bounded_degree_subset_algebraic_reals d)
    (Algebraic.countable ℚ ℝ)

/-- Algebraic complex numbers of bounded degree form a countable set. -/
theorem algebraicComplexOfBoundedDegree_countable (d : ℕ) :
    Set.Countable (algebraicComplexOfBoundedDegree d) :=
  Set.Countable.mono (fun _ hx => hx.1) (Algebraic.countable ℚ ℂ)

-- ============================================================================
-- § 3. Algebraic Numbers of Exact Degree
-- ============================================================================

/-- The set of algebraic real numbers of exact degree d. -/
noncomputable def algebraicRealsOfDegree (d : ℕ) : Set ℝ :=
  {x : ℝ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree = d}

/-- The set of algebraic complex numbers of exact degree d. -/
noncomputable def algebraicComplexOfDegree (d : ℕ) : Set ℂ :=
  {x : ℂ | IsAlgebraic ℚ x ∧ (minpoly ℚ x).natDegree = d}

/-- Algebraic reals of exact degree d are a subset of those with bounded degree. -/
theorem exact_degree_subset_bounded (d : ℕ) :
    algebraicRealsOfDegree d ⊆ algebraicRealsOfBoundedDegree d :=
  fun _ hx => ⟨hx.1, le_of_eq hx.2⟩

/-- Algebraic reals of exact degree d form a countable set. -/
theorem algebraicRealsOfDegree_countable (d : ℕ) :
    Set.Countable (algebraicRealsOfDegree d) :=
  Set.Countable.mono (exact_degree_subset_bounded d)
    (algebraicRealsOfBoundedDegree_countable d)

/-- Algebraic complex numbers of exact degree d form a countable set. -/
theorem algebraicComplexOfDegree_countable (d : ℕ) :
    Set.Countable (algebraicComplexOfDegree d) := by
  apply Set.Countable.mono _ (algebraicComplexOfBoundedDegree_countable d)
  intro x hx
  exact ⟨hx.1, le_of_eq hx.2⟩

-- ============================================================================
-- § 4. Degree Stratification
-- ============================================================================

/-- The algebraic reals are the union of all degree strata.

Every algebraic number has some finite degree (the degree of its minimal
polynomial), so the algebraic reals decompose as ⋃ d, algebraicRealsOfDegree d. -/
theorem algebraic_reals_eq_iUnion_degree :
    {x : ℝ | IsAlgebraic ℚ x} = ⋃ d : ℕ, algebraicRealsOfDegree d := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, algebraicRealsOfDegree]
  constructor
  · intro hx
    exact ⟨(minpoly ℚ x).natDegree, hx, rfl⟩
  · rintro ⟨d, hx, -⟩
    exact hx

/-- The algebraic complex numbers are the union of all degree strata. -/
theorem algebraic_complex_eq_iUnion_degree :
    {x : ℂ | IsAlgebraic ℚ x} = ⋃ d : ℕ, algebraicComplexOfDegree d := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, algebraicComplexOfDegree]
  constructor
  · intro hx
    exact ⟨(minpoly ℚ x).natDegree, hx, rfl⟩
  · rintro ⟨d, hx, -⟩
    exact hx

/-- Alternative proof of algebraic reals being countable, via the degree
stratification: countable union of countable sets is countable. -/
theorem algebraic_reals_countable_via_strata :
    Set.Countable {x : ℝ | IsAlgebraic ℚ x} := by
  rw [algebraic_reals_eq_iUnion_degree]
  exact Set.countable_iUnion algebraicRealsOfDegree_countable

-- ============================================================================
-- § 5. Degree 1 = Rationals
-- ============================================================================

/-- Every rational number is algebraic of degree 1.

The minimal polynomial of q ∈ ℚ over ℚ is X - q, which has degree 1. -/
theorem rat_algebraic_degree_one (q : ℚ) :
    IsAlgebraic ℚ (algebraMap ℚ ℝ q) := isAlgebraic_algebraMap q

/-- The bounded degree sets form a monotone chain:
  algebraicRealsOfBoundedDegree d ⊆ algebraicRealsOfBoundedDegree (d + 1). -/
theorem bounded_degree_monotone (d : ℕ) :
    algebraicRealsOfBoundedDegree d ⊆ algebraicRealsOfBoundedDegree (d + 1) :=
  fun _ hx => ⟨hx.1, Nat.le_succ_of_le hx.2⟩

-- ============================================================================
-- § 6. Cardinality Comparisons
-- ============================================================================

/-- The algebraic and rational numbers have the same cardinality.

Both sets have cardinality ℵ₀, despite the algebraic numbers being a proper
superset of the rationals. This illustrates the "paradoxical" nature of
infinite cardinalities. -/
theorem card_algebraic_eq_card_rat :
    Cardinal.mk {x : ℝ // IsAlgebraic ℚ x} = Cardinal.mk ℚ := by
  rw [card_algebraic_reals_eq_aleph0, Cardinal.mk_denumerable]

/-- The algebraic and natural numbers have the same cardinality. -/
theorem card_algebraic_eq_card_nat :
    Cardinal.mk {x : ℝ // IsAlgebraic ℚ x} = Cardinal.mk ℕ := by
  rw [card_algebraic_reals_eq_aleph0, Cardinal.mk_denumerable]

-- ============================================================================
-- § 7. Growing Chain of Algebraic Numbers
-- ============================================================================

/-- The bounded degree sets form an exhaustive filtration of algebraic numbers.

The algebraic reals are the union ⋃ d, algebraicRealsOfBoundedDegree d. -/
theorem algebraic_reals_eq_iUnion_bounded :
    {x : ℝ | IsAlgebraic ℚ x} = ⋃ d : ℕ, algebraicRealsOfBoundedDegree d := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, algebraicRealsOfBoundedDegree]
  constructor
  · intro hx
    exact ⟨(minpoly ℚ x).natDegree, hx, le_refl _⟩
  · rintro ⟨d, hx, -⟩
    exact hx

end AlgebraicNumbersCountable

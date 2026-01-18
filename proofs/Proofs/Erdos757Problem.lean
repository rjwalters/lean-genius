/-
  Erdős Problem #757: Sidon Sets in Almost-Sidon Families

  Let A ⊂ ℝ be a set of size n such that every subset B ⊆ A with |B| = 4
  has |B - B| ≥ 11. Find the best constant c > 0 such that A must always
  contain a Sidon set of size ≥ cn.

  For comparison, a Sidon set B of size 4 has |B - B| = 13 (all differences
  distinct, plus 0). So the condition says at most one difference is "missing"
  from any 4-element subset.

  **Known Bounds** (Gyárfás-Lehel 1995):
  - 1/2 < c ≤ 3/5 (the exact value is OPEN)

  References:
  - https://erdosproblems.com/757
  - Gyárfás, A., Lehel, J., "Linear sets with five distinct differences
    among any four elements", J. Combin. Theory Ser. B (1995), 108-118.
-/

import Mathlib

open scoped Pointwise
open Filter Set Finset

namespace Erdos757

/-!
## Core Definitions

A **Sidon set** is a set where all pairwise sums are distinct. Equivalently,
all non-zero differences are distinct.
-/

/-- A set S is **Sidon** if all pairwise sums a + b (a ≤ b) are distinct.
Equivalently, if a + b = c + d with a ≤ b and c ≤ d, then {a,b} = {c,d}. -/
def IsSidon (S : Set ℝ) : Prop :=
  ∀ a b c d : ℝ, a ∈ S → b ∈ S → c ∈ S → d ∈ S →
    a + b = c + d → ({a, b} : Set ℝ) = {c, d}

/-- The difference set A - A = {a - a' : a, a' ∈ A}. -/
def differenceSet (A : Set ℝ) : Set ℝ := A - A

/-!
## The Almost-Sidon Condition

A 4-element Sidon set has exactly 13 elements in its difference set:
- 0 (from a - a)
- 12 distinct non-zero differences (±(aᵢ - aⱼ) for i ≠ j)

The condition |B - B| ≥ 11 says we're "close" to being Sidon.
-/

/-- A set A has the **almost-Sidon property** if every 4-element subset B
has at least 11 elements in B - B. -/
def AlmostSidon (A : Set ℝ) : Prop :=
  ∀ B ⊆ A, B.ncard = 4 → (B - B).ncard ≥ 11

/-- A constant c is **admissible** if every finite almost-Sidon set A
contains a Sidon subset of size at least c * |A|. -/
def IsAdmissible (c : ℝ) : Prop :=
  ∀ {A : Set ℝ}, A.Finite → AlmostSidon A →
    ∃ S ⊆ A, IsSidon S ∧ c * A.ncard ≤ (S.ncard : ℝ)

/-!
## Main Conjecture

Find the exact value of sup{c : IsAdmissible c}.
-/

/-- **Erdős Problem #757 (OPEN)**: What is the supremum of the set of
admissible constants?

Gyárfás-Lehel (1995) proved 1/2 < sSup {c | IsAdmissible c} < 3/5.
The exact value remains unknown. -/
axiom erdos_757_conjecture :
    ∃ c : ℝ, c = sSup {x : ℝ | IsAdmissible x} ∧ (1/2 : ℝ) < c ∧ c < 3/5

/-!
## Known Results (Gyárfás-Lehel 1995)
-/

/-- **Lower Bound** (Gyárfás-Lehel 1995): The supremum is strictly larger
than 1/2.

The proof constructs explicit Sidon subsets using a greedy algorithm. -/
axiom gyarfas_lehel_lower_bound :
    (1/2 : ℝ) < sSup {c : ℝ | IsAdmissible c}

/-- **Upper Bound** (Gyárfás-Lehel 1995): The supremum is strictly less
than 3/5.

The proof exhibits a family of almost-Sidon sets where the largest
Sidon subset has size just under 3n/5. -/
axiom gyarfas_lehel_upper_bound :
    sSup {c : ℝ | IsAdmissible c} < (3/5 : ℝ)

/-!
## Properties of Sidon Sets
-/

/-- A Sidon set of size n has exactly n(n-1)/2 + 1 elements in its
difference set (the +1 is for 0). -/
axiom sidon_difference_count :
    ∀ S : Finset ℝ, IsSidon (↑S : Set ℝ) →
      ((↑S : Set ℝ) - ↑S).ncard = S.card * (S.card - 1) / 2 + S.card + 1

/-- In particular, a Sidon set of size 4 has difference set of size 13. -/
axiom sidon_4_difference_count :
    ∀ S : Finset ℝ, S.card = 4 → IsSidon (↑S : Set ℝ) →
      ((↑S : Set ℝ) - ↑S).ncard = 13

/-- Any subset of a Sidon set is Sidon. -/
axiom sidon_subset :
    ∀ S T : Set ℝ, IsSidon S → T ⊆ S → IsSidon T

/-- The empty set is Sidon. -/
theorem sidon_empty : IsSidon (∅ : Set ℝ) := by
  intro a b c d ha _ _ _
  exact absurd ha (Set.notMem_empty a)

/-- Singletons are Sidon. -/
theorem sidon_singleton (x : ℝ) : IsSidon ({x} : Set ℝ) := by
  intro a b c d ha hb hc hd _
  rw [Set.mem_singleton_iff] at ha hb hc hd
  subst ha hb hc hd
  rfl

/-- Pairs are Sidon. -/
axiom sidon_pair (x y : ℝ) (hxy : x ≠ y) : IsSidon ({x, y} : Set ℝ)

/-!
## Difference Sets
-/

/-- The difference set always contains 0. -/
theorem zero_mem_differenceSet (A : Set ℝ) (hA : A.Nonempty) :
    (0 : ℝ) ∈ differenceSet A := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a, ha, a, ha, sub_self a⟩

/-- The difference set is symmetric: x ∈ A - A ↔ -x ∈ A - A. -/
theorem differenceSet_symmetric (A : Set ℝ) (x : ℝ) :
    x ∈ differenceSet A ↔ -x ∈ differenceSet A := by
  constructor <;> intro ⟨a, ha, b, hb, hab⟩
  · exact ⟨b, hb, a, ha, by linarith⟩
  · exact ⟨b, hb, a, ha, by linarith⟩

/-!
## The Condition |B - B| ≥ 11

This condition is a relaxation of the Sidon property. It says that
among any 4 elements, we can have at most one "collision" of differences.
-/

/-- The maximum size of |B - B| for a 4-element set B is 13 (Sidon case). -/
axiom max_difference_4 :
    ∀ B : Finset ℝ, B.card = 4 → (↑B - ↑B : Set ℝ).ncard ≤ 13

/-- The minimum size of |B - B| for a 4-element set B is 7
(arithmetic progression case). -/
axiom min_difference_4 :
    ∀ B : Finset ℝ, B.card = 4 → 7 ≤ (↑B - ↑B : Set ℝ).ncard

/-- An almost-Sidon set has the property that no 4-element subset is
"too far" from being Sidon. -/
theorem almostSidon_of_sidon (A : Set ℝ) (hA : IsSidon A) : AlmostSidon A := by
  intro B hB hcard
  -- If A is Sidon, so is B
  -- A Sidon set of size 4 has |B - B| = 13 ≥ 11
  sorry

/-!
## The Set of Admissible Constants
-/

/-- 0 is admissible (trivially, the empty set is Sidon). -/
theorem zero_admissible : IsAdmissible 0 := by
  intro A _ _
  use ∅
  constructor
  · exact Set.empty_subset A
  · constructor
    · exact sidon_empty
    · simp

/-- Negative numbers are admissible. -/
theorem neg_admissible (c : ℝ) (hc : c < 0) : IsAdmissible c := by
  intro A _ _
  use ∅
  constructor
  · exact Set.empty_subset A
  · constructor
    · exact sidon_empty
    · simp only [Set.ncard_empty, Nat.cast_zero]
      have h : c * A.ncard ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg (le_of_lt hc) (Nat.cast_nonneg A.ncard)
      exact h

/-- The set of admissible constants is bounded above. -/
axiom admissible_bounded_above :
    BddAbove {c : ℝ | IsAdmissible c}

/-- The set of admissible constants is nonempty. -/
theorem admissible_nonempty : {c : ℝ | IsAdmissible c}.Nonempty :=
  ⟨0, zero_admissible⟩

/-!
## Connection to Extremal Combinatorics

This problem is part of a family of questions about the structure of
sets with "few" arithmetic configurations.
-/

/-- A **B₂ sequence** is another name for a Sidon set (from the perspective
of additive combinatorics). -/
def IsB2Sequence (S : Set ℝ) : Prop := IsSidon S

/-- The Sidon set constant problem: what is the largest Sidon subset
guaranteed in a set of size n? This is asymptotically √n. -/
axiom sidon_constant :
    ∃ C : ℝ, C > 0 ∧
      ∀ (A : Finset ℝ), ∃ S ⊆ (↑A : Set ℝ), IsSidon S ∧
        C * Real.sqrt A.card ≤ (S.ncard : ℝ)

end Erdos757

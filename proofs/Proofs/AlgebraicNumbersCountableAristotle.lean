/-
  Aristotle targets for Algebraic Numbers Countable
  Routine supporting lemmas for automated proof search.
  See AlgebraicNumbersCountable.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorems (algebraic reals/complex countable - fully proved)
  - Routine cardinality and set facts used in countability arguments
  - No definition sorries
  - No axioms

  Included targets (5):
  - nat_countable: ℕ is countable
  - int_countable: ℤ is countable
  - rat_countable: ℚ is countable
  - finset_countable: any finset is countable
  - set_countable_of_finite: finite sets are countable
-/
import Mathlib

namespace AlgebraicNumbersCountableAristotle

-- Routine: ℕ is countable.
-- The natural numbers are the prototype countable set.
theorem nat_countable : (Set.univ : Set ℕ).Countable := by
  sorry

-- Routine: ℤ is countable.
-- The integers are countable (bijection with ℕ).
theorem int_countable : (Set.univ : Set ℤ).Countable := by
  sorry

-- Routine: ℚ is countable.
-- The rationals are countable (Cantor diagonalization argument).
theorem rat_countable : (Set.univ : Set ℚ).Countable := by
  sorry

-- Routine: any Finset is countable.
-- Finite sets are clearly countable.
theorem finset_countable {α : Type*} (s : Finset α) : (s : Set α).Countable := by
  sorry

-- Routine: finite sets are countable.
-- A set is countable if it is finite.
theorem set_countable_of_finite {α : Type*} (s : Set α) (hs : s.Finite) : s.Countable := by
  sorry

end AlgebraicNumbersCountableAristotle

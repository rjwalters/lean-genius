/-
  Aristotle targets for Erdős Problem #623
  Routine supporting lemmas for automated proof search.
  See Erdos623Problem.lean for the main formalization.

  Criteria for inclusion:
  - erdos_623_dichotomy: logical dichotomy via push_neg; if ¬conjecture then negative exists
  - weak_follows_from_strong: if conjecture holds, exists free function with independent set
  - Excluded: aleph_omega_is_singular (requires cofinality computation)
  - Excluded: singleton_independent (direction might be false for B = ∅)
  - Excluded: counterexample_at_aleph_n (requires type construction from cardinality)
  - No axioms
  - No definition sorries
-/
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Tactic

namespace Erdos623Aristotle

open Cardinal Set

noncomputable def aleph_omega : Cardinal := Cardinal.aleph ω

/-- A function f : Finset X → X is "free" if f(A) ∉ A for all finite A. -/
def IsFreeFunction {X : Type*} (f : Finset X → X) : Prop :=
  ∀ A : Finset X, f A ∉ A

/-- A set Y ⊆ X is "independent" for f if f(B) ∉ Y for all finite B ⊆ Y. -/
def IsIndependent {X : Type*} (f : Finset X → X) (Y : Set X) : Prop :=
  ∀ B : Finset X, ↑B ⊆ Y → f B ∉ Y

/-- The main conjecture for ℵ_ω. -/
def erdos_623_conjecture : Prop :=
  ∀ (X : Type) (hX : #X = aleph_omega) (f : Finset X → X),
    IsFreeFunction f → ∃ Y : Set X, Y.Infinite ∧ IsIndependent f Y

/-- The negative formulation. -/
def erdos_623_negative : Prop :=
  ∃ (X : Type) (_ : #X = aleph_omega) (f : Finset X → X),
    IsFreeFunction f ∧ ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y

/-- The weak version: at least one free function has an infinite independent set. -/
def erdos_623_weak : Prop :=
  ∀ (X : Type) (_ : #X = aleph_omega),
    ∃ (f : Finset X → X) (Y : Set X),
      IsFreeFunction f ∧ Y.Infinite ∧ IsIndependent f Y

-- Routine: Logical dichotomy — conjecture or its negation holds.
-- From ¬erdos_623_conjecture, push_neg gives the existential negative formulation.
-- The two cases are exactly erdos_623_conjecture and erdos_623_negative.
theorem erdos_623_dichotomy :
    erdos_623_conjecture ∨ erdos_623_negative := by
  sorry

-- Routine: The weak version follows from the strong conjecture.
-- If for every free f there's an infinite independent set, then in particular
-- some free f and some infinite independent set exist.
-- (Requires IsFreeFunction instance; free functions exist for infinite X.)
theorem weak_follows_from_strong (h : erdos_623_conjecture) : erdos_623_weak := by
  sorry

-- Routine: Negation of an existential distributes as push_neg.
-- ¬(∃ Y, Y.Infinite ∧ IsIndependent f Y) = ∀ Y, Y.Infinite → ¬IsIndependent f Y
theorem neg_exists_iff {X : Type*} (f : Finset X → X) :
    (¬∃ Y : Set X, Y.Infinite ∧ IsIndependent f Y) ↔
    ∀ Y : Set X, Y.Infinite → ¬IsIndependent f Y := by
  sorry

-- Routine: Empty set is trivially independent for any function.
-- The condition ∀ B ⊆ ∅, f B ∉ ∅ is vacuously true.
theorem empty_independent {X : Type*} (f : Finset X → X) :
    IsIndependent f ∅ := by
  sorry

-- Routine: If ¬P and P ↔ Q, then ¬Q.
-- Basic logical fact used in dichotomy proof.
theorem not_of_iff_not {P Q : Prop} (h : P ↔ Q) (hn : ¬P) : ¬Q := by
  sorry

end Erdos623Aristotle

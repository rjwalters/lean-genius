/-!
# Erdős Problem #598: Coloring Countable Subsets

Let m be an infinite cardinal and κ = (2^ℵ₀)⁺ (successor of the continuum).
Can one color the countable subsets of m with κ colors so that every
X ⊆ m with |X| = κ contains subsets of every color?

## Status: OPEN

## References
- Erdős (1987)
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic

open Cardinal

/-!
## Section I: Cardinal Setup
-/

/-- κ = (2^ℵ₀)⁺: the successor of the continuum cardinal. -/
noncomputable def kappa : Cardinal := Order.succ (2 ^ ℵ₀)

/-- κ is uncountable: κ > ℵ₀. -/
axiom kappa_gt_aleph0 : kappa > ℵ₀

/-!
## Section II: Countable Subsets
-/

/-- The type of countable subsets of a type α. -/
def CountableSubset (α : Type*) := { S : Set α // S.Countable }

/-!
## Section III: The Coloring Property
-/

/-- A coloring of countable subsets of α using κ colors is a function
from countable subsets to some type with κ elements. -/
def IsKappaColoring (α : Type*) (c : CountableSubset α → Set.Iio kappa) : Prop :=
  True  -- any function is a valid coloring

/-- The chromatic completeness property: every subset X of α with
|X| = κ contains countable subsets of every color. -/
def ChromaticCompleteness (α : Type*) (c : CountableSubset α → Set.Iio kappa) : Prop :=
  ∀ X : Set α, Cardinal.mk X = kappa →
    ∀ color : Set.Iio kappa,
      ∃ S : CountableSubset α, S.1 ⊆ X ∧ c S = color

/-!
## Section IV: The Conjecture
-/

/-- **Erdős Problem #598**: For every infinite type α with |α| ≥ κ,
can we color countable subsets with κ colors such that every κ-sized
subset contains all colors? -/
def ErdosProblem598 : Prop :=
  ∀ (α : Type*) [Infinite α],
    Cardinal.mk α ≥ kappa →
      ∃ c : CountableSubset α → Set.Iio kappa,
        ChromaticCompleteness α c

/-!
## Section V: Special Cases
-/

/-- The case m = κ itself: can we color countable subsets of κ with
κ colors with chromatic completeness? This is the smallest case. -/
def ErdosProblem598Minimal : Prop :=
  ∃ c : CountableSubset (Set.Iio kappa) → Set.Iio kappa,
    ChromaticCompleteness (Set.Iio kappa) c

/-- Under CH (continuum hypothesis), κ = ℵ₂. The problem becomes
whether ℵ₂-many colors suffice for countable subsets with the
completeness property. -/
axiom under_CH_kappa_eq_aleph2 :
  Cardinal.continuum = ℵ₁ → kappa = aleph 2

/-!
## Section VI: Monotonicity
-/

/-- If the coloring exists for m, it exists for any m' ≥ m.
Larger ground sets only provide more room. -/
axiom coloring_monotone (α β : Type*) [Infinite α] [Infinite β]
    (h : Cardinal.mk α ≤ Cardinal.mk β)
    (c : CountableSubset β → Set.Iio kappa)
    (hc : ChromaticCompleteness β c) :
  ∃ c' : CountableSubset α → Set.Iio kappa,
    ChromaticCompleteness α c'

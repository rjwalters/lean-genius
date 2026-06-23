/-
  Aristotle targets for Erdos632Problem (a,b)-Choosability Scaling Conjecture
  Routine supporting lemmas for automated proof search.
  See Erdos632Problem.lean for the main formalization.

  Status: DISPROVED (Dvořák-Hu-Sereni 2019)

  Five provable lemmas about list coloring/choosability:
  - choosable_requires_b_le_a: b > a implies non-choosable (cardinality argument)
  - empty_graph_choosable: ⊥ is always (a,b)-choosable when b ≤ a (no adjacency)
  - choosable_mono_b: fewer required colors → easier choosability
  - choosable_mono_a: more available colors → easier choosability
  - list_chromatic_iff_choosable: sInf characterization of list chromatic number
-/
import Mathlib

open Finset Function SimpleGraph

namespace Erdos632.Aristotle

variable {V : Type*}

/-- A color assignment gives each vertex a list of available colors. -/
def ColorAssignment (V : Type*) (a : ℕ) := V → Finset (Fin a)

/-- A valid color assignment gives each vertex exactly 'a' colors. -/
def IsValidAssignment (L : ColorAssignment V a) : Prop :=
  ∀ v : V, (L v).card = a

/-- A color selection picks a subset from each vertex's list. -/
def ColorSelection (V : Type*) (a : ℕ) := V → Finset (Fin a)

/-- A valid selection picks exactly 'b' colors from each list. -/
def IsValidSelection (L : ColorAssignment V a) (S : ColorSelection V a) (b : ℕ) : Prop :=
  ∀ v : V, (S v) ⊆ (L v) ∧ (S v).card = b

/-- Adjacent vertices have disjoint color selections. -/
def SelectionsDisjoint (G : SimpleGraph V) (S : ColorSelection V a) : Prop :=
  ∀ u v : V, G.Adj u v → Disjoint (S u) (S v)

/-- A graph is (a,b)-choosable if for any valid a-list, there exists a b-selection
    such that adjacent vertices have disjoint selections. -/
def IsChoosable (G : SimpleGraph V) (a b : ℕ) : Prop :=
  ∀ L : ColorAssignment V a, IsValidAssignment L →
    ∃ S : ColorSelection V a, IsValidSelection L S b ∧ SelectionsDisjoint G S

/-- The list chromatic number of G. -/
noncomputable def listChromaticNumber (G : SimpleGraph V) : ℕ :=
  sInf { a : ℕ | IsChoosable G a 1 }

/-
## Lemma 1: b > a makes choosability impossible

If b > a, then no valid b-selection can exist (we can't pick b colors
from a list of size a when b > a), so G is not (a,b)-choosable.
-/

/-- b > a implies G is NOT (a,b)-choosable. -/
theorem choosable_requires_b_le_a (G : SimpleGraph V) (a b : ℕ) (hb : b > a) :
    ¬IsChoosable G a b := by
  sorry

/-
## Lemma 2: Empty graph is always (a,b)-choosable when b ≤ a

The empty graph has no edges, so SelectionsDisjoint holds vacuously.
We just need to select b elements from each a-element list, which is
possible whenever b ≤ a.
-/

/-- The empty graph on V is (a,b)-choosable whenever b ≤ a. -/
theorem empty_graph_choosable (V : Type*) (a b : ℕ) (h : b ≤ a) :
    IsChoosable (⊥ : SimpleGraph V) a b := by
  sorry

/-
## Lemma 3: Choosability is anti-monotone in b

If G is (a,b₁)-choosable and b₂ ≤ b₁, then G is (a,b₂)-choosable.
Take the b₁-selection and restrict to any b₂-element subset of it.
-/

/-- Fewer required colors makes choosability easier. -/
theorem choosable_mono_b (G : SimpleGraph V) (a b₁ b₂ : ℕ) (h : b₁ ≥ b₂)
    (hc : IsChoosable G a b₁) : IsChoosable G a b₂ := by
  sorry

/-
## Lemma 4: Choosability is monotone in a

If G is (a₁,b)-choosable and a₁ ≤ a₂, then G is (a₂,b)-choosable.
More colors available makes it easier to find a valid selection.
-/

/-- More available colors makes choosability easier. -/
theorem choosable_mono_a (G : SimpleGraph V) (a₁ a₂ b : ℕ) (h : a₁ ≤ a₂)
    (hc : IsChoosable G a₁ b) : IsChoosable G a₂ b := by
  sorry

/-
## Lemma 5: List chromatic number characterization

The list chromatic number sInf {a | IsChoosable G a 1} is ≤ a
if and only if G is (a,1)-choosable.
-/

/-- χ_L(G) ≤ a ↔ G is (a,1)-choosable. -/
theorem list_chromatic_iff_choosable (G : SimpleGraph V) (a : ℕ) :
    listChromaticNumber G ≤ a ↔ IsChoosable G a 1 := by
  sorry

end Erdos632.Aristotle

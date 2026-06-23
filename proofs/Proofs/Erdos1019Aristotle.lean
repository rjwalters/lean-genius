/-
  Aristotle targets for Erdős Problem #1019
  Routine supporting lemmas for automated proof search.
  See Erdos1019Problem.lean for the main formalization.

  Main open sorry: K4_saturated_planar has 1 sorry:
    (⊤ : SimpleGraph ↥S).edgeFinset.card = 6 given Fintype.card ↥S = 4

  Criteria for inclusion:
  - NOT the main open conjecture (simonovits_theorem)
  - Known result likely in Mathlib
  - Clean statement with no definition sorries
  - No axiom declarations
-/
import Mathlib

namespace Erdos1019Aristotle

open SimpleGraph

-- Routine: The complete graph (⊤) on a type with 4 elements has exactly 6 edges.
-- This is C(4,2) = 4.choose 2 = 6.
-- Proof approach: use Fintype.equivFinOfCardEq to get α ≃ Fin 4,
-- then use the bijection to reduce to native_decide on (⊤ : SimpleGraph (Fin 4)).
-- Alternative: use card_edgeFinset_le_card_choose_two + lower bound from injectivity.
theorem top_edgeFinset_card_of_card_eq_four {α : Type*} [Fintype α] [DecidableEq α]
    (h : Fintype.card α = 4) :
    (⊤ : SimpleGraph α).edgeFinset.card = 6 := by sorry

-- Routine: Fintype.card (Fin 4) = 4
theorem fin4_card : Fintype.card (Fin 4) = 4 := by sorry

-- Routine: The top graph on Fin 4 has 6 edges (direct computation).
theorem top_edgeFinset_card_fin4 :
    (⊤ : SimpleGraph (Fin 4)).edgeFinset.card = 6 := by sorry

-- Routine: C(4,2) = 6
theorem choose_4_2 : Nat.choose 4 2 = 6 := by sorry

-- Routine: The edge count of the top graph on α equals (Fintype.card α).choose 2.
-- Key formula: n(n-1)/2 = n.choose 2 for complete graphs.
theorem top_edgeFinset_card_eq_choose {α : Type*} [Fintype α] [DecidableEq α] :
    (⊤ : SimpleGraph α).edgeFinset.card = (Fintype.card α).choose 2 := by sorry

end Erdos1019Aristotle

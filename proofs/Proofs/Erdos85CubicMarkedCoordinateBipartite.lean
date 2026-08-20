import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.ZMod.Basic

/-! # Diagonal coordinate transitions force even marked cycles -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
private theorem zmodEight_unitStep_parity_cases :
    ∀ i j : ZMod 8, (j = i - 1 ∨ j = i + 1) →
      (i.val % 2 = 0 ∧ j.val % 2 = 1) ∨
      (i.val % 2 = 1 ∧ j.val % 2 = 0) := by
  native_decide

/-- Any graph whose edges change a `ZMod 8` coordinate by `±1` is bipartite,
colored by the parity of that coordinate.  In the h305 value-five graph, the
straight/crossed local matching theorem supplies precisely this step law. -/
theorem isBipartite_of_zmodEight_unitStep
    {α : Type*} (G : SimpleGraph α) (coord : α → ZMod 8)
    (hstep : ∀ ⦃a b⦄, G.Adj a b →
      coord b = coord a - 1 ∨ coord b = coord a + 1) :
    G.IsBipartite := by
  rw [SimpleGraph.isBipartite_iff_exists_isBipartiteWith]
  let evenSide : Set α := {a | (coord a).val % 2 = 0}
  let oddSide : Set α := {a | (coord a).val % 2 = 1}
  refine ⟨evenSide, oddSide, ?_⟩
  constructor
  · apply Set.disjoint_left.mpr
    intro a ha hb
    change (coord a).val % 2 = 0 at ha
    change (coord a).val % 2 = 1 at hb
    omega
  · intro a b hab
    rcases zmodEight_unitStep_parity_cases
      (coord a) (coord b) (hstep hab) with h | h
    · exact Or.inl h
    · exact Or.inr h

end

end Erdos85

#print axioms Erdos85.isBipartite_of_zmodEight_unitStep

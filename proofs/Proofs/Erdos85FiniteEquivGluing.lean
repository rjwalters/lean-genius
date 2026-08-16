import Mathlib

/-!
# Gluing finite equivalences along a decidable partition

This small constructor is used by the order-49 normalization to combine the
high block, two overlapping-neighborhood pieces, and their complement without
reproving bijectivity for a casewise function.
-/

namespace Erdos85

noncomputable section

/-- Glue equivalences on a predicate and its complement into an equivalence
of the ambient types. -/
def equivOfSubtypeAndCompl
    {α β : Type*} (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q]
    (ep : {x // p x} ≃ {y // q y})
    (en : {x // ¬ p x} ≃ {y // ¬ q y}) : α ≃ β :=
  (Equiv.sumCompl p).symm |>.trans
    ((Equiv.sumCongr ep en).trans (Equiv.sumCompl q))

theorem equivOfSubtypeAndCompl_apply_pos
    {α β : Type*} (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q]
    (ep : {x // p x} ≃ {y // q y})
    (en : {x // ¬ p x} ≃ {y // ¬ q y})
    (x : α) (hx : p x) :
    equivOfSubtypeAndCompl p q ep en x = (ep ⟨x, hx⟩).1 := by
  simp [equivOfSubtypeAndCompl, Equiv.sumCompl, hx]

theorem equivOfSubtypeAndCompl_apply_neg
    {α β : Type*} (p : α → Prop) (q : β → Prop)
    [DecidablePred p] [DecidablePred q]
    (ep : {x // p x} ≃ {y // q y})
    (en : {x // ¬ p x} ≃ {y // ¬ q y})
    (x : α) (hx : ¬ p x) :
    equivOfSubtypeAndCompl p q ep en x = (en ⟨x, hx⟩).1 := by
  simp [equivOfSubtypeAndCompl, Equiv.sumCompl, hx]

end


end Erdos85

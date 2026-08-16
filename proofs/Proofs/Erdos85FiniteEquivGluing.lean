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

/-- Extend a finite injective partial labeling to an equivalence with
`Fin n`.  This is convenient when several locally normalized pieces have
already been combined into one injective list: the unnamed complement is
filled in automatically. -/
theorem exists_equiv_fin_extending_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    {n k : Nat} (hcard : Fintype.card V = n)
    (f : Fin k → V) (g : Fin k → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ E : V ≃ Fin n, ∀ i, E (f i) = g i := by
  let b : Fin n ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let f' : Fin k → Fin n := fun i => b.symm (f i)
  have hf' : Function.Injective f' := b.symm.injective.comp hf
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f' g hf' hg
  refine ⟨b.symm.trans σ, ?_⟩
  intro i
  exact hσ i

end


end Erdos85

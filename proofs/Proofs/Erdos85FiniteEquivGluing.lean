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
    {V I : Type*} [Fintype V] [DecidableEq V] [Finite I]
    {n : Nat} (hcard : Fintype.card V = n)
    (f : I → V) (g : I → Fin n)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ E : V ≃ Fin n, ∀ i, E (f i) = g i := by
  let b : Fin n ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  let f' : I → Fin n := fun i => b.symm (f i)
  have hf' : Function.Injective f' := b.symm.injective.comp hf
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f' g hf' hg
  refine ⟨b.symm.trans σ, ?_⟩
  intro i
  exact hσ i

theorem Sum.elim_injective_of_disjoint
    {I J X : Type*} {f : I → X} {g : J → X}
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hcross : ∀ i j, f i ≠ g j) :
    Function.Injective (Sum.elim f g) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j => simpa using hf hxy
      | inr j => exact (hcross i j hxy).elim
  | inr i =>
      cases y with
      | inl j => exact (hcross j i hxy.symm).elim
      | inr j => simpa using hg hxy

/-- Extend two disjoint injective partial labelings simultaneously. -/
theorem exists_equiv_fin_extending_disjoint_pairs
    {V I J : Type*} [Fintype V] [DecidableEq V]
    [Finite I] [Finite J] {n : Nat}
    (hcard : Fintype.card V = n)
    (fI : I → V) (fJ : J → V) (gI : I → Fin n) (gJ : J → Fin n)
    (hfI : Function.Injective fI) (hfJ : Function.Injective fJ)
    (hgI : Function.Injective gI) (hgJ : Function.Injective gJ)
    (hfCross : ∀ i j, fI i ≠ fJ j)
    (hgCross : ∀ i j, gI i ≠ gJ j) :
    ∃ E : V ≃ Fin n,
      (∀ i, E (fI i) = gI i) ∧ (∀ j, E (fJ j) = gJ j) := by
  obtain ⟨E, hE⟩ := exists_equiv_fin_extending_pair hcard
    (Sum.elim fI fJ) (Sum.elim gI gJ)
    (Sum.elim_injective_of_disjoint hfI hfJ hfCross)
    (Sum.elim_injective_of_disjoint hgI hgJ hgCross)
  exact ⟨E, fun i => hE (Sum.inl i), fun j => hE (Sum.inr j)⟩

end


end Erdos85

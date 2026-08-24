import Proofs.Erdos85MinimalEvenConfigurationKernelRigidity

/-!
# Rank formula for a minimal binary even configuration

Rank-nullity converts circuit kernel rigidity into the exact identity
`rank(incidence) + 1 = number of rows`.  In particular, a circuit has at
most one more row than available point coordinates.
-/

open Finset

namespace Erdos85

noncomputable section

/-- The incidence matrix of a nonempty minimal even configuration has rank
exactly one less than its number of rows. -/
theorem minimal_even_configuration_incidenceRank_add_one_eq_card
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (heven : ∀ y : β,
      Even (((Finset.univ : Finset α).filter fun a => Inc a y).card))
    (hminimal : ∀ U : Finset α, U ⊂ Finset.univ → U.Nonempty →
      ¬ ∀ y : β, Even ((U.filter fun a => Inc a y).card)) :
    let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
    Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) + 1 =
      Fintype.card α := by
  classical
  dsimp only
  let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
  have hnull :=
    (minimal_even_configuration_kernel_eq_span_one Inc heven hminimal).2
  have hrankNull := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [hnull] at hrankNull
  simpa [Module.finrank_fintype_fun_eq_card] using hrankNull

/-- Singleton-form consequence: a nonempty minimal binary even
configuration has at most one more row than point coordinates.  Consumers
may take `β` to be the actually used support, not the whole ambient point
set. -/
theorem minimal_even_configuration_card_le_pointCard_add_one
    {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (heven : ∀ y : β,
      Even (((Finset.univ : Finset α).filter fun a => Inc a y).card))
    (hminimal : ∀ U : Finset α, U ⊂ Finset.univ → U.Nonempty →
      ¬ ∀ y : β, Even ((U.filter fun a => Inc a y).card)) :
    Fintype.card α ≤ Fintype.card β + 1 := by
  classical
  let M : Matrix β α (ZMod 2) := fun y a => if Inc a y then 1 else 0
  have hrank :=
    minimal_even_configuration_incidenceRank_add_one_eq_card
      Inc heven hminimal
  have hle : Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) ≤
      Module.finrank (ZMod 2) (β → ZMod 2) :=
    LinearMap.finrank_le_finrank_of_injective
      (Submodule.subtype_injective (LinearMap.range M.mulVecLin))
  rw [Module.finrank_fintype_fun_eq_card] at hle
  change Module.finrank (ZMod 2) (LinearMap.range M.mulVecLin) + 1 =
    Fintype.card α at hrank
  omega

end

end Erdos85

#print axioms
  Erdos85.minimal_even_configuration_incidenceRank_add_one_eq_card
#print axioms
  Erdos85.minimal_even_configuration_card_le_pointCard_add_one

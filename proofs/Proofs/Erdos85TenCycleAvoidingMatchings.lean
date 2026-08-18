import Proofs.Erdos85OneRegularRelationEquiv

/-!
# Perfect matchings avoiding a ten-cycle

The triangle-bearing `C10` block leaves exactly thirteen possible residual
perfect matchings before further symmetry quotienting.
-/

namespace Erdos85

def standardTenCycleRelation (x y : Fin 5) : Prop :=
  y.val = x.val ∨ y.val = (x.val + 4) % 5

instance standardTenCycleRelation_decidable :
    DecidableRel standardTenCycleRelation := by
  intro x y
  unfold standardTenCycleRelation
  infer_instance

def tenCycleAvoidingMatchings : Finset (Equiv.Perm (Fin 5)) :=
  Finset.univ.filter fun f => ∀ x, ¬ standardTenCycleRelation x (f x)

set_option maxRecDepth 100000 in
/-- Closed kernel audit: exactly thirteen permutations avoid every edge of
the standard bipartite ten-cycle. -/
theorem tenCycleAvoidingMatchings_card :
    tenCycleAvoidingMatchings.card = 13 := by
  decide

end Erdos85

#print axioms Erdos85.tenCycleAvoidingMatchings_card

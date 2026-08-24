import Proofs.Erdos85ThreeSeparatorKFiberColorTemplate

/-!
# Exact attachment deficit at a P-center

The fiber of `p_w` splits into points with no separator attachment and
points attached to the complementary separator vertex `w`.  The first
class labels the edges incident with `p_w` in `Γ_K`; hence the degree
deficit is exactly the size of the second class.  This is (B41').
-/

open Finset SimpleGraph

namespace Erdos85

/-- Predicate form of the exact deficit identity in B41'. -/
theorem fiber_deficit_eq_filter_card
    {V : Type*} [DecidableEq V]
    (F : Finset V) (attached : V → Prop)
    [DecidablePred attached] [∀ x, Decidable (¬ attached x)]
    (a d : ℕ)
    (hFcard : F.card = a)
    (hdegree : (F.filter fun x ↦ ¬ attached x).card = d) :
    d + (F.filter attached).card = a ∧
      a - d = (F.filter attached).card := by
  have hsplit := F.card_filter_add_card_filter_not attached
  rw [hFcard, hdegree] at hsplit
  omega

/-- Graph-facing B41': if the `Γ_K` degree of `p` counts precisely the
points of its X-fiber not D-adjacent to `w`, its deficit counts precisely
the D-attached points. -/
theorem PCenter_KFiber_degree_deficit_eq_attachment_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel D.Adj]
    (X : Finset V) (p w : V) (a d : ℕ)
    (hfiberCard : (A.neighborFinset p ∩ X).card = a)
    (hdegree : ((A.neighborFinset p ∩ X).filter fun x ↦ ¬ D.Adj x w).card = d) :
    d + ((A.neighborFinset p ∩ X).filter fun x ↦ D.Adj x w).card = a ∧
      a - d = ((A.neighborFinset p ∩ X).filter fun x ↦ D.Adj x w).card := by
  exact fiber_deficit_eq_filter_card
    (A.neighborFinset p ∩ X) (fun x ↦ D.Adj x w) a d hfiberCard hdegree

#print axioms fiber_deficit_eq_filter_card
#print axioms PCenter_KFiber_degree_deficit_eq_attachment_card

end Erdos85

import Proofs.Erdos85IsCyclesComponentCharpoly
import Proofs.Erdos85OrderSixteenTwoFourCyclesTriangleBound
import Proofs.Erdos85ResidueSignedCount

/-! # Two four-cycle components leave at most one triangle component

This is the graph-facing form of the order-sixteen partition obstruction.
-/

namespace Erdos85

open SimpleGraph

/-- In a two-regular graph on sixteen vertices, two distinct components of
order four force uniqueness of any component of order three. -/
theorem twoRegular_orderSixteen_two_orderFour_components_orderThree_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) [DecidableRel F.Adj]
    (hcard : Fintype.card V = 16)
    (hdeg : ∀ v, F.degree v = 2)
    (a b : F.ConnectedComponent) (hab : a ≠ b)
    (ha : a.supp.ncard = 4) (hb : b.supp.ncard = 4)
    {c d : F.ConnectedComponent}
    (hc : c.supp.ncard = 3) (hd : d.supp.ncard = 3) : c = d := by
  classical
  by_contra hcd
  have hmin : ∀ e : F.ConnectedComponent, 3 ≤ e.supp.ncard := by
    intro e
    obtain ⟨x, p, hp, hpverts, _⟩ :=
      twoRegular_component_induce_eq_cycleSubgraph F hdeg e
    calc
      3 ≤ p.length := hp.three_le_length
      _ = Nat.card p.toSubgraph.verts := (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = e.supp.ncard := congrArg Set.ncard hpverts
  have hsum : ∑ e : F.ConnectedComponent, e.supp.ncard = 16 := by
    simpa [hcard] using sum_connectedComponent_supp_ncard F
  have hac : a ≠ c := by
    intro h
    subst c
    omega
  have had : a ≠ d := by
    intro h
    subst d
    omega
  have hbc : b ≠ c := by
    intro h
    subst c
    omega
  have hbd : b ≠ d := by
    intro h
    subst d
    omega
  exact orderSixteen_partition_false_of_two_four_two_three
    (fun e : F.ConnectedComponent ↦ e.supp.ncard)
    hsum hmin hab hac had hbc hbd hcd ha hb hc hd

end Erdos85

import Proofs.Erdos85IsCyclesComponentCharpoly

/-!
# Two-regular graphs of order five

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

A simple two-regular graph has cycle components, each of order at least
three.  Five vertices cannot support two such components, so the graph is a
single spanning five-cycle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every simple two-regular graph on five vertices is connected. -/
theorem twoRegular_order_five_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x = 2)
    (hcard : Fintype.card V = 5) :
    G.Connected := by
  classical
  have hcomponent (c : G.ConnectedComponent) : 3 ≤ c.supp.ncard := by
    obtain ⟨r, hr, hre, _⟩ :=
      twoRegular_component_charpoly_chebyshev G hdeg c
    omega
  have hparts : (∑ c : G.ConnectedComponent, c.supp.ncard) = 5 := by
    calc
      (∑ c : G.ConnectedComponent, c.supp.ncard) =
          ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
            apply Finset.sum_congr rfl
            intro c _
            simpa [Nat.card_eq_fintype_card] using
              (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : G.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
      _ = 5 := hcard
  have hsub : Subsingleton G.ConnectedComponent := by
    constructor
    intro c d
    by_contra hcd
    have hpair : c.supp.ncard + d.supp.ncard ≤
        ∑ e : G.ConnectedComponent, e.supp.ncard := by
      calc
        c.supp.ncard + d.supp.ncard =
            ∑ e ∈ ({c, d} : Finset G.ConnectedComponent), e.supp.ncard := by
              simp [hcd]
        _ ≤ ∑ e ∈ (Finset.univ : Finset G.ConnectedComponent),
              e.supp.ncard := by
              exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by simp)
        _ = ∑ e : G.ConnectedComponent, e.supp.ncard := by simp
    rw [hparts] at hpair
    have hc := hcomponent c
    have hd := hcomponent d
    omega
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  exact ⟨fun x y => by
    apply ConnectedComponent.exact
    exact hsub.elim (G.connectedComponentMk x) (G.connectedComponentMk y)⟩

/-- Cycle witness form: a simple two-regular graph of order five is traced
by a spanning simple closed walk of length five. -/
theorem twoRegular_order_five_exists_spanning_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ x, G.degree x = 2)
    (hcard : Fintype.card V = 5) :
    ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧ p.length = 5 ∧
      p.toSubgraph.verts = Set.univ ∧
      p.toSubgraph.coe = G.induce p.toSubgraph.verts := by
  classical
  have hconn := twoRegular_order_five_connected G hdeg hcard
  let c := G.connectedComponentMk (Classical.choice (Fintype.card_pos_iff.mp (by omega)))
  obtain ⟨x, p, hp, hpverts, hpgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph G hdeg c
  have hcsupp : c.supp = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    rw [ConnectedComponent.mem_supp_iff]
    exact ConnectedComponent.sound (hconn _ _)
  have hlen : p.length = 5 := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
      _ = 5 := by
        rw [hcsupp, Set.ncard_univ]
        simpa [Nat.card_eq_fintype_card] using hcard
  refine ⟨x, p, hp, hlen, hpverts.trans hcsupp, ?_⟩
  exact hpgraph

end

end Erdos85

#print axioms Erdos85.twoRegular_order_five_connected
#print axioms Erdos85.twoRegular_order_five_exists_spanning_cycle

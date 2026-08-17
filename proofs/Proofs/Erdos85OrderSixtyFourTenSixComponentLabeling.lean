import Proofs.Erdos85OrderSixtyFourTenSixEncoding
import Proofs.Erdos85IsCyclesComponentCharpoly

/-! # Constructing the certificate labeling of a `[10,6]` two-factor -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A connected component of a finite two-regular graph is not merely the
right size: it admits cycle coordinates preserving adjacency. -/
theorem exists_componentCycleEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdeg : ∀ x, H.degree x = 2)
    (c : H.ConnectedComponent) (n : Nat) (hc : c.supp.ncard = n) :
    ∃ e : Fin n ≃ c.supp,
      ∀ i j, (cycleGraph n).Adj i j ↔ H.Adj (e i).1 (e j).1 := by
  classical
  obtain ⟨x, p, hp, hpverts, hgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph H hdeg c
  have hlen : p.length = n := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
      _ = n := hc
  clear hc
  subst n
  let e : Fin p.length ≃ c.supp :=
    (cycleVertexEquiv hp).trans (Equiv.setCongr hpverts)
  refine ⟨e, ?_⟩
  intro i j
  have hij : (cycleGraph p.length).Adj i j ↔
      p.toSubgraph.coe.Adj (cycleVertexEquiv hp i)
        (cycleVertexEquiv hp j) :=
    (isCycle_cycleGraphIsoToSubgraph hp).map_rel_iff.symm
  change (cycleGraph p.length).Adj i j ↔
    H.Adj ((Equiv.setCongr hpverts) (cycleVertexEquiv hp i)).1
      ((Equiv.setCongr hpverts) (cycleVertexEquiv hp j)).1
  rw [hij]
  rw [hgraph]
  rfl

theorem tenSixCycleGraph_left : ∀ i j : Fin 10,
    tenSixCycleGraph.Adj (Fin.castAdd 6 i) (Fin.castAdd 6 j) ↔
      (cycleGraph 10).Adj i j := by
  native_decide

theorem tenSixCycleGraph_right : ∀ i j : Fin 6,
    tenSixCycleGraph.Adj (Fin.natAdd 10 i) (Fin.natAdd 10 j) ↔
      (cycleGraph 6).Adj i j := by
  native_decide

theorem tenSixCycleGraph_cross_left_right : ∀ (i : Fin 10) (j : Fin 6),
    ¬tenSixCycleGraph.Adj (Fin.castAdd 6 i) (Fin.natAdd 10 j) := by
  native_decide

theorem tenSixCycleGraph_cross_right_left : ∀ (i : Fin 6) (j : Fin 10),
    ¬tenSixCycleGraph.Adj (Fin.natAdd 10 i) (Fin.castAdd 6 j) := by
  native_decide

end

end Erdos85

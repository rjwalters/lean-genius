import Proofs.Erdos85ComponentCycleCharpoly

/-! # Characteristic polynomials of components of a two-factor

This file packages the generic part of the defect-cycle argument: every
connected component of a finite graph in which every vertex has degree two
is a spanning simple cycle, so its induced adjacency characteristic
polynomial is the corresponding Chebyshev cycle polynomial.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Every connected component of a finite 2-regular graph is traced by a
simple cycle whose subgraph is exactly the graph induced on the component. -/
theorem twoRegular_component_induce_eq_cycleSubgraph
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, G.degree x = 2)
    (c : G.ConnectedComponent) :
    ∃ (x : V) (p : G.Walk x x), p.IsCycle ∧
      p.toSubgraph.verts = c.supp ∧
      p.toSubgraph.coe = G.induce p.toSubgraph.verts := by
  classical
  obtain ⟨x, hx⟩ := c.nonempty_supp
  have hcycles : G.IsCycles := by
    intro v _hv
    rw [← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree, hdeg v]
  have hn : (G.neighborSet x).Nonempty :=
    G.neighborSet_nonempty.mpr ((G.degree_pos x).mp (by rw [hdeg]; omega))
  obtain ⟨p, hp, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hx hn
  refine ⟨x, p, hp, hpverts, ?_⟩
  exact isCycle_toSubgraph_coe_eq_induce_of_degree_two hp
    (fun v _hv ↦ hdeg v)

/-- The adjacency characteristic polynomial of a component of a finite
2-regular graph is `C_r - 2`, where `r` is the component order. -/
theorem twoRegular_component_charpoly_chebyshev
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hdeg : ∀ x, G.degree x = 2)
    (c : G.ConnectedComponent) :
    ∃ r : ℕ, 3 ≤ r ∧ r = c.supp.ncard ∧
      ((G.induce c.supp).adjMatrix ℤ).charpoly =
        Polynomial.Chebyshev.C ℤ (r : ℤ) - 2 := by
  classical
  obtain ⟨x, p, hp, hpverts, hgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph G hdeg c
  letI : Fintype p.toSubgraph.verts := Fintype.ofFinite _
  letI : DecidableRel p.toSubgraph.coe.Adj := Classical.decRel _
  letI : DecidableRel (G.induce p.toSubgraph.verts).Adj := Classical.decRel _
  have hrsize : p.length = c.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
  refine ⟨p.length, hp.three_le_length, hrsize, ?_⟩
  have hpoly := isCycle_induce_charpoly_chebyshev hp hgraph
  let e : p.toSubgraph.verts ≃ c.supp := Equiv.setCongr hpverts
  let M := (G.induce p.toSubgraph.verts).adjMatrix ℤ
  have hM : Matrix.reindex e e M = (G.induce c.supp).adjMatrix ℤ := by
    ext u v
    simp [M, e, Matrix.reindex_apply, SimpleGraph.adjMatrix_apply]
  calc
    ((G.induce c.supp).adjMatrix ℤ).charpoly =
        (Matrix.reindex e e M).charpoly := congrArg Matrix.charpoly hM.symm
    _ = M.charpoly := Matrix.charpoly_reindex e M
    _ = Polynomial.Chebyshev.C ℤ (p.length : ℤ) - 2 := hpoly

end

end Erdos85

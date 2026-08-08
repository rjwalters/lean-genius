import Proofs.Erdos85CycleCharpoly

namespace Erdos85

open SimpleGraph

theorem isCycle_toSubgraph_coe_eq_induce_of_degree_two
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {x : V} {p : G.Walk x x} (hp : p.IsCycle)
    (hdeg : ∀ v ∈ p.toSubgraph.verts, G.degree v = 2) :
    p.toSubgraph.coe = G.induce p.toSubgraph.verts := by
  ext u v
  simp only [Subgraph.coe_adj, induce_adj]
  constructor
  · exact p.toSubgraph.adj_sub
  · intro huv
    have hu : u.val ∈ p.support := by
      simpa [Walk.mem_verts_toSubgraph] using u.property
    have hsub : p.toSubgraph.neighborSet u.val ⊆ G.neighborSet u.val :=
      p.toSubgraph.neighborSet_subset u.val
    have hpcard : (p.toSubgraph.neighborSet u.val).ncard = 2 :=
      hp.ncard_neighborSet_toSubgraph_eq_two hu
    have hGcard : (G.neighborSet u.val).ncard = 2 := by
      rw [← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree,
        hdeg u.val u.property]
    have heq : p.toSubgraph.neighborSet u.val = G.neighborSet u.val :=
      Set.eq_of_subset_of_ncard_le hsub (by omega)
    have hvG : v.val ∈ G.neighborSet u.val := huv
    have hvp : v.val ∈ p.toSubgraph.neighborSet u.val := by
      rw [heq]
      exact hvG
    exact hvp

theorem secondOrderDefect_component_induce_eq_cycleSubgraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ∃ (x : V) (p : (secondOrderDefectGraph G).Walk x x),
      p.IsCycle ∧ p.toSubgraph.verts = c.supp ∧
      p.toSubgraph.coe =
        (secondOrderDefectGraph G).induce p.toSubgraph.verts := by
  obtain ⟨x, hx⟩ := c.nonempty_supp
  obtain ⟨p, hp, hpverts⟩ := exists_secondOrderDefect_cycle_spanning_component
    G hfree hd heven hmin hcard c hx
  refine ⟨x, p, hp, hpverts, ?_⟩
  apply isCycle_toSubgraph_coe_eq_induce_of_degree_two hp
  intro v hv
  exact secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard v

theorem isCycle_induce_charpoly_chebyshev
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {x : V} {p : G.Walk x x} (hp : p.IsCycle)
    [Fintype p.toSubgraph.verts] [DecidableRel p.toSubgraph.coe.Adj]
    [DecidableRel (G.induce p.toSubgraph.verts).Adj]
    (hgraph : p.toSubgraph.coe =
      G.induce p.toSubgraph.verts) :
    ((G.induce p.toSubgraph.verts).adjMatrix ℤ).charpoly =
      Polynomial.Chebyshev.C ℤ (p.length : ℤ) - 2 := by
  have hadj : (G.induce p.toSubgraph.verts).adjMatrix ℤ =
      p.toSubgraph.coe.adjMatrix ℤ := by
    ext u v
    simp only [SimpleGraph.adjMatrix_apply]
    have huv := congrArg
      (fun H : SimpleGraph p.toSubgraph.verts ↦ H.Adj u v) hgraph
    by_cases h : p.toSubgraph.coe.Adj u v <;> simp_all
  rw [hadj, isCycle_charpoly_adjMatrix_eq_cycleGraph hp]
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 3 := by
    exact ⟨p.length - 3, by have := hp.three_le_length; omega⟩
  rw [hn]
  exact cycleGraph_charpoly_eq_chebyshev_C_sub_two n

theorem induce_resolvent_det_eq_of_set_eq
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {s t : Set V}
    [Fintype s] [Fintype t] [DecidableRel (G.induce s).Adj]
    [DecidableRel (G.induce t).Adj] (h : s = t) (a : ℤ) :
    Matrix.det (Matrix.diagonal (fun _ : s ↦ a) - (G.induce s).adjMatrix ℤ) =
      Matrix.det (Matrix.diagonal (fun _ : t ↦ a) - (G.induce t).adjMatrix ℤ) := by
  let e : s ≃ t := Equiv.setCongr h
  let M : Matrix s s ℤ := Matrix.diagonal (fun _ ↦ a) - (G.induce s).adjMatrix ℤ
  have hM : Matrix.reindex e e M =
      Matrix.diagonal (fun _ ↦ a) - (G.induce t).adjMatrix ℤ := by
    ext u v
    simp [M, Matrix.reindex_apply, e, SimpleGraph.adjMatrix_apply,
      Matrix.diagonal_apply]
    simp [Subtype.ext_iff]
  calc
    Matrix.det M = Matrix.det (Matrix.reindex e e M) :=
      (Matrix.det_reindex_self e M).symm
    _ = Matrix.det (Matrix.diagonal (fun _ : t ↦ a) - (G.induce t).adjMatrix ℤ) :=
      congrArg Matrix.det hM

theorem secondOrderDefect_component_resolvent_chebyshev
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj] [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree) (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (a : ℤ) :
    ∃ r : ℕ, 3 ≤ r ∧ r = c.supp.ncard ∧
      Matrix.det (Matrix.diagonal (fun _ : c.supp ↦ a) -
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ) =
        (Polynomial.Chebyshev.C ℤ (r : ℤ) - 2).eval a := by
  obtain ⟨x, p, hp, hpverts, hgraph⟩ :=
    secondOrderDefect_component_induce_eq_cycleSubgraph
      G hfree hd heven hmin hcard c
  letI : Fintype p.toSubgraph.verts := Fintype.ofFinite _
  letI : DecidableRel p.toSubgraph.coe.Adj := Classical.decRel _
  letI : DecidableRel ((secondOrderDefectGraph G).induce p.toSubgraph.verts).Adj :=
    Classical.decRel _
  have hrsize : p.length = c.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts := (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
  refine ⟨p.length, hp.three_le_length, hrsize, ?_⟩
  have hpoly := isCycle_induce_charpoly_chebyshev hp hgraph
  have htrans := induce_resolvent_det_eq_of_set_eq
    (G := secondOrderDefectGraph G) hpverts a
  rw [← htrans]
  have hdiag : Matrix.diagonal (fun _ : p.toSubgraph.verts ↦ a) =
      Matrix.scalar p.toSubgraph.verts a := by
    rfl
  rw [hdiag, ← Matrix.eval_charpoly, hpoly]

end Erdos85

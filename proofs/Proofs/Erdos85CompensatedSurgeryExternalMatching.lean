import Proofs.Erdos85DistanceLayers
import Proofs.Erdos85ControlledDeletion
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# The external matching half of compensated plateau surgery

The degree-compensation matching required by the tight delete-one/add-two
normal form is automatic.  The genuinely open part of that construction is
the balanced bipartite colouring of the retained common-neighbour conflict
graph, not existence of enough disjoint survivor edges.
-/

open SimpleGraph

namespace Erdos85

/-- A finite graph of minimum degree at least `d-1` contains a matching
covering at least `d` vertices, provided `d` is even and the graph has at
least `d` vertices.

This is the maximal-matching argument used by the compensated-surgery
scaling reduction: if a maximal matching covered fewer than `d` vertices,
evenness would make it cover at most `d-2`; an uncovered vertex would then
have all of its at least `d-1` neighbours among those covered vertices. -/
theorem exists_matching_card_verts_ge_of_even_minDegree_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] {d : ℕ}
    (hd : 2 ≤ d) (heven : Even d) (hcard : d ≤ Fintype.card V)
    (hmin : d - 1 ≤ H.minDegree) :
    ∃ M : H.Subgraph, M.IsMatching ∧ d ≤ M.verts.ncard := by
  classical
  let C : Finset H.Subgraph := Finset.univ.filter Subgraph.IsMatching
  have hC : C.Nonempty := by
    refine ⟨⊥, ?_⟩
    simp [C, Subgraph.IsMatching]
  obtain ⟨M, hMC, hmax⟩ :=
    Finset.exists_max_image C (fun N : H.Subgraph => N.verts.ncard) hC
  have hMmatching : M.IsMatching := by
    simpa [C] using (Finset.mem_filter.mp hMC).2
  refine ⟨M, hMmatching, ?_⟩
  by_contra hnot
  have hMlt : M.verts.ncard < d := Nat.lt_of_not_ge hnot
  have hMeven : Even M.verts.ncard := by
    letI : Fintype M.verts := Fintype.ofFinite _
    simpa [Set.ncard_eq_toFinset_card] using hMmatching.even_card
  have hMle : M.verts.ncard ≤ d - 2 := by
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hMeven
    omega
  have hproper : M.verts.ncard < Fintype.card V := hMlt.trans_le hcard
  obtain ⟨u, huM⟩ : ∃ u : V, u ∉ M.verts := by
    by_contra hall
    push Not at hall
    have hverts : M.verts = Set.univ := Set.eq_univ_of_forall hall
    simpa [hverts] using hproper
  have huDegree : d - 1 ≤ H.degree u :=
    hmin.trans (H.minDegree_le_degree u)
  have hneighbors : H.neighborSet u ⊆ M.verts := by
    intro v hv
    have huv : H.Adj u v := hv
    by_contra hvM
    have hdisj : Disjoint M.support (H.subgraphOfAdj huv).support := by
      rw [hMmatching.support_eq_verts, Set.disjoint_left]
      intro z hzM hzE
      have hedgeMatching := Subgraph.IsMatching.subgraphOfAdj huv
      rw [hedgeMatching.support_eq_verts, SimpleGraph.subgraphOfAdj_verts] at hzE
      have hzpair : z = u ∨ z = v := by
        simpa [eq_comm] using hzE
      rcases hzpair with rfl | rfl
      · exact huM hzM
      · exact hvM hzM
    have hsupMatching : (M ⊔ H.subgraphOfAdj huv).IsMatching :=
      hMmatching.sup (Subgraph.IsMatching.subgraphOfAdj huv) hdisj
    have hsupC : M ⊔ H.subgraphOfAdj huv ∈ C := by
      simp [C, hsupMatching]
    have hstrict : M.verts.ncard <
        (M ⊔ H.subgraphOfAdj huv).verts.ncard := by
      rw [Subgraph.verts_sup]
      have huE : u ∈ (H.subgraphOfAdj huv).verts := by
        rw [SimpleGraph.subgraphOfAdj_verts]
        simp
      have huUnion : u ∈ M.verts ∪ (H.subgraphOfAdj huv).verts := Or.inr huE
      apply Set.ncard_lt_ncard (ht := Set.toFinite _)
      rw [Set.ssubset_iff_subset_ne]
      refine ⟨Set.subset_union_left, ?_⟩
      intro heq
      exact huM (heq ▸ huUnion)
    exact (Nat.not_lt_of_ge (hmax _ hsupC)) hstrict
  have hdegreeCard : H.degree u ≤ M.verts.ncard := by
    have hncard := Set.ncard_le_ncard hneighbors
    change (H.neighborSet u).toFinset.card ≤ M.verts.ncard
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq]
    exact hncard
  omega

/-- In a regular `C₄`-free graph, the vertices outside the closed
neighbourhood of any root contain a matching covering at least `d` vertices
when `d` is even.  Equivalently, this supplies at least `d/2` disjoint
survivor edges for the tight compensated delete-one/add-two construction.

The deliberately weak order hypothesis `2*d+1 ≤ |V|` is far below the
plateau order `d(d-1)+3+e`; it is exactly what is needed to leave at least
`d` vertices after deleting the root and its `d` neighbours. -/
theorem exists_external_matching_card_verts_ge_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d)
    (heven : Even d) (hreg : ∀ v, G.degree v = d)
    (horder : 2 * d + 1 ≤ Fintype.card V) (x : V) :
    let D := insert x (G.neighborFinset x)
    ∃ M : (deleteVertexSetGraph G D).Subgraph,
      M.IsMatching ∧ d ≤ M.verts.ncard := by
  classical
  let D := insert x (G.neighborFinset x)
  let H := deleteVertexSetGraph G D
  have hxN : x ∉ G.neighborFinset x := by simp
  have hDcard : D.card = d + 1 := by
    simp [D, Finset.card_insert_of_notMem hxN,
      G.card_neighborFinset_eq_degree, hreg x]
  have hHcard : Fintype.card {v : V // v ∉ D} = Fintype.card V - (d + 1) := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ D)]
    simp [hDcard]
  have hdH : d ≤ Fintype.card {v : V // v ∉ D} := by
    rw [hHcard]
    omega
  letI : Nonempty {v : V // v ∉ D} :=
    Fintype.card_pos_iff.mp (lt_of_lt_of_le (by omega) hdH)
  have hloss : ∀ v : {v : V // v ∉ D},
      (G.neighborFinset v.1 ∩ D).card ≤ 1 := by
    intro v
    have hvx : v.1 ≠ x := by
      intro hv
      exact v.2 (by simp [D, hv])
    have hvnotAdj : ¬G.Adj v.1 x := by
      intro hvadj
      exact v.2 (by
        simp [D, (G.mem_neighborFinset x v.1).mpr hvadj.symm])
    have hvnotx : x ∉ G.neighborFinset v.1 := by
      simpa [SimpleGraph.mem_neighborFinset] using hvnotAdj
    have hinter : G.neighborFinset v.1 ∩ D =
        G.neighborFinset v.1 ∩ G.neighborFinset x := by
      ext z
      simp only [D, Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hzv, rfl | hzx⟩
        · exact False.elim (hvnotx hzv)
        · exact ⟨hzv, hzx⟩
      · rintro ⟨hzv, hzx⟩
        exact ⟨hzv, Or.inr hzx⟩
    rw [hinter]
    exact common_le_one_of_not_containsC4 hfree v.1 x hvx
  have hHmin : d - 1 ≤ H.minDegree := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree
    intro v
    have hsplit := degree_deleteVertexSetGraph_add G D v
    have hvreg := hreg v.1
    have hvloss := hloss v
    dsimp [H] at hsplit ⊢
    omega
  simpa [D, H] using
    exists_matching_card_verts_ge_of_even_minDegree_pred
      H hd heven hdH hHmin

end Erdos85

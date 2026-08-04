import Proofs.Erdos85Problem
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Edge-minimal witnesses for Erdős Problem 85
-/

open SimpleGraph

namespace Erdos85

theorem degree_le_deleteEdge_degree_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v x : V) :
    G.degree x ≤ (G.deleteEdges {s(u, v)}).degree x + 1 := by
  have hkeep : (G.deleteEdges {s(u, v)}).neighborFinset x =
      (G.neighborFinset x).filter (fun y => s(x, y) ≠ s(u, v)) := by
    ext y
    simp [SimpleGraph.deleteEdges_adj]
  have hdel : ((G.neighborFinset x).filter
      (fun y => s(x, y) = s(u, v))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    have hab : s(x, a) = s(x, b) := ha.2.trans hb.2.symm
    rcases Sym2.eq_iff.mp hab with h | h
    · exact h.2
    · exfalso
      exact (G.ne_of_adj ((G.mem_neighborFinset x a).mp ha.1)) h.2.symm
  rw [degree, degree, hkeep]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset x) (p := fun y => s(x, y) ≠ s(u, v))
  have hnot : (G.neighborFinset x).filter (fun y => ¬s(x, y) ≠ s(u, v)) =
      (G.neighborFinset x).filter (fun y => s(x, y) = s(u, v)) := by
    ext y
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hy, hne⟩
      exact ⟨hy, not_ne_iff.mp hne⟩
    · rintro ⟨hy, heq⟩
      exact ⟨hy, fun hne => hne heq⟩
  rw [hnot] at hpartition
  omega

theorem degree_deleteEdge_eq_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v x : V)
    (hxu : x ≠ u) (hxv : x ≠ v) :
    (G.deleteEdges {s(u, v)}).degree x = G.degree x := by
  rw [degree, degree]
  congr 1
  ext y
  simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
    Set.mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · intro hxy
    refine ⟨hxy, ?_⟩
    intro he
    rcases Sym2.eq_iff.mp he with h | h
    · exact hxu h.1
    · exact hxv h.1

theorem le_minDegree_deleteEdge_of_lt_degrees
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) {d : ℕ}
    (hmin : d ≤ G.minDegree) (hu : d < G.degree u) (hv : d < G.degree v) :
    d ≤ (G.deleteEdges {s(u, v)}).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro x
  by_cases hxu : x = u
  · subst x
    have hdrop := degree_le_deleteEdge_degree_add_one G u v u
    omega
  · by_cases hxv : x = v
    · subst x
      have hdrop := degree_le_deleteEdge_degree_add_one G u v v
      omega
    · rw [degree_deleteEdge_eq_of_ne G u v x hxu hxv]
      exact hmin.trans (G.minDegree_le_degree x)

theorem pred_minDegree_le_deleteEdge_minDegree
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u v : V) :
    G.minDegree - 1 ≤ (G.deleteEdges {s(u, v)}).minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro x
  have hmin := G.minDegree_le_degree x
  have hdrop := degree_le_deleteEdge_degree_add_one G u v x
  omega


/-- Every positive-degree C4-free witness has a spanning subgraph with exactly
the target minimum degree. This is the edge-minimal normalization used in the
C4-versus-star Ramsey literature. -/
theorem exists_spanning_minDegree_eq
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 1 ≤ d) (hmin : d ≤ G.minDegree) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      H ≤ G ∧ H.minDegree = d ∧
      ∀ ⦃u v⦄, H.Adj u v → H.degree u = d ∨ H.degree v = d := by
  classical
  let md (H : SimpleGraph V) : ℕ :=
    @SimpleGraph.minDegree V H _ (Classical.decRel H.Adj)
  let C : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H => d ≤ md H ∧ H ≤ G
  have hGC : G ∈ C := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, le_rfl⟩
    change d ≤ @SimpleGraph.minDegree V G _ (Classical.decRel G.Adj)
    rw [show Classical.decRel G.Adj =
      (inferInstance : DecidableRel G.Adj) from Subsingleton.elim _ _]
    exact hmin
  obtain ⟨H, hHC, hleast⟩ :=
    Finset.exists_min_image C (fun H => H.edgeFinset.card) ⟨G, hGC⟩
  have hprops : d ≤ md H ∧ H ≤ G := by
    simpa [C] using hHC
  letI : DecidableRel H.Adj := Classical.decRel H.Adj
  have hHmin : d ≤ H.minDegree := by simpa [md] using hprops.1
  have hdelete (u v : V) (huv : H.Adj u v)
      (hkeep : d ≤ (H.deleteEdges {s(u, v)}).minDegree) : False := by
    let H' := H.deleteEdges (↑({s(u, v)} : Finset (Sym2 V)))
    letI : DecidableRel H'.Adj := Classical.decRel H'.Adj
    have hH'le : H' ≤ G := (H.deleteEdges_le _).trans hprops.2
    have hH'C : H' ∈ C := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hH'le⟩
      change d ≤ @SimpleGraph.minDegree V H' _ (Classical.decRel H'.Adj)
      rw [show Classical.decRel H'.Adj =
        (inferInstance : DecidableRel H'.Adj) from Subsingleton.elim _ _]
      simpa [H'] using hkeep
    have hcardle := hleast H' hH'C
    have hedge : s(u, v) ∈ H.edgeFinset := by
      simpa [SimpleGraph.mem_edgeFinset] using huv
    have hcardlt : H'.edgeFinset.card < H.edgeFinset.card := by
      rw [show H'.edgeFinset = H.edgeFinset \ {s(u, v)} by
        exact SimpleGraph.edgeFinset_deleteEdges _]
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hedge]
      have := Finset.card_pos.mpr ⟨s(u, v), hedge⟩
      omega
    exact (not_lt_of_ge hcardle) hcardlt
  have hdegree : H.minDegree = d := by
    apply le_antisymm
    · by_contra hnot
      have hstrict : d < H.minDegree := by omega
      have hne : H ≠ ⊥ := by
        intro heq
        have : d ≤ 0 := by simpa [heq] using hHmin
        omega
      obtain ⟨u, v, huv⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hne
      apply hdelete u v huv
      have hpred := pred_minDegree_le_deleteEdge_minDegree H u v
      omega
    · exact hHmin
  refine ⟨H, inferInstance, hprops.2, hdegree, ?_⟩
  intro u v huv
  by_contra htight
  push Not at htight
  have huMin := hHmin.trans (H.minDegree_le_degree u)
  have hvMin := hHmin.trans (H.minDegree_le_degree v)
  have hu : d < H.degree u := lt_of_le_of_ne huMin (Ne.symm htight.1)
  have hv : d < H.degree v := lt_of_le_of_ne hvMin (Ne.symm htight.2)
  exact hdelete u v huv (le_minDegree_deleteEdge_of_lt_degrees H u v hHmin hu hv)

/-- Exact-degree normalization preserves C4-freeness. -/

theorem not_adj_of_lt_degrees_of_edgeCovered
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hcover : ∀ ⦃u v⦄, G.Adj u v →
      G.degree u = d ∨ G.degree v = d)
    {u v : V} (hu : d < G.degree u) (hv : d < G.degree v) :
    ¬ G.Adj u v := by
  intro huv
  rcases hcover huv with huEq | hvEq <;> omega

/-- A C4-free witness can be normalized so its degree-d vertices cover every
edge; equivalently, all vertices above minimum degree form an independent
set. -/
theorem exists_c4Free_edgeCovered_minDegree_eq
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 1 ≤ d) (hmin : d ≤ G.minDegree)
    (hfree : ¬ containsC4 V G) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      H.minDegree = d ∧
      ¬ containsC4 V H ∧
      ∀ ⦃u v⦄, H.Adj u v → H.degree u = d ∨ H.degree v = d := by
  obtain ⟨H, hdec, hle, hdegree, hcover⟩ :=
    exists_spanning_minDegree_eq G hd hmin
  exact ⟨H, hdec, hdegree, fun h => hfree (containsC4_mono hle h), hcover⟩

/-- At every order n at least four, a top-degree witness can be chosen with
the tight vertices covering all edges. -/
theorem exists_top_edgeCovered_exact_minDegree {n : ℕ} (hn : 4 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.minDegree = minDegreeForC4 n - 1 ∧
      ¬ containsC4 (Fin n) G ∧
      ∀ ⦃u v⦄, G.Adj u v →
        G.degree u = minDegreeForC4 n - 1 ∨
        G.degree v = minDegreeForC4 n - 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have htwo : 2 ≤ minDegreeForC4 n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact two_le_minDegreeForC4 (by omega)
  have hw : C4FreeMinDegreeWitness n (minDegreeForC4 n - 1) :=
    (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).2 (by omega)
  obtain ⟨G, hdec, hmin, hfree⟩ := hw
  letI : DecidableRel G.Adj := hdec
  exact exists_c4Free_edgeCovered_minDegree_eq G (by omega) hmin.ge hfree

/-- Exact-degree normalization preserves C4-freeness. -/
theorem exists_c4Free_spanning_minDegree_eq
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : 1 ≤ d) (hmin : d ≤ G.minDegree)
    (hfree : ¬ containsC4 V G) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      H.minDegree = d ∧ ¬ containsC4 V H := by
  obtain ⟨H, hdec, hle, hdegree, _⟩ := exists_spanning_minDegree_eq G hd hmin
  exact ⟨H, hdec, hdegree, fun h => hfree (containsC4_mono hle h)⟩


/-- Witness existence can be normalized to exact minimum degree. -/
theorem c4FreeMinDegreeWitness_iff_exists_exact {n d : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) :
    C4FreeMinDegreeWitness n d ↔
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        G.minDegree = d ∧ ¬ containsC4 (Fin n) G := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  constructor
  · rintro ⟨G, hdec, hmin, hfree⟩
    letI : DecidableRel G.Adj := hdec
    exact exists_c4Free_spanning_minDegree_eq G hd hmin hfree
  · rintro ⟨G, hdec, hdegree, hfree⟩
    exact ⟨G, hdec, hdegree.ge, hfree⟩

/-- At every nontrivial order, the largest admissible degree below the
threshold is realized exactly by an edge-minimal C4-free graph. -/
theorem exists_top_exact_minDegree {n : ℕ} (hn : 4 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
      G.minDegree = minDegreeForC4 n - 1 ∧ ¬ containsC4 (Fin n) G := by
  have htwo : 2 ≤ minDegreeForC4 n := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact two_le_minDegreeForC4 (by omega)
  apply (c4FreeMinDegreeWitness_iff_exists_exact (by omega) (by omega)).mp
  apply (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4 hn).2
  omega


/-- A tight threshold witness has a vertex whose degree is exactly f(n)-1. -/
theorem exists_top_tight_vertex {n : ℕ} (hn : 4 ≤ n) :
    ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (x : Fin n),
      G.minDegree = minDegreeForC4 n - 1 ∧
      G.degree x = minDegreeForC4 n - 1 ∧
      ¬ containsC4 (Fin n) G := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨G, hdec, hdegree, hfree⟩ := exists_top_exact_minDegree hn
  letI : DecidableRel G.Adj := hdec
  obtain ⟨x, hx⟩ := G.exists_minimal_degree_vertex
  exact ⟨G, hdec, x, hdegree, (hdegree ▸ hx).symm, hfree⟩

end Erdos85

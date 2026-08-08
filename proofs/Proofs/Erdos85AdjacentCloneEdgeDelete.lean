import Proofs.Erdos85AdjacentCloneSplit
import Proofs.Erdos85MinimalWitness

/-!
# Breaking a local matching edge before adjacent-clone splitting

At the sharp even-degree obstruction, the graph induced on a critical
neighbourhood is a perfect matching.  If one of its edges has both endpoints
strictly above the target minimum degree, that edge can first be deleted.
The endpoints then become isolated local vertices, removing the parity
obstruction to the adjacent-clone split.
-/

open SimpleGraph

namespace Erdos85

/-- An isolated vertex is the unique vertex in its connected component. -/
theorem connectedComponentMk_supp_ncard_eq_one_of_isIsolated
    {V : Type*} [Finite V] (H : SimpleGraph V) (v : V)
    (hv : H.IsIsolated v) :
    (H.connectedComponentMk v).supp.ncard = 1 := by
  have hsupp : (H.connectedComponentMk v).supp = {v} := by
    ext w
    simp only [ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff,
      ConnectedComponent.eq]
    constructor
    · intro hr
      by_contra hw
      exact (not_reachable_of_neighborSet_right_eq_empty hw
        hv.neighborSet_eq_empty) hr
    · rintro rfl
      exact Reachable.rfl
  rw [hsupp, Set.ncard_singleton]

/-- If `a-b` lies inside `N(x)` and both endpoints have degree strictly above
`d`, delete `a-b` and then perform the sharp adjacent-clone split at `x`.
The deletion preserves minimum degree, while `a` becomes an isolated local
vertex and removes the last parity obstruction at degree `2*d-2`. -/
theorem c4FreeMinDegreeWitness_succ_of_threshold_localEdge_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x a b : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hxdegree : 2 * d - 2 ≤ G.degree x)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hab : G.Adj a b)
    (haHigh : d < G.degree a) (hbHigh : d < G.degree b) :
    C4FreeMinDegreeWitness (N + 1) d := by
  classical
  let G' : SimpleGraph V := G.deleteEdges {s(a, b)}
  letI : Nonempty V := ⟨x⟩
  have haxb : x ≠ b := (G.ne_of_adj hbx).symm
  have haxa : x ≠ a := (G.ne_of_adj hax).symm
  have habx : a ≠ x := G.ne_of_adj hax
  have hedgeAX : s(a, x) ≠ s(a, b) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with h | h
    · exact haxb h.2
    · exact (G.ne_of_adj hab) h.1
  have hax' : G'.Adj a x := by
    rw [show G' = G.deleteEdges {s(a, b)} from rfl,
      SimpleGraph.deleteEdges_adj]
    exact ⟨hax, by simpa using hedgeAX⟩
  have hmin' : d ≤ G'.minDegree := by
    simpa [G'] using
      (le_minDegree_deleteEdge_of_lt_degrees G a b hmin haHigh hbHigh)
  have hfree' : ¬ containsC4 V G' := by
    intro hc4
    exact hfree (containsC4_mono (G.deleteEdges_le _) hc4)
  have hxdegree' : 2 * d - 2 ≤ G'.degree x := by
    rw [show G'.degree x = G.degree x by
      simpa [G'] using degree_deleteEdge_eq_of_ne G a b x haxa haxb]
    exact hxdegree
  let a0 : {v : V // v ≠ x} := ⟨a, habx⟩
  let aN : {y : {v : V // v ≠ x} //
      y ∈ (deletedNeighborhood G' x : Set {v : V // v ≠ x})} :=
    ⟨a0, (mem_deletedNeighborhood G' x a0).2 hax'⟩
  have haIsolated : (deletedNeighborhoodInducedGraph G' x).IsIsolated aN := by
    intro y hay
    have hay' : G'.Adj a y.1.1 := hay
    have hayG : G.Adj a y.1.1 :=
      (SimpleGraph.deleteEdges_adj.mp hay').1
    have hyb : y.1.1 ≠ b := by
      intro hyb
      exact (SimpleGraph.deleteEdges_adj.mp hay').2 (by simp [hyb])
    have hyx' : G'.Adj y.1.1 x :=
      (mem_deletedNeighborhood G' x y.1).1 y.2
    have hyxG : G.Adj y.1.1 x :=
      (SimpleGraph.deleteEdges_adj.mp hyx').1
    exact hfree (containsC4_of_two_common habx hyb
      hayG.symm hyxG hab.symm hbx)
  have hsingleton :
      ∃ c : (deletedNeighborhoodInducedGraph G' x).ConnectedComponent,
        c.supp.ncard = 1 := by
    exact ⟨(deletedNeighborhoodInducedGraph G' x).connectedComponentMk aN,
      connectedComponentMk_supp_ncard_eq_one_of_isIsolated
        (deletedNeighborhoodInducedGraph G' x) aN haIsolated⟩
  exact
    c4FreeMinDegreeWitness_succ_of_vertex_degree_ge_two_mul_sub_two_of_localSingleton
      G' x hVcard hmin' hfree' hd hxdegree' hsingleton

/-- In a nonextendable witness, every edge in a threshold neighbourhood has
at least one endpoint of minimum degree.  This is the local vertex-cover
rigidity forced by failure of both edge deletion and adjacent cloning. -/
theorem threshold_localEdge_has_tight_endpoint_of_not_witness_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x a b : V)
    {N d : ℕ} (hVcard : Fintype.card V = N)
    (hmin : d ≤ G.minDegree) (hfree : ¬ containsC4 V G)
    (hd : 1 ≤ d) (hno : ¬ C4FreeMinDegreeWitness (N + 1) d)
    (hxdegree : 2 * d - 2 ≤ G.degree x)
    (hax : G.Adj a x) (hbx : G.Adj b x) (hab : G.Adj a b) :
    G.degree a = d ∨ G.degree b = d := by
  have haMin : d ≤ G.degree a := hmin.trans (G.minDegree_le_degree a)
  have hbMin : d ≤ G.degree b := hmin.trans (G.minDegree_le_degree b)
  by_contra htight
  push Not at htight
  exact hno
    (c4FreeMinDegreeWitness_succ_of_threshold_localEdge_excess
      G x a b hVcard hmin hfree hd hxdegree hax hbx hab
        (lt_of_le_of_ne haMin (Ne.symm htight.1))
        (lt_of_le_of_ne hbMin (Ne.symm htight.2)))

end Erdos85

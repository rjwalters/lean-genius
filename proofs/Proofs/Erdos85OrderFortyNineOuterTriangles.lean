import Proofs.Erdos85SquareOrderOuterGraph
import Proofs.Erdos85OrderFortyNineLowTriangles

/-!
# Forced triangles in the order-49 outer graph

In the unique-high sector, an outer vertex which is unmatched inside its
five-vertex high-root branch cannot use the parent triangle supplied by the
general all-low-triangle theorem.  Its forced triangle therefore lies
entirely in the 40-vertex outer graph.  This is the graph-facing coverage
condition used by the reduced branch-holonomy formulation.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An outer vertex not incident with an internal branch edge belongs to a
triangle entirely inside the outer graph. -/
theorem orderFortyNine_exists_outer_triangle_of_uniqueHigh_unmatched
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {v : V}
    (hv : G.degree v = 8)
    (hunique : ∀ {w : V}, G.degree w = 8 → w = v)
    (x : {x : V // x ∈ secondLayer G v})
    (s : {z : V // z ∈ G.neighborSet v})
    (hxs : x.1 ∈ secondLayerBranch G v s)
    (hunmatched :
      (G.neighborFinset x.1 ∩ secondLayerBranch G v s).card = 0) :
    ∃ y z : {x : V // x ∈ secondLayer G v},
      (squareOrderOuterGraph G v).Adj x y ∧
      (squareOrderOuterGraph G v).Adj x z ∧
      (squareOrderOuterGraph G v).Adj y z := by
  classical
  have hxOutside : x.1 ∉ insert v (G.neighborFinset v) :=
    (Finset.mem_sdiff.mp hxs).2
  have hxv : x.1 ≠ v := by
    intro hxv
    exact hxOutside (by simp [hxv])
  have hx7 : G.degree x.1 = 7 := by
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard x.1 with hx | hx
    · exact hx
    · exact (hxv (hunique hx)).elim
  have hkzero :
      (G.neighborFinset x.1 ∩ orderFortyNineHighVertices G).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hw8 : G.degree w = 8 :=
      (Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2
    have hwv : w = v := hunique hw8
    have hxw : G.Adj x.1 w := by
      simpa [SimpleGraph.mem_neighborFinset] using
        (Finset.mem_inter.mp hw).1
    subst w
    exact hxOutside (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr hxw.symm)
  rcases orderFortyNine_exists_allLow_triangle_of_highNeighborCount_zero
    G hfree hmin hcard hx7 hkzero with
      ⟨y, z, hy7, hz7, hxy, hxz, hyz⟩
  have hstructure := squareOrder_degree_succ_highRoot_structure
    G hfree (by omega : 2 ≤ 7) hmin (by simpa using hcard) hv
  have hexternal := externalRepairCandidates_eq_empty_of_squareOrder_highRoot
    G hfree (by omega : 2 ≤ 7) (by simpa using hcard) hv
      hstructure.2.1 hstructure.2.2
  have hneighbor_location : ∀ {q : V}, G.Adj x.1 q →
      q ∈ G.neighborFinset v ∨ q ∈ secondLayer G v := by
    intro q hxq
    have hq : q ∈ (Finset.univ : Finset V) := by simp
    have hpartition :=
      closedNeighborhood_union_secondLayer_union_external_eq_univ G v
    rw [← hpartition, hexternal] at hq
    simp only [Finset.map_empty, Finset.union_empty, Finset.mem_union,
      Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hq
    rcases hq with (hqv | hqN) | hqSecond
    · subst q
      exact (hxOutside (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr hxq.symm)).elim
    · exact Or.inl ((G.mem_neighborFinset v q).mpr hqN)
    · exact Or.inr hqSecond
  have hparent_unique : ∀ {q : V}, q ∈ G.neighborFinset v →
      G.Adj x.1 q → q = s.1 := by
    intro q hqN hxq
    let t : {z : V // z ∈ G.neighborSet v} :=
      ⟨q, (G.mem_neighborFinset v q).mp hqN⟩
    have hxt : x.1 ∈ secondLayerBranch G v t := by
      apply Finset.mem_sdiff.mpr
      exact ⟨(G.mem_neighborFinset q x.1).mpr hxq.symm, hxOutside⟩
    have hts : t = s := by
      by_contra hne
      have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
        (by simp : t ∈ (Finset.univ : Finset _))
        (by simp : s ∈ (Finset.univ : Finset _)) hne
      exact (Finset.disjoint_left.mp hdisj) hxt hxs
    exact congrArg Subtype.val hts
  have hsecond_outside : ∀ {q : V}, q ∈ secondLayer G v →
      q ∉ insert v (G.neighborFinset v) := by
    intro q hqSecond
    rw [secondLayer] at hqSecond
    rcases Finset.mem_biUnion.mp hqSecond with ⟨u, _, hqu⟩
    exact (Finset.mem_sdiff.mp hqu).2
  have hyOuter : y ∈ secondLayer G v := by
    rcases hneighbor_location hxy with hyN | hySecond
    · have hys : y = s.1 := hparent_unique hyN hxy
      have hzOuter : z ∈ secondLayer G v := by
        rcases hneighbor_location hxz with hzN | hzSecond
        · have hzs : z = s.1 := hparent_unique hzN hxz
          subst y
          subst z
          exact (G.loopless.irrefl s.1 hyz).elim
        · exact hzSecond
      have hzsBranch : z ∈ secondLayerBranch G v s := by
        apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset s.1 z).mpr ?_, ?_⟩
        · simpa [hys] using hyz
        · exact hsecond_outside hzOuter
      have hzx : z ∈ G.neighborFinset x.1 ∩ secondLayerBranch G v s :=
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset x.1 z).mpr hxz, hzsBranch⟩
      rw [Finset.card_eq_zero] at hunmatched
      rw [hunmatched] at hzx
      exact (Finset.notMem_empty z hzx).elim
    · exact hySecond
  have hzOuter : z ∈ secondLayer G v := by
    rcases hneighbor_location hxz with hzN | hzSecond
    · have hzs : z = s.1 := hparent_unique hzN hxz
      have hysBranch : y ∈ secondLayerBranch G v s := by
        apply Finset.mem_sdiff.mpr
        refine ⟨(G.mem_neighborFinset s.1 y).mpr ?_, ?_⟩
        · simpa [hzs] using hyz.symm
        · exact hsecond_outside hyOuter
      have hyx : y ∈ G.neighborFinset x.1 ∩ secondLayerBranch G v s :=
        Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset x.1 y).mpr hxy, hysBranch⟩
      rw [Finset.card_eq_zero] at hunmatched
      rw [hunmatched] at hyx
      exact (Finset.notMem_empty y hyx).elim
    · exact hzSecond
  let y' : {x : V // x ∈ secondLayer G v} := ⟨y, hyOuter⟩
  let z' : {x : V // x ∈ secondLayer G v} := ⟨z, hzOuter⟩
  exact ⟨y', z', hxy, hxz, hyz⟩

end

end Erdos85

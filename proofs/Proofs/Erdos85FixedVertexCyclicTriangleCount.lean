import Proofs.Erdos85MultiComponentTriangleIncidenceCount

/-!
# Fixed-vertex ordered triangle count

The ordered cyclic triangles with fixed first vertex are the directed edges
of the graph induced on that vertex's neighborhood.  Hence their number is
twice the local neighbor-edge count.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem card_cyclicTriangles_filter_first_eq_two_mul_localEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    ((cyclicColoredTriples G G G).filter fun p => p.1 = x).card =
      2 * (G.induce (G.neighborSet x)).edgeFinset.card := by
  classical
  let U := {y : V // y ∈ G.neighborSet x}
  let H := G.induce (G.neighborSet x)
  let E := (Finset.univ : Finset (U × U)).filter fun uv => H.Adj uv.1 uv.2
  have hfiberE :
      ((cyclicColoredTriples G G G).filter fun p => p.1 = x).card = E.card := by
    apply Finset.card_bij (fun p hp => by
      have htri := (Finset.mem_filter.mp hp).1
      have hfirst := (Finset.mem_filter.mp hp).2
      simp only [cyclicColoredTriples, Finset.mem_filter,
        Finset.mem_univ, true_and] at htri
      refine (⟨p.2.1, ?_⟩, ⟨p.2.2, ?_⟩)
      · rw [SimpleGraph.mem_neighborSet, ← hfirst]
        exact htri.2.2.symm
      · rw [SimpleGraph.mem_neighborSet, ← hfirst]
        exact htri.1)
    · intro p hp
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and]
      have htri := (Finset.mem_filter.mp hp).1
      simp only [cyclicColoredTriples, Finset.mem_filter,
        Finset.mem_univ, true_and] at htri
      exact htri.2.1.symm
    · intro p hp q hq heq
      have hpfirst := (Finset.mem_filter.mp hp).2
      have hqfirst := (Finset.mem_filter.mp hq).2
      apply Prod.ext
      · exact hpfirst.trans hqfirst.symm
      · apply Prod.ext
        · exact congrArg (fun uv : U × U => uv.1.1) heq
        · exact congrArg (fun uv : U × U => uv.2.1) heq
    · intro uv huv
      simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at huv
      let p : V × V × V := (x, uv.1.1, uv.2.1)
      refine ⟨p, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        constructor
        · simp only [cyclicColoredTriples, Finset.mem_filter,
            Finset.mem_univ, true_and]
          have hu : G.Adj x uv.1.1 := by
            have huMem := uv.1.2
            change G.Adj x uv.1.1 at huMem
            exact huMem
          have hv : G.Adj x uv.2.1 := by
            have hvMem := uv.2.2
            change G.Adj x uv.2.1 at hvMem
            exact hvMem
          exact ⟨hv, huv.symm, hu.symm⟩
        · rfl
      · apply Prod.ext
        · apply Subtype.ext
          rfl
        · apply Subtype.ext
          rfl
  rw [hfiberE]
  have hhand := H.two_mul_card_edgeFinset
  change 2 * H.edgeFinset.card = E.card at hhand
  exact hhand.symm

/-- At degree eight with triangle-free degree two, every vertex is the first
coordinate of exactly six ordered cyclic triangles. -/
theorem card_cyclicTriangles_filter_first_eq_six_of_degree_eight_tfdegree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (x : V)
    (hdegree : G.degree x = 8)
    (htfdegree : (triangleFreeEdgeGraph G).degree x = 2) :
    ((cyclicColoredTriples G G G).filter fun p => p.1 = x).card = 6 := by
  rw [card_cyclicTriangles_filter_first_eq_two_mul_localEdges]
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have htfcard : (triangleFreeNeighbors G x).card = 2 := by
    rw [← triangleFreeEdgeGraph_neighborFinset G x,
      SimpleGraph.card_neighborFinset_eq_degree, htfdegree]
  rw [htfcard, hdegree] at hlocal
  omega

/-- The all-internal-triangle-free, triangle-free-degree-two local model in a
two-component order-64 branch forces the mixed-nonambient residue. -/
theorem orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_tfdegree_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = 8 * m c)
    (hsum : ∑ c, m c = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (hinternal : ∀ {x y : V}, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (triangleFreeEdgeGraph G).Adj x y)
    (htfdegree : ∀ x ∈ c.supp,
      (triangleFreeEdgeGraph G).degree x = 2) :
    (192 : ℤ) ∣
      ((literalMixedOwnerNonambientCyclicTriples G).card : ℤ) + 96 := by
  apply orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_localSix
    G hfree hreg hcard m hm hsum hcount c hc hinternal
  intro x hx
  exact card_cyclicTriangles_filter_first_eq_six_of_degree_eight_tfdegree_two
    G hfree x (hreg x) (htfdegree x hx)

end

end Erdos85

#print axioms Erdos85.card_cyclicTriangles_filter_first_eq_two_mul_localEdges
#print axioms
  Erdos85.card_cyclicTriangles_filter_first_eq_six_of_degree_eight_tfdegree_two
#print axioms
  Erdos85.orderSixtyFour_mixedNonambient_add_96_dvd_192_of_twoComponents_tfdegree_two

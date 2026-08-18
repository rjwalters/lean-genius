import Proofs.Erdos85BinarySquareComplementTriangleColorPartition

/-!
# Monochromatic owner triangles inject into defect-complement triangles

Unique ownership of every complement edge makes the owner-monochromatic
triangle families disjoint.  Forgetting the owner color therefore injects
their sigma type into the ordered triangles of the defect complement.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The sum of ordered monochromatic owner-triangle counts is bounded by all
ordered triangles in the complement of the defect graph. -/
theorem sum_card_componentOwner_cyclicTriples_le_defectComplement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      (cyclicColoredTriples
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)).card) ≤
      (cyclicColoredTriples
        (secondOrderDefectGraph G)ᶜ
        (secondOrderDefectGraph G)ᶜ
        (secondOrderDefectGraph G)ᶜ).card := by
  classical
  let D := secondOrderDefectGraph G
  let S := Finset.univ.sigma fun c : D.ConnectedComponent =>
    cyclicColoredTriples (componentOwnerGraph G D c)
      (componentOwnerGraph G D c) (componentOwnerGraph G D c)
  let T := cyclicColoredTriples Dᶜ Dᶜ Dᶜ
  rw [← Finset.card_sigma]
  change S.card ≤ T.card
  refine Finset.card_le_card_of_injOn (s := S) (t := T)
    (fun q => q.2) ?_ ?_
  · intro q hq
    change q ∈ S at hq
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hq
    change q.2 ∈ T
    simp only [T, cyclicColoredTriples, Finset.mem_filter,
      Finset.mem_univ, true_and] at hq ⊢
    rcases hq with ⟨hxy, hyz, hzx⟩
    have hnot (x y : V) (hxyO : (componentOwnerGraph G D q.1).Adj x y) :
        ¬ D.Adj x y := by
      intro hD
      have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
        G hfree hD q.1
      have hdata := (componentOwnerGraph_adj G D q.1 x y).mp hxyO
      obtain ⟨z, hz⟩ := hdata.2
      have hz' := Finset.mem_inter.mp hz
      exact (Finset.disjoint_left.mp hdis)
        hz'.1 hz'.2
    exact ⟨⟨hxy.ne, hnot q.2.1 q.2.2.2 hxy⟩,
      ⟨hyz.ne, hnot q.2.2.2 q.2.2.1 hyz⟩,
      ⟨hzx.ne, hnot q.2.2.1 q.2.1 hzx⟩⟩
  · intro q hq r hr heq
    change q ∈ S at hq
    change r ∈ S at hr
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hq hr
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq hr
    have hqedge : (componentOwnerGraph G D q.1).Adj q.2.1 q.2.2.2 := by
      exact hq.1
    have hredge : (componentOwnerGraph G D r.1).Adj r.2.1 r.2.2.2 := by
      exact hr.1
    have hcolor : q.1 = r.1 := by
      have hnot : ¬ D.Adj q.2.1 q.2.2.2 := by
        intro hD
        have hdis := componentNeighborFinset_disjoint_of_secondOrderDefect_adj
          G hfree hD q.1
        have hdata := (componentOwnerGraph_adj G D q.1 _ _).mp hqedge
        obtain ⟨z, hz⟩ := hdata.2
        have hz' := Finset.mem_inter.mp hz
        exact (Finset.disjoint_left.mp hdis)
          hz'.1 hz'.2
      obtain ⟨c, hc, huniq⟩ :=
        (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
          G hfree hqedge.ne).mp hnot
      exact (huniq q.1 hqedge).trans
        (huniq r.1 (by
          change q.2 = r.2 at heq
          rw [← heq] at hredge
          exact hredge)).symm
    cases q with
    | mk qc qp =>
      cases r with
      | mk rc rp =>
        simp only at hcolor heq
        subst rc
        cases heq
        rfl

/-- **Literal nonnegativity of the mixed-owner triangle deficit.** -/
theorem sum_componentOwner_triangleMinorCount_le_defectComplement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcard : 3 ≤ Fintype.card V) :
    (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      (adjacencyTriangleMinorFinset
        (componentOwnerGraph G (secondOrderDefectGraph G) c)).card) ≤
      (adjacencyTriangleMinorFinset (secondOrderDefectGraph G)ᶜ).card := by
  have hordered := sum_card_componentOwner_cyclicTriples_le_defectComplement
    G hfree
  have howner : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      (cyclicColoredTriples
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)).card =
        6 * (adjacencyTriangleMinorFinset
          (componentOwnerGraph G (secondOrderDefectGraph G) c)).card := by
    intro c
    have ht := trace_three_adjMatrices_eq_card_cyclicColoredTriples
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
    have hc := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
      (componentOwnerGraph G (secondOrderDefectGraph G) c) hcard
    rw [hc] at ht
    norm_cast at ht
    omega
  have hcompl :
      (cyclicColoredTriples
        (secondOrderDefectGraph G)ᶜ
        (secondOrderDefectGraph G)ᶜ
        (secondOrderDefectGraph G)ᶜ).card =
        6 * (adjacencyTriangleMinorFinset (secondOrderDefectGraph G)ᶜ).card := by
    have ht := trace_three_adjMatrices_eq_card_cyclicColoredTriples
      (secondOrderDefectGraph G)ᶜ (secondOrderDefectGraph G)ᶜ
      (secondOrderDefectGraph G)ᶜ
    have hc := trace_adjMatrix_cube_eq_six_mul_triangleMinorCount
      (secondOrderDefectGraph G)ᶜ hcard
    rw [hc] at ht
    norm_cast at ht
    omega
  simp_rw [howner] at hordered
  rw [hcompl, ← Finset.mul_sum] at hordered
  omega

end


end Erdos85

#print axioms
  Erdos85.sum_card_componentOwner_cyclicTriples_le_defectComplement
#print axioms
  Erdos85.sum_componentOwner_triangleMinorCount_le_defectComplement

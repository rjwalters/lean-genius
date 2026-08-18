import Proofs.Erdos85BinarySquareExactAdjacencyKernel

/-! # The unique owner graph in the connected-defect stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- When the second-order defect graph is connected, its unique component
owner graph is exactly the simple-graph complement of the defect graph.  This
turns the `[8]` owner-density terminal into a direct defect/operator identity. -/
theorem componentOwnerGraph_eq_compl_secondOrderDefect_of_oneComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1)
    (a : (secondOrderDefectGraph G).ConnectedComponent) :
    componentOwnerGraph G (secondOrderDefectGraph G) a =
      (secondOrderDefectGraph G)ᶜ := by
  classical
  haveI hsub : Subsingleton
      (secondOrderDefectGraph G).ConnectedComponent :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  ext x y
  by_cases hxy : x = y
  · subst y
    simp
  · rw [SimpleGraph.compl_adj]
    rw [and_iff_right hxy]
    constructor
    · intro howner hdefect
      have hunique :=
        (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
          G hfree hxy).mpr
          ⟨a, howner, fun c _ => Subsingleton.elim c a⟩
      exact hunique hdefect
    · intro hnot
      obtain ⟨c, hc, _⟩ :=
        (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
          G hfree hxy).mp hnot
      simpa [Subsingleton.elim c a] using hc

/-- In the connected-defect stratum the sole centered owner Gram is not just
isospectral to the defect Laplacian: after the owner-complement identification
it is literally `q` times that Laplacian. -/
theorem centeredOwnerGram_eq_q_smul_defect_lapMatrix_of_oneComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1)
    (a : (secondOrderDefectGraph G).ConnectedComponent) :
    (q : ℤ) •
        ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ +
          (q : ℤ) • (1 : Matrix V V ℤ)) -
      (q : ℤ) • FriendshipTheoremOQ01.onesMatrix V =
        (q : ℤ) • (secondOrderDefectGraph G).lapMatrix ℤ := by
  let D := secondOrderDefectGraph G
  have hDdegree : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
      rw [hcard]
      calc
        q * q = q * ((q - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
        _ = q * (q - 1) + q := by ring
        _ = q * (q - 1) + 3 + (q - 3) := by omega
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have hOeq := componentOwnerGraph_eq_compl_secondOrderDefect_of_oneComponent
    G hfree hcount a
  have hAdj :
      (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ =
        Dᶜ.adjMatrix ℤ := by
    ext x y
    have hOadj :
        (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y ↔
          Dᶜ.Adj x y := by rw [hOeq]
    by_cases h₁ :
        (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y
    · have h₂ : Dᶜ.Adj x y := hOadj.mp h₁
      simp only [SimpleGraph.adjMatrix_apply]
      rw [if_pos h₁, if_pos h₂]
    · have h₂ : ¬Dᶜ.Adj x y := fun h => h₁ (hOadj.mpr h)
      simp only [SimpleGraph.adjMatrix_apply]
      rw [if_neg h₁, if_neg h₂]
  rw [hAdj]
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply]
  by_cases hxy : x = y
  · subst y
    have hdeg : (secondOrderDefectGraph G).degree x = q - 1 := by
      simpa [D] using hDdegree x
    simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
      SimpleGraph.adjMatrix_apply, FriendshipTheoremOQ01.onesMatrix, hdeg]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  · by_cases hDxy : D.Adj x y
    · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
        FriendshipTheoremOQ01.onesMatrix, hxy, hDxy, D]
    · simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj,
        FriendshipTheoremOQ01.onesMatrix, hxy, hDxy, D]

/-- The non-tautological ambient companion to `C = q L_D`: connected defect
forces the rational adjacency operator of `G` to have zero nullity. -/
theorem binarySquare_regular_oneComponent_finrank_adj_kernel_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 1)
    (a : (secondOrderDefectGraph G).ConnectedComponent) :
    Module.finrank ℚ (LinearMap.ker (G.adjMatrix ℚ).mulVecLin) = 0 := by
  rw [binarySquare_regular_finrank_adj_kernel_eq_card_components_sub_one
    G hfree hq hreg hcard a, hcount]

end

end Erdos85

#print axioms Erdos85.componentOwnerGraph_eq_compl_secondOrderDefect_of_oneComponent
#print axioms Erdos85.centeredOwnerGram_eq_q_smul_defect_lapMatrix_of_oneComponent
#print axioms Erdos85.binarySquare_regular_oneComponent_finrank_adj_kernel_eq_zero

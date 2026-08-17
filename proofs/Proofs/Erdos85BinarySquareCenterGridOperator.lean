import Proofs.Erdos85BinarySquareCenterGridComplement

/-! # Operator formula for the fourth center-grid factor -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The `A D A` entry is exactly the number of defect edges between the two
ambient root neighborhoods, i.e. the defect-pair part of the center grid. -/
theorem adj_defect_adj_apply_eq_card_crossRootDefectCenterPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (x y : V) :
    (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ *
        G.adjMatrix ℤ) x y =
      ((crossRootDefectCenterPairs G x y).card : ℤ) := by
  classical
  rw [crossRootDefectCenterPairs, crossRootCenterGrid,
    Finset.card_filter]
  push_cast
  rw [Finset.sum_product]
  simp [Matrix.mul_apply, SimpleGraph.adjMatrix_apply,
    -Finset.sum_const, -Finset.sum_boole, G.adj_comm,
    (secondOrderDefectGraph G).adj_comm, neighborFinset_eq_filter,
    Finset.sum_filter]
  trans (∑ v : V, ∑ u : V,
    if G.Adj y v then
      if (secondOrderDefectGraph G).Adj v u then
        if G.Adj x u then (1 : ℤ) else 0 else 0 else 0)
  · apply Finset.sum_congr rfl
    intro v _hv
    by_cases hyv : G.Adj y v <;> simp [hyv]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _hu
    by_cases hxu : G.Adj x u
    · simp only [hxu, ↓reduceIte]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hyv : G.Adj y v <;>
        by_cases huv : (secondOrderDefectGraph G).Adj u v <;>
          simp [hyv, huv, (secondOrderDefectGraph G).adj_comm]
    · simp [hxu]

/-- The adjacency-defect-adjacency sandwich is controlled pointwise by the
defect square.  Combinatorially, the left side counts defect edges between
the two ambient neighborhoods. -/
theorem adj_defect_adj_apply_eq_degree_terms_sub_defect_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q r : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = r)
    (x y : V) :
    (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ *
        G.adjMatrix ℤ) x y =
      (q - 1 : ℤ) * (secondOrderDefectGraph G).adjMatrix ℤ x y + r -
        ((secondOrderDefectGraph G).adjMatrix ℤ *
          (secondOrderDefectGraph G).adjMatrix ℤ) x y := by
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hcomm : A * D = D * A :=
    adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hsq : A * A =
      (q - 1 : ℤ) • (1 : Matrix V V ℤ) + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hDJ : D * J = (r : ℤ) • J :=
    FriendshipTheoremOQ01.adjMatrix_mul_ones
      (secondOrderDefectGraph G) r hDreg
  have hmatrix : A * D * A =
      (q - 1 : ℤ) • D + (r : ℤ) • J - D * D := by
    calc
      A * D * A = D * (A * A) := by rw [hcomm, Matrix.mul_assoc]
      _ = D * ((q - 1 : ℤ) • (1 : Matrix V V ℤ) + J - D) := by rw [hsq]
      _ = (q - 1 : ℤ) • D + (r : ℤ) • J - D * D := by
        rw [Matrix.mul_sub, Matrix.mul_add, hDJ]
        simp only [Matrix.mul_smul, Matrix.mul_one]
  have happ := congrArg (fun M : Matrix V V ℤ => M x y) hmatrix
  simpa only [A, D, J, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply,
    smul_eq_mul, mul_one] using happ

/-- Order-64 specialization on a defect edge: the sandwich entry is fourteen
minus the number of two-step defect walks between the endpoints. -/
theorem orderSixtyFour_adj_defect_adj_apply_of_defect_adj
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    {x y : Fin 64} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ *
        G.adjMatrix ℤ) x y =
      14 - ((secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) x y := by
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 7 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree (e := 5) hreg (by norm_num) z
    omega
  rw [adj_defect_adj_apply_eq_degree_terms_sub_defect_sq
    G hfree hreg hDreg x y]
  simp [SimpleGraph.adjMatrix_apply, hxyD]

/-- Exact defect-pair cardinality in the fourth center-grid factor. -/
theorem orderSixtyFour_crossRootDefectCenterPairs_card
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    {x y : Fin 64} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    ((crossRootDefectCenterPairs G x y).card : ℤ) =
      14 - ((secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) x y := by
  rw [← adj_defect_adj_apply_eq_card_crossRootDefectCenterPairs G x y]
  exact orderSixtyFour_adj_defect_adj_apply_of_defect_adj
    G hfree hreg hxyD

/-- Exact complementary source-common cardinality: two plus the adjacent
defect codegree. -/
theorem orderSixtyFour_crossRootSourceCommonCenterPairs_card
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : e.supp.ncard = 16) (hf : f.supp.ncard = 16)
    (hg : g.supp.ncard = 16)
    (hexhaust : ∀ k : (secondOrderDefectGraph G).ConnectedComponent,
      k = d ∨ k = e ∨ k = f ∨ k = g)
    (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    ((crossRootSourceCommonCenterPairs G d x.1 y.1).card : ℤ) =
      2 + ((secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) x.1 y.1 := by
  have hsplit :=
    orderSixtyFour_sourceCommon_add_defect_centerPairs_card_eq_sixteen
      G hfree hreg hde hdf hdg hef heg hfg he hf hg hexhaust x y hxyD
  have hdefect := orderSixtyFour_crossRootDefectCenterPairs_card
    G hfree hreg hxyD
  omega

end

end Erdos85

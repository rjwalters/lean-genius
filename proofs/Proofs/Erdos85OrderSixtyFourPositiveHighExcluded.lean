import Proofs.Erdos85OrderSixtyFourBranchReduction

/-! # Positive-high parity exclusion at order 64

At square order, the zero-slack high-root theorem makes the graph induced on
the neighborhood of a degree-`d+1` vertex 1-regular.  For `d = 8` that
neighborhood has nine vertices, contradicting the handshake identity.  Thus
every normalized order-64 tight core is regular; all six positive high-count
branches collapse simultaneously.
-/

open SimpleGraph

namespace Erdos85

/-- A normalized order-64 tight-cover graph has no degree-nine vertex. -/
theorem orderSixtyFour_no_degree_nine_of_tightCover
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x) :
    ∀ v : Fin 64, G.degree v ≠ 9 := by
  intro v hv
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  have hlocal :=
    (squareOrder_degree_succ_highRoot_structure
      G hfree (d := 8) (by norm_num) hmin hcard hv).2.2
  let N := {z : Fin 64 // z ∈ G.neighborSet v}
  let L := G.induce (G.neighborSet v)
  have hsumOne : (∑ y : N, L.degree y) = Fintype.card N := by
    calc
      (∑ y : N, L.degree y) = ∑ _y : N, 1 := by
        apply Finset.sum_congr rfl
        intro y _
        exact hlocal y
      _ = Fintype.card N := by simp
  have hNcard : Fintype.card N = 9 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by
      ext z
      simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  have hhand := L.sum_degrees_eq_twice_card_edges
  rw [hsumOne, hNcard] at hhand
  omega

/-- Consequently the high sector is empty. -/
theorem orderSixtyFour_highVertices_eq_empty_of_tightCover
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x) :
    squareOrderHighVertices G 8 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hvNine : G.degree v = 9 := by
    simpa [squareOrderHighVertices] using (Finset.mem_filter.mp hv).2
  exact orderSixtyFour_no_degree_nine_of_tightCover G hfree hmin v hvNine

/-- Every positive high-count branch is impossible, independently of energy
minimality and slide saturation. -/
theorem orderSixtyFour_positive_high_branch_excluded
    {h : Nat} (hpos : 0 < h) :
    OrderSixtyFourTightBranchExcluded h := by
  intro G hdec hfree hmin _hminimal _hcover _hslide hh
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  have hmin' : ∀ x : Fin 64, 8 ≤ G.degree x :=
    fun x => hmin.trans (G.minDegree_le_degree x)
  have hempty := orderSixtyFour_highVertices_eq_empty_of_tightCover
    G hfree hmin'
  rw [hempty] at hh
  simp at hh
  omega

theorem orderSixtyFour_two_high_excluded :
    OrderSixtyFourTightBranchExcluded 2 :=
  orderSixtyFour_positive_high_branch_excluded (by norm_num)

theorem orderSixtyFour_four_high_excluded :
    OrderSixtyFourTightBranchExcluded 4 :=
  orderSixtyFour_positive_high_branch_excluded (by norm_num)

theorem orderSixtyFour_six_high_excluded :
    OrderSixtyFourTightBranchExcluded 6 :=
  orderSixtyFour_positive_high_branch_excluded (by norm_num)

theorem orderSixtyFour_eight_high_excluded :
    OrderSixtyFourTightBranchExcluded 8 :=
  orderSixtyFour_positive_high_branch_excluded (by norm_num)

theorem orderSixtyFour_ten_high_excluded :
    OrderSixtyFourTightBranchExcluded 10 :=
  orderSixtyFour_positive_high_branch_excluded (by norm_num)

theorem orderSixtyFour_twelve_high_excluded :
    OrderSixtyFourTightBranchExcluded 12 :=
  orderSixtyFour_positive_high_branch_excluded (by norm_num)

/-- Order-64 nonexistence now has only the regular branch left. -/
theorem no_orderSixtyFour_witness_of_regular_branch
    (h0 : OrderSixtyFourTightBranchExcluded 0) :
    ¬ C4FreeMinDegreeWitness 64 8 :=
  no_orderSixtyFour_witness_of_branches h0
    orderSixtyFour_two_high_excluded
    orderSixtyFour_four_high_excluded
    orderSixtyFour_six_high_excluded
    orderSixtyFour_eight_high_excluded
    orderSixtyFour_ten_high_excluded
    orderSixtyFour_twelve_high_excluded

end Erdos85

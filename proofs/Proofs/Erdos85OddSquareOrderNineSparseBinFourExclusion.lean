import Proofs.Erdos85OddSquareOrderNineIncidenceQuotientArithmetic

/-! # Pointwise exclusion of the sparse q = 9 bin-four profile

Node: B.3 / GAP B-CLASSIFY.  The h=9 histogram `(9,66,0,0,6)` passes the
aggregate symmetric quotient equations, but fails the pointwise defect-row
law at every bin-four vertex.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The h=9 scalar histogram `(9,66,0,0,6)` cannot occur.  Its low support
is confined to incidence weights 1 and 4.  A bin-four vertex has four defect
neighbors whose weights sum to five, but four entries from `{1,4}` cannot
have that sum. -/
theorem squareOrderNine_not_highIncidence_profile_9_66_0_0_6_of_nine_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 9)
    (hc0 : squareOrderNineHighIncidenceHistogram G 0 = 9)
    (_hc1 : squareOrderNineHighIncidenceHistogram G 1 = 66)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 6) : False := by
  let B := squareOrderNineLowIncidenceBin G
  have hbzero := squareOrderNine_lowIncidenceBin_zero_card_add_high_card G hp
  have hb0 : (B 0).card = 0 := by
    dsimp [B]
    rw [hhigh, hc0] at hbzero
    omega
  have hb2 : (B 2).card = 0 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero G hp (by omega), hc2]
  have hb3 : (B 3).card = 0 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero G hp (by omega), hc3]
  have hb4 : (B 4).card = 6 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero G hp (by omega), hc4]
  have hB0 : B 0 = ∅ := Finset.card_eq_zero.mp hb0
  have hB2 : B 2 = ∅ := Finset.card_eq_zero.mp hb2
  have hB3 : B 3 = ∅ := Finset.card_eq_zero.mp hb3
  have hB4nonempty : (B 4).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hB4nonempty
  have hpart := squareOrderNine_defectNeighbor_bin_partition
    G hfree hmin hcard hp x
  dsimp only at hpart
  change
    (∑ j ∈ Finset.range 5,
      ((secondOrderDefectGraph G).neighborFinset x ∩ B j).card) =
        (secondOrderDefectGraph G).degree x ∧
      (∑ j ∈ Finset.range 5,
        j * ((secondOrderDefectGraph G).neighborFinset x ∩ B j).card) =
        ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
          squareOrderHighIncidenceCount G 9 y at hpart
  have hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9 := by
    intro u v huv
    rcases hp.degree_dichotomy u with hu | hu
    · exact Or.inl hu
    · rcases hp.degree_dichotomy v with hv | hv
      · exact Or.inr hv
      · exact (hp.high_independent
          (Finset.mem_filter.mpr ⟨by simp, hu⟩)
          (Finset.mem_filter.mpr ⟨by simp, hv⟩) huv).elim
  have hdegree : (secondOrderDefectGraph G).degree x = 4 := by
    -- The pointwise degree formula is already embedded in the quotient proof;
    -- recover it directly from the standard square-order identity.
    have hxlow : G.degree x = 9 := by
      have hxL := (Finset.mem_filter.mp hx).1
      have hxnot := (Finset.mem_sdiff.mp hxL).2
      rcases hp.degree_dichotomy x with hlo | hhi
      · exact hlo
      · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
    have hd := squareOrder_defectDegree_add_highIncidence_eq_pred
      G hfree (by norm_num) hmin hcover hcard hxlow
    have hk : squareOrderHighIncidenceCount G 9 x = 4 :=
      (Finset.mem_filter.mp hx).2
    rw [hk] at hd
    omega
  have hweight :
      (∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
        squareOrderHighIncidenceCount G 9 y) = 5 := by
    have hxlow : G.degree x = 9 := by
      have hxL := (Finset.mem_filter.mp hx).1
      have hxnot := (Finset.mem_sdiff.mp hxL).2
      rcases hp.degree_dichotomy x with hlo | hhi
      · exact hlo
      · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, hhi⟩)).elim
    have hw := squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree (by norm_num) hmin hcard hxlow
    have hk : squareOrderHighIncidenceCount G 9 x = 4 :=
      (Finset.mem_filter.mp hx).2
    rw [hk, hhigh] at hw
    omega
  norm_num [Finset.sum_range_succ] at hpart
  rw [hB0, hB2, hB3] at hpart
  norm_num [hdegree, hweight] at hpart
  omega

end

end Erdos85

#print axioms
  Erdos85.squareOrderNine_not_highIncidence_profile_9_66_0_0_6_of_nine_high

import Proofs.Erdos85SizeTwoEigenlineEightEightHighCrossAntipodal
import Proofs.Erdos85SizeTwoEigenlineEightEightBothTriangleExteriorModel

/-!
# Exterior-pair coordinates for the high eight-plus-eight cross block

These lemmas deliberately stop short of choosing a cyclic phase for the
cross block.  The checked high owner CNF carries those cross bits itself, so
the graph adapter only needs the exact within-shore relation and the fact
that cross exterior pairs are the complement of cross defect adjacency.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- If the diagonal defect block of a labeled C8 is the half-turn matching,
then its exterior-pair block consists exactly of offsets `±1, ±3`. -/
theorem sizeTwo_eight_halfTurnDefect_exteriorPair_iff_odd_nonzero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    (hD : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (w i) (w j) ↔
        j - i = 4) :
    ∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (w i) (w j) ↔
      j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7 := by
  let H := G.induce c.supp
  intro i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have hcommon (hij : i ≠ j) :
      (∃ z, H.Adj (w i) z ∧ H.Adj (w j) z) ↔
        j - i = 2 ∨ j - i = 6 :=
    zmodEight_cycle_internalCommon_iff_offset_two_six H w hwinj hw i j hij
  constructor
  · rintro ⟨hij, hnotD, hnoCommon⟩
    have hij' : i ≠ j := fun h => hij (congrArg w h)
    have hnot4 : j - i ≠ 4 := by
      intro h4
      exact hnotD ((hD i j).mpr h4)
    have hnotCommon : ¬ (j - i = 2 ∨ j - i = 6) := by
      intro hoff
      apply hnoCommon
      simpa [H] using (hcommon hij').mpr hoff
    have hall : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨
        j - i = 6 ∨ j - i = 7 := by
      generalize j - i = d
      revert d
      decide
    have hnot0 : j - i ≠ 0 := by
      intro h0
      apply hij'
      exact (sub_eq_zero.mp h0).symm
    tauto
  · intro hoff
    have hij' : i ≠ j := by
      intro h
      subst j
      have hzero : ¬ ((0 : ZMod 8) = 1 ∨ (0 : ZMod 8) = 3 ∨
          (0 : ZMod 8) = 5 ∨ (0 : ZMod 8) = 7) := by decide
      exact hzero (by simpa using hoff)
    refine ⟨hwinj.ne hij', ?_, ?_⟩
    · intro hDij
      have h4 := (hD i j).mp (by simpa using hDij)
      rcases hoff with h1 | h3 | h5 | h7
      · rw [h1] at h4; revert h4; decide
      · rw [h3] at h4; revert h4; decide
      · rw [h5] at h4; revert h4; decide
      · rw [h7] at h4; revert h4; decide
    · intro hex
      have hc := (hcommon hij').mp (by simpa [H] using hex)
      rcases hoff with h1 | h3 | h5 | h7
      · rw [h1] at hc; revert hc; decide
      · rw [h3] at hc; revert hc; decide
      · rw [h5] at hc; revert hc; decide
      · rw [h7] at hc; revert hc; decide

/-- Between two distinct ambient-cycle components there is no internal
common neighbor.  Hence a cross pair is owned outside exactly when it is a
cross defect nonedge. -/
theorem sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp) :
    ∀ i j, (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
      ¬ ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j) := by
  let H := G.induce c.supp
  have hua : ∀ i, H.connectedComponentMk (u i) = a := by
    intro i
    exact (ConnectedComponent.mem_supp_iff a (u i)).mp (by
      rw [← hurange]
      exact ⟨i, rfl⟩)
  have hvb : ∀ j, H.connectedComponentMk (v j) = b := by
    intro j
    exact (ConnectedComponent.mem_supp_iff b (v j)).mp (by
      rw [← hvrange]
      exact ⟨j, rfl⟩)
  intro i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have hne : u i ≠ v j := by
    intro huv
    apply hab
    rw [← hua i, ← hvb j, huv]
  have hnoCommon := distinct_components_no_internalCommon
    H a b hab u v hua hvb i j
  constructor
  · exact fun h => h.2.1
  · intro hnotD
    exact ⟨hne, hnotD, by simpa [H] using hnoCommon⟩

/-- At quotient six the complementary cross exterior block has row and
column degree two.  This is the exact cardinality constraint used by the
variable-cross CNF. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_crossExterior_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6) :
    (∀ i, ((Finset.univ : Finset (ZMod 8)).filter fun j =>
      (exteriorPairGraph G c.supp).Adj (u i) (v j)).card = 2) ∧
    (∀ j, ((Finset.univ : Finset (ZMod 8)).filter fun i =>
      (exteriorPairGraph G c.supp).Adj (u i) (v j)).card = 2) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let R := exteriorPairGraph G c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hba6 : componentQuotientMatrix K H b a = 6 := by
    have hbal := componentQuotientMatrix_balance K H 2 hHdegree hcomm a b
    change a.supp.ncard * componentQuotientMatrix K H a b =
      b.supp.ncard * componentQuotientMatrix K H b a at hbal
    rw [ha, hb] at hbal
    have hab6' : componentQuotientMatrix K H a b = 6 := by simpa [K, H] using hab6
    rw [hab6'] at hbal
    omega
  have hcompUV := sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    G hfree c a b hab u v hurange hvrange
  have hcompVU : ∀ j i, R.Adj (v j) (u i) ↔ ¬ K.Adj (v j) (u i) := by
    intro j i
    rw [R.adj_comm, K.adj_comm]
    exact hcompUV i j
  have rowCard
      (w z : ZMod 8 → c.supp)
      (hzinj : Function.Injective z)
      (d e : H.ConnectedComponent)
      (hwmem : ∀ x, w x ∈ d.supp)
      (hzrange : Set.range z = e.supp)
      (hde : componentQuotientMatrix K H d e = 6)
      (hcomp : ∀ x y, R.Adj (w x) (z y) ↔ ¬ K.Adj (w x) (z y)) :
      ∀ x, ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        R.Adj (w x) (z y)).card = 2 := by
    intro x
    let T := (Finset.univ : Finset (ZMod 8)).filter fun y => K.Adj (w x) (z y)
    let B := componentNeighborFinset K H e (w x)
    have himage : T.image z = B := by
      ext q
      simp only [T, B, Finset.mem_image, Finset.mem_filter,
        Finset.mem_univ, true_and, componentNeighborFinset]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨(K.mem_neighborFinset _ _).mpr hy,
          (ConnectedComponent.mem_supp_iff e (z y)).mp (by
            rw [← hzrange]; exact ⟨y, rfl⟩)⟩
      · rintro ⟨hqK, hqe⟩
        have hqSupp : q ∈ e.supp :=
          (ConnectedComponent.mem_supp_iff e q).mpr hqe
        rw [← hzrange] at hqSupp
        obtain ⟨y, rfl⟩ := hqSupp
        exact ⟨y, (K.mem_neighborFinset _ _).mp hqK, rfl⟩
    have hTcard : T.card = 6 := by
      rw [← Finset.card_image_of_injective T hzinj, himage]
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm d e
        (hwmem x)]
      exact hde
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (ZMod 8))) (p := fun y => K.Adj (w x) (z y))
    have hRfilter :
        ((Finset.univ : Finset (ZMod 8)).filter fun y => R.Adj (w x) (z y)) =
          (Finset.univ.filter fun y => ¬ K.Adj (w x) (z y)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hcomp x y
    rw [hRfilter]
    change T.card + _ = 8 at hpartition
    rw [hTcard] at hpartition
    omega
  constructor
  · apply rowCard u v hvinj a b
    · intro i
      rw [← hurange]
      exact ⟨i, rfl⟩
    · exact hvrange
    · simpa [K, H] using hab6
    · exact hcompUV
  · intro j
    have h := rowCard v u huinj b a (fun k => by
      rw [← hvrange]; exact ⟨k, rfl⟩) hurange hba6 hcompVU j
    simpa only [R.adj_comm] using h

/-- The complementary cross exterior block intertwines the two C8 adjacency
operators entrywise.  Complementing changes each cross entry from `d` to
`1-d`; the two constant terms cancel in the cycle recurrence. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_crossExterior_intertwines
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : Fintype.card V = 8 * 8) (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∀ x y,
      (exteriorPairGraph G c.supp).adjMatrix ℤ (u (x - 1)) (v y) +
          (exteriorPairGraph G c.supp).adjMatrix ℤ (u (x + 1)) (v y) =
        (exteriorPairGraph G c.supp).adjMatrix ℤ (u x) (v (y + 1)) +
          (exteriorPairGraph G c.supp).adjMatrix ℤ (u x) (v (y - 1)) := by
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let R := exteriorPairGraph G c.supp
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    obtain ⟨_, _, hHK⟩ :=
      binarySquare_regular_sizeTwoPart_commuting_regular_blocks
        G hfree (by omega) hreg hcard c hc
    simpa [K, H] using hHK.symm
  have hupair : ∀ x, u (x - 1) ≠ u (x + 1) := fun x =>
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) x)
  have hvpair : ∀ y, v (y - 1) ≠ v (y + 1) := fun y =>
    hvinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) y)
  have hDinter := entry_cycleIntertwine_of_adjMatrix_comm
    K H u v (1 : ZMod 8) (1 : ZMod 8) hcomm hu hv hupair hvpair
  have hcomp := sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    G hfree c a b hab u v hurange hvrange
  have hentry (x y : ZMod 8) :
      R.adjMatrix ℤ (u x) (v y) = 1 - K.adjMatrix ℤ (u x) (v y) := by
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases hD : K.Adj (u x) (v y)
    · have hR : ¬ R.Adj (u x) (v y) := by
        intro h
        exact (hcomp x y).mp h hD
      simp [hD, hR]
    · have hR : R.Adj (u x) (v y) := (hcomp x y).mpr hD
      simp [hD, hR]
  intro x y
  rw [hentry, hentry, hentry, hentry]
  have h := hDinter x y
  linear_combination -h

end

end Erdos85

#print axioms Erdos85.sizeTwo_eight_halfTurnDefect_exteriorPair_iff_odd_nonzero
#print axioms Erdos85.sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect

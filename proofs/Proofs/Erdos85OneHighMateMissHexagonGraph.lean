import Proofs.Erdos85OneHighMateMissHexagon
import Proofs.Erdos85OneHighGlobalMissLabelCounting

/-! # Graph specialization of the mate-miss hexagon -/

namespace Erdos85

open SimpleGraph

noncomputable section

private theorem mateHexagon_eq_or_swap_of_minMax_pair_eq
    {L : Type*} [LinearOrder L]
    {a b c d : L} (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : (min a b, max a b) = (min c d, max c d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt <;>
    rcases lt_or_gt_of_ne hcd with hcdlt | hdclt
  · rw [min_eq_left hablt.le, max_eq_right hablt.le,
      min_eq_left hcdlt.le, max_eq_right hcdlt.le] at hpair
    exact Or.inl (Prod.mk.inj hpair)
  · rw [min_eq_left hablt.le, max_eq_right hablt.le,
      min_eq_right hdclt.le, max_eq_left hdclt.le] at hpair
    exact Or.inr (Prod.mk.inj hpair)
  · have h := Prod.mk.inj hpair
    rw [min_eq_right hbalt.le, max_eq_left hbalt.le,
      min_eq_left hcdlt.le, max_eq_right hcdlt.le] at h
    exact Or.inr ⟨h.2, h.1⟩
  · have h := Prod.mk.inj hpair
    rw [min_eq_right hbalt.le, max_eq_left hbalt.le,
      min_eq_right hdclt.le, max_eq_left hdclt.le] at h
    exact Or.inl ⟨h.2, h.1⟩

/-- A concrete global internal matching edge whose two unique miss labels are
an adjacent root pair produces the mate-miss hexagon configuration. -/
theorem exists_oneHighMateMissHexagon_of_globalEdge
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (x : OneHighAllMatchedVertices G v)
    (hx : x ∈ nonconstantMatchingEdgeSources
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj))
    (u w : {z : V // z ∈ G.neighborSet v})
    (huw : G.Adj u.1 w.1)
    (hpair : exchangedMissPairKey
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) x = (min u w, max u w)) :
    Nonempty (OneHighMateMissHexagon G v) := by
  let mate := oneHighGlobalInternalMate G hfree v
  let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
    rootMate hrootAdj
  let xm := mate x
  have hlabelNe : label x ≠ label xm :=
    (Finset.mem_filter.mp hx).2.2
  have huwNe : u ≠ w := fun h =>
    (G.ne_of_adj huw) (congrArg Subtype.val h)
  have horient :
      (label x = u ∧ label xm = w) ∨
        (label x = w ∧ label xm = u) := by
    exact mateHexagon_eq_or_swap_of_minMax_pair_eq hlabelNe huwNe hpair
  have hxMem := oneHighGlobalMissLabel_mem G hfree hv hexternal
    houterDegree rootMate hrootAdj x
  have hxmMem := oneHighGlobalMissLabel_mem G hfree hv hexternal
    houterDegree rootMate hrootAdj xm
  have hxMatched :
      (G.neighborFinset x.2.1.1 ∩
        secondLayerBranch G v x.1).card = 1 := by
    rw [← degree_induce_secondLayerBranch_eq_card_inter]
    exact x.2.2
  have hxmMatched :
      (G.neighborFinset xm.2.1.1 ∩
        secondLayerBranch G v xm.1).card = 1 := by
    rw [← degree_induce_secondLayerBranch_eq_card_inter]
    exact xm.2.2
  have hxy : G.Adj x.2.1.1 xm.2.1.1 := by
    change G.Adj x.2.1.1
      (oneHighInternalMate G hfree v x.1 x.2).1.1
    exact degreeOneMate_adj
      (G.induce (secondLayerBranch G v x.1))
      (degree_induce_secondLayerBranch_le_one G hfree v x.1) x.2
  have hsees (z : {q : V // q ∈ G.neighborSet v})
      (hzBase : z ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)))
      (hzNe : z ≠ label x) :
      (G.neighborFinset x.2.1.1 ∩
        secondLayerBranch G v z).card ≠ 0 := by
    intro hzero
    have hzMiss : z ∈ oneHighFarMissBranches G v rootMate x.1 x.2.1.1 :=
      Finset.mem_filter.mpr ⟨hzBase, hzero⟩
    have heq := eq_oneHighMissingBranch_of_matched_of_mem G hfree hv
      hexternal houterDegree rootMate hrootAdj x.1 x.2.1.1 x.2.1.2
      hxMatched z hzMiss
    exact hzNe heq
  have hseesM (z : {q : V // q ∈ G.neighborSet v})
      (hzBase : z ∈ ((Finset.univ.erase xm.1).erase (rootMate xm.1)))
      (hzNe : z ≠ label xm) :
      (G.neighborFinset xm.2.1.1 ∩
        secondLayerBranch G v z).card ≠ 0 := by
    intro hzero
    have hzMiss : z ∈ oneHighFarMissBranches G v rootMate xm.1 xm.2.1.1 :=
      Finset.mem_filter.mpr ⟨hzBase, hzero⟩
    have heq := eq_oneHighMissingBranch_of_matched_of_mem G hfree hv
      hexternal houterDegree rootMate hrootAdj xm.1 xm.2.1.1 xm.2.1.2
      hxmMatched z hzMiss
    exact hzNe heq
  rcases horient with h | h
  · have huBase := (Finset.mem_filter.mp hxMem).1
    have hwBase := (Finset.mem_filter.mp hxmMem).1
    change label x ∈
      ((Finset.univ.erase x.1).erase (rootMate x.1)) at huBase
    change label xm ∈
      ((Finset.univ.erase xm.1).erase (rootMate xm.1)) at hwBase
    rw [h.1] at huBase
    rw [h.2] at hwBase
    have hsu : x.1 ≠ u :=
      Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp huBase).2).1
    have hsw : x.1 ≠ w :=
      Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp hwBase).2).1
    apply exists_oneHighMateMissHexagon G hfree x.1 u w hsu hsw huw
      x.2.1.2 xm.2.1.2 hxy
    · simpa [label, h.1] using (Finset.mem_filter.mp hxMem).2
    · simpa [label, h.2] using (Finset.mem_filter.mp hxmMem).2
    · exact hseesM u (by simpa [xm, mate, oneHighGlobalInternalMate] using huBase) (by
        rw [h.2]
        exact huwNe)
    · exact hsees w hwBase (by rw [h.1]; exact huwNe.symm)
  · have hwBase := (Finset.mem_filter.mp hxMem).1
    have huBase := (Finset.mem_filter.mp hxmMem).1
    change label x ∈
      ((Finset.univ.erase x.1).erase (rootMate x.1)) at hwBase
    change label xm ∈
      ((Finset.univ.erase xm.1).erase (rootMate xm.1)) at huBase
    rw [h.1] at hwBase
    rw [h.2] at huBase
    have hsu : x.1 ≠ u :=
      Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp huBase).2).1
    have hsw : x.1 ≠ w :=
      Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp hwBase).2).1
    apply exists_oneHighMateMissHexagon G hfree x.1 u w hsu hsw huw
      xm.2.1.2 x.2.1.2 hxy.symm
    · simpa [label, h.2] using (Finset.mem_filter.mp hxmMem).2
    · simpa [label, h.1] using (Finset.mem_filter.mp hxMem).2
    · exact hsees u
        (by simpa [xm, mate, oneHighGlobalInternalMate] using huBase) (by
          rw [h.1]
          exact huwNe)
    · exact hseesM w
        (by simpa [xm, mate, oneHighGlobalInternalMate] using hwBase) (by
        rw [h.2]
        exact huwNe.symm)

/-- Direct odd-support consumer: an odd exchanged multiplicity on an adjacent
root pair supplies a concrete matching edge and hence a mate-miss hexagon. -/
theorem exists_oneHighMateMissHexagon_of_oddMultiplicity
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (u w : {z : V // z ∈ G.neighborSet v})
    (huw : G.Adj u.1 w.1)
    (hodd : Odd (exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) (min u w, max u w))) :
    Nonempty (OneHighMateMissHexagon G v) := by
  have hpos : 0 < exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) (min u w, max u w) := by
    rcases hodd with ⟨k, hk⟩
    omega
  unfold exchangedMissPairMultiplicity at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  have hxParts := Finset.mem_filter.mp hx
  exact exists_oneHighMateMissHexagon_of_globalEdge G hfree hv hexternal
    houterDegree rootMate hrootAdj x hxParts.1 u w huw hxParts.2

end

end Erdos85

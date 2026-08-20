import Proofs.Erdos85MuNegThreeZeroFiveAntipodalForcedTypeCounts
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCommonTypeBalance

/-! # Seven opposite-shore targets for every antipodal center -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The five forced same-shore targets and the antipodal type balance imply
that every antipodal center has at least seven opposite-shore targets. -/
theorem h305_antipodal_offDiagonalCommon_typeZero_seven_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j}) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    7 ≤ offDiagonalCommonShoreTypeCount R Cedge a U 0 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let F := h305AntipodalSaturatedStarTypeFinset R u i 2
  let T := (offDiagonalCommonNeighborSupport Cedge a).filter fun b ↦
    (b.1.toFinset ∩ U).card = 2
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  have hcoords : ∀ i j : ZMod 8, j - i = 4 →
      i + 2 ≠ i ∧ i + 2 ≠ j ∧ i + 6 ≠ i ∧ i + 6 ≠ j := by
    native_decide
  have hFa : ∀ e ∈ F, e ≠ a.1 := by
    intro e he hea
    have heUnion := (Finset.mem_filter.mp he).1
    have heCentral : e.toFinset = {u i, u j} := by
      rw [hea, ha]
    rw [h305AntipodalSaturatedStarUnion, Finset.mem_union] at heUnion
    rcases heUnion with he2 | he6
    · have hm : u (i + 2) ∈ e.toFinset := Sym2.mem_toFinset.mpr
        ((R.mem_incidenceFinset (u (i + 2)) e).mp he2).2
      rw [heCentral] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact (hcoords i j hoffset).1 (huinj hm)
      · exact (hcoords i j hoffset).2.1 (huinj hm)
    · have hm : u (i + 6) ∈ e.toFinset := Sym2.mem_toFinset.mpr
        ((R.mem_incidenceFinset (u (i + 6)) e).mp he6).2
      rw [heCentral] at hm
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact (hcoords i j hoffset).2.2.1 (huinj hm)
      · exact (hcoords i j hoffset).2.2.2 (huinj hm)
  have hsubset : F ⊆ T.map eR := by
    intro e he
    obtain ⟨b, hbe, hcommon⟩ :=
      h305_antipodalSaturatedStarUnion_forced_common H R Cedge hservice
        hHreg hRreg hCreg hfree u huinj hu a i j hoffset ha e
          (Finset.mem_filter.mp he).1
    have hba : b ≠ a := by
      intro hba
      apply hFa e he
      simpa [hba] using hbe.symm
    have hbSupport : b ∈ offDiagonalCommonNeighborSupport Cedge a := by
      simp [offDiagonalCommonNeighborSupport, hba, hcommon]
    have hbType : (b.1.toFinset ∩ U).card = 2 := by
      have := (Finset.mem_filter.mp he).2
      simpa [F, U, hbe] using this
    apply Finset.mem_map.mpr
    exact ⟨b, Finset.mem_filter.mpr ⟨hbSupport, hbType⟩, hbe⟩
  have hFcard : F.card = 5 := by
    simpa [F] using
      (h305_antipodalSaturatedStar_typeCounts R hRreg u huinj hmode i).1
  have hTfive : 5 ≤ T.card := by
    have hc := Finset.card_le_card hsubset
    rw [Finset.card_map, hFcard] at hc
    exact hc
  have hbalance :=
    h305_antipodal_offDiagonalCommon_typeZero_eq_typeTwo_add_two
      H R Cedge hservice hHreg hCreg hfree u huinj hu a i j
        hoffset ha
  change 7 ≤ offDiagonalCommonShoreTypeCount R Cedge a U 0
  change offDiagonalCommonShoreTypeCount R Cedge a U 0 =
    offDiagonalCommonShoreTypeCount R Cedge a U 2 + 2 at hbalance
  change 5 ≤ offDiagonalCommonShoreTypeCount R Cedge a U 2 at hTfive
  omega

end

end Erdos85

#print axioms Erdos85.h305_antipodal_offDiagonalCommon_typeZero_seven_le

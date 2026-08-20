import Proofs.Erdos85MuNegThreeZeroFiveCommonStarSaturation
import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry
import Proofs.Erdos85C4FreeRegularCommonSupport

/-! # The eleven forced common-support targets of an antipodal h305 edge -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The union of the two exterior incidence stars at the nonendpoint
eligible coordinates of an antipodal shore edge. -/
def h305AntipodalSaturatedStarUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (i : ZMod 8) : Finset (Sym2 V) :=
  R.incidenceFinset (u (i + 2)) ∪ R.incidenceFinset (u (i + 6))

/-- The two six-edge stars overlap in their unique antipodal connecting
edge, so their union has size eleven. -/
theorem h305_antipodalSaturatedStarUnion_card_eleven
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (hRreg : ∀ x, R.degree x = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (i : ZMod 8) :
    (h305AntipodalSaturatedStarUnion R u i).card = 11 := by
  classical
  let k := i + 2
  let l := i + 6
  have hklCoord : l - k = (4 : ZMod 8) := by
    dsimp [k, l]
    ring
  have hkl : R.Adj (u k) (u l) := by
    rcases hmode with htri | htf
    · exact (htri k l).2 (Or.inr (Or.inl hklCoord))
    · exact (htf k l).2 (Or.inr (Or.inl hklCoord))
  have hinter : R.incidenceFinset (u k) ∩ R.incidenceFinset (u l) =
      {s(u k, u l)} := by
    ext e
    have hs := R.incidenceSet_inter_incidenceSet_of_adj hkl
    simpa [SimpleGraph.mem_incidenceFinset] using Set.ext_iff.mp hs e
  have huCard : (R.incidenceFinset (u k)).card = 6 := by
    simp [R.card_incidenceFinset_eq_degree, hRreg]
  have hvCard : (R.incidenceFinset (u l)).card = 6 := by
    simp [R.card_incidenceFinset_eq_degree, hRreg]
  have hcount := Finset.card_union_add_card_inter
    (R.incidenceFinset (u k)) (R.incidenceFinset (u l))
  rw [huCard, hvCard, hinter] at hcount
  change (R.incidenceFinset (u k) ∪ R.incidenceFinset (u l)).card = 11
  simp only [Finset.card_singleton] at hcount
  omega

/-- Every edge in the eleven-target union is an actual exterior edge that
shares a service neighbor with the central antipodal edge. -/
theorem h305_antipodalSaturatedStarUnion_forced_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j : ZMod 8)
    (haoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j})
    (e : Sym2 V) (he : e ∈ h305AntipodalSaturatedStarUnion R u i) :
    ∃ b : R.edgeFinset, b.1 = e ∧
      (Cedge.neighborFinset b ∩ Cedge.neighborFinset a).Nonempty := by
  classical
  have helig : ∀ i j : ZMod 8, j - i = 4 →
      i + 2 ∈ h305ServiceNonendpointEligibleCoordinates i j ∧
      i + 6 ∈ h305ServiceNonendpointEligibleCoordinates i j := by
    native_decide
  have hk := h305_antipodal_commonStar_saturates H R Cedge hservice
    hHreg hRreg hCreg hfree u huinj hu a i j (i + 2) haoffset ha
      (helig i j haoffset).1
  have hl := h305_antipodal_commonStar_saturates H R Cedge hservice
    hHreg hRreg hCreg hfree u huinj hu a i j (i + 6) haoffset ha
      (helig i j haoffset).2
  rw [h305AntipodalSaturatedStarUnion, Finset.mem_union] at he
  have hvalue : e ∈ incidentServiceCommonEdgeValues R Cedge
      (u (i + 2)) a ∨
      e ∈ incidentServiceCommonEdgeValues R Cedge (u (i + 6)) a := by
    rcases he with he | he
    · exact Or.inl (hk.symm ▸ he)
    · exact Or.inr (hl.symm ▸ he)
  rcases hvalue with he | he
  · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp he
    refine ⟨b, hbe, ?_⟩
    exact (Finset.mem_filter.mp hb).2.2
  · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp he
    refine ⟨b, hbe, ?_⟩
    exact (Finset.mem_filter.mp hb).2.2

end

end Erdos85

#print axioms Erdos85.h305_antipodalSaturatedStarUnion_card_eleven
#print axioms Erdos85.h305_antipodalSaturatedStarUnion_forced_common

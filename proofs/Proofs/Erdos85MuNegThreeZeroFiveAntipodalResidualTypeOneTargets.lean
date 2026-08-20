import Proofs.Erdos85MuNegThreeZeroFiveAntipodalTypeOneLower
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalForcedTypeCounts

/-! # Two type-one targets outside every antipodal forced star -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Type-one common targets not already belonging to the center's forced
eleven-target incidence-star union. -/
def h305AntipodalResidualTypeOneTargets
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : ZMod 8 → V) (i : ZMod 8) (a : R.edgeFinset) :
    Finset R.edgeFinset :=
  ((offDiagonalCommonNeighborSupport Cedge a).filter fun b ↦
    (b.1.toFinset ∩ (Finset.univ : Finset (ZMod 8)).image u).card = 1).filter
      fun b ↦ b.1 ∉ h305AntipodalSaturatedStarUnion R u i

/-- At least eight type-one targets exist, while at most the six type-one
members of the forced star can lie inside it.  Hence at least two type-one
targets remain outside the center's own forced star. -/
theorem h305_antipodalResidualTypeOneTargets_card_two_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ x, Cedge.degree x = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j}) :
    2 ≤ (h305AntipodalResidualTypeOneTargets R Cedge u i a).card := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let T := (offDiagonalCommonNeighborSupport Cedge a).filter fun b ↦
    (b.1.toFinset ∩ U).card = 1
  let Inside := T.filter fun b ↦
    b.1 ∈ h305AntipodalSaturatedStarUnion R u i
  let Outside := T.filter fun b ↦
    b.1 ∉ h305AntipodalSaturatedStarUnion R u i
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  have hT : 8 ≤ T.card := by
    simpa [T, U, offDiagonalCommonShoreTypeCount] using
      (h305_antipodal_offDiagonalCommon_typeOne_eight_le
        H R Cedge hservice hHreg hRreg hCreg hfree u v huinj hvinj hu
          hdisj hcover humode hvmode a i j hoffset ha)
  have hInsideMap : Inside.map eR ⊆
      h305AntipodalSaturatedStarTypeFinset R u i 1 := by
    intro e he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp he
    have hb' := Finset.mem_filter.mp hb
    have hbT := Finset.mem_filter.mp hb'.1
    apply Finset.mem_filter.mpr
    refine ⟨hb'.2, ?_⟩
    change (b.1.toFinset ∩
      (Finset.univ : Finset (ZMod 8)).image u).card = 1
    simpa [U] using hbT.2
  have hInside : Inside.card ≤ 6 := by
    have hc := Finset.card_le_card hInsideMap
    rw [Finset.card_map] at hc
    have hforced :=
      (h305_antipodalSaturatedStar_typeCounts R hRreg u huinj humode i).2.1
    omega
  have hsplit : Inside.card + Outside.card = T.card := by
    exact Finset.card_filter_add_card_filter_not
      (s := T) (p := fun b ↦
        b.1 ∈ h305AntipodalSaturatedStarUnion R u i)
  change 2 ≤ Outside.card
  omega

end

end Erdos85

#print axioms
  Erdos85.h305_antipodalResidualTypeOneTargets_card_two_le

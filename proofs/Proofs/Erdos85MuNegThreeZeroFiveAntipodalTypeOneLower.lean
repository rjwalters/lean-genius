import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCommonTypeBalance
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # Eight cross-shore targets for every antipodal center -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The three endpoint types partition any finset of exterior edges. -/
theorem shoreType_filter_card_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (T : Finset R.edgeFinset) (U : Finset V) :
    (T.filter fun b ↦ (b.1.toFinset ∩ U).card = 0).card +
      (T.filter fun b ↦ (b.1.toFinset ∩ U).card = 1).card +
      (T.filter fun b ↦ (b.1.toFinset ∩ U).card = 2).card = T.card := by
  classical
  let q := fun b : R.edgeFinset ↦ (b.1.toFinset ∩ U).card
  induction T using Finset.induction_on with
  | empty => simp
  | @insert b T hb ih =>
      have hle : q b ≤ 2 := by
        calc
          _ ≤ b.1.toFinset.card := Finset.card_le_card Finset.inter_subset_left
          _ = 2 := R.card_toFinset_mem_edgeFinset b
      change
        ((insert b T).filter fun x ↦ q x = 0).card +
          ((insert b T).filter fun x ↦ q x = 1).card +
          ((insert b T).filter fun x ↦ q x = 2).card = (insert b T).card
      change
        (T.filter fun x ↦ q x = 0).card +
          (T.filter fun x ↦ q x = 1).card +
          (T.filter fun x ↦ q x = 2).card = T.card at ih
      interval_cases htag : q b <;>
        simp [Finset.filter_insert, hb, htag] <;> omega

/-- The exact type-zero population cap and the antipodal weighted balance
force at least eight cross-shore common targets at each antipodal center. -/
theorem h305_antipodal_offDiagonalCommon_typeOne_eight_le
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
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j}) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    8 ≤ offDiagonalCommonShoreTypeCount R Cedge a U 1 := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let T := offDiagonalCommonNeighborSupport Cedge a
  let n := fun t ↦ (T.filter fun b ↦
    (b.1.toFinset ∩ U).card = t).card
  have hTcard : T.card = 30 := by
    have h := offDiagonalCommonNeighborSupport_card_of_regular_not_containsC4
      Cedge hfree 6 hCreg a
    norm_num at h
    exact h
  have hpartition : n 0 + n 1 + n 2 = 30 := by
    have h := shoreType_filter_card_sum R T U
    simpa [n, hTcard] using h
  have hbalance : n 0 = n 2 + 2 := by
    simpa only [n, T, U, offDiagonalCommonShoreTypeCount] using
      (h305_antipodal_offDiagonalCommon_typeZero_eq_typeTwo_add_two
        H R Cedge hservice hHreg hCreg hfree u huinj hu a i j hoffset ha)
  have hpop := h305_correctShoreModes_typePopulations_of_coordinates
    R u v huinj hvinj hdisj hcover humode hvmode hRreg
  have hglobal0 : (shoreTypeEdgeFinset R U 0).card = 12 := by
    simpa [U] using hpop.2.2
  have hsubset0 : (T.filter fun b ↦
      (b.1.toFinset ∩ U).card = 0) ⊆ shoreTypeEdgeFinset R U 0 := by
    intro b hb
    have ht := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩
  have hcap : n 0 ≤ 12 := by
    have := Finset.card_le_card hsubset0
    simpa [n, hglobal0] using this
  change 8 ≤ n 1
  omega

end

end Erdos85

#print axioms Erdos85.shoreType_filter_card_sum
#print axioms Erdos85.h305_antipodal_offDiagonalCommon_typeOne_eight_le

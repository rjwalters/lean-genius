import Proofs.Erdos85MuNegThreeZeroFiveAntipodalTypeZeroLower
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalTripleTarget
import Proofs.Erdos85EdgeIndexedServiceCommonWitnessPacking

/-! # The four coordinate antipodal service centers -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def h305AntipodalCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (i : Fin 4) : R.edgeFinset := by
  let q : ZMod 8 := i.1
  refine ⟨s(u q, u (q + 4)), R.mem_edgeFinset.mpr ?_⟩
  rcases hmode with htri | htf
  · exact (htri q (q + 4)).2 (Or.inr (Or.inl (by ring)))
  · exact (htf q (q + 4)).2 (Or.inr (Or.inl (by ring)))

def h305AntipodalCenterFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) : Finset R.edgeFinset :=
  Finset.univ.image (h305AntipodalCenter R u hmode)

@[simp] theorem h305AntipodalCenter_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (i : Fin 4) :
    (h305AntipodalCenter R u hmode i).1.toFinset =
      {u (i.1 : ZMod 8), u ((i.1 : ZMod 8) + 4)} := by
  exact Sym2.toFinset_mk_eq

theorem h305AntipodalCenter_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    Function.Injective (h305AntipodalCenter R u hmode) := by
  intro i j hij
  apply Fin.ext
  fin_cases i <;> fin_cases j <;>
    simp only [h305AntipodalCenter, Subtype.ext_iff] at hij ⊢ <;>
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq] at hij
  all_goals
    rcases hij with h | h
    · have hh := huinj h.1
      exfalso
      revert hh
      decide
    · have hh := huinj (congrArg Prod.fst h)
      exfalso
      revert hh
      decide

theorem h305AntipodalCenterFinset_card_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    (h305AntipodalCenterFinset R u hmode).card = 4 := by
  rw [h305AntipodalCenterFinset,
    Finset.card_image_of_injective _
      (h305AntipodalCenter_injective R u huinj hmode)]
  decide

theorem h305AntipodalCenterFinset_typeZero_seven_le
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
      MuNegThreeZeroFiveTfShoreMode R u) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    ∀ a ∈ h305AntipodalCenterFinset R u hmode,
      7 ≤ offDiagonalCommonShoreTypeCount R Cedge a U 0 := by
  classical
  dsimp only
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  let q : ZMod 8 := i.1
  apply h305_antipodal_offDiagonalCommon_typeZero_seven_le
    H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu hmode
      (h305AntipodalCenter R u hmode i) q (q + 4)
  · ring
  · exact h305AntipodalCenter_toFinset R u hmode i

/-- Fully coordinated collision package: the four concrete antipodal
centers force an opposite-shore target seen by three centers, together with
packed common-neighbor witnesses for those three incidences. -/
theorem h305_antipodalCenters_exists_tripleTarget_with_witnessPacking
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
    (hzero : (shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 0).card = 12) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    let A := h305AntipodalCenterFinset R u hmode
    ∃ b ∈ shoreTypeEdgeFinset R U 0,
      ∃ S : Finset R.edgeFinset, S ⊆ A ∧ S.card = 3 ∧
        ∃ w : ↥(S : Set R.edgeFinset) → R.edgeFinset,
          (∀ a, Cedge.Adj b (w a) ∧ Cedge.Adj a.1 (w a)) ∧
          ∀ a d, w a ≠ w d →
            Disjoint (w a).1.toFinset (w d).1.toFinset := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let A := h305AntipodalCenterFinset R u hmode
  have hA : A.card = 4 :=
    h305AntipodalCenterFinset_card_four R u huinj hmode
  have hlower : ∀ a ∈ A,
      7 ≤ offDiagonalCommonShoreTypeCount R Cedge a U 0 :=
    h305AntipodalCenterFinset_typeZero_seven_le
      H R Cedge hservice hHreg hRreg hCreg hfree u huinj hu hmode
  obtain ⟨b, hbzero, hbthree⟩ :=
    h305_four_antipodal_centers_have_triple_typeZero_target
      R Cedge U A hA hzero hlower
  refine ⟨b, hbzero, ?_⟩
  exact edgeIndexedService_exists_three_commonWitnesses
    H R Cedge hservice A b hbthree

end

end Erdos85

#print axioms Erdos85.h305AntipodalCenterFinset_card_four
#print axioms
  Erdos85.h305_antipodalCenters_exists_tripleTarget_with_witnessPacking

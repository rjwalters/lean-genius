import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCenters
import Proofs.Erdos85MuNegThreeZeroFiveMiddleProfileParity

/-! # The eight nonantipodal targets on one h305 shore -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The within-shore exterior edges other than the four antipodal centers. -/
def h305SameShoreNonantipodalTargetFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) : Finset R.edgeFinset :=
  shoreTypeEdgeFinset R ((Finset.univ : Finset (ZMod 8)).image u) 2 \
    h305AntipodalCenterFinset R u hmode

/-- Each canonical antipodal center is a type-two edge of its shore. -/
theorem h305AntipodalCenterFinset_subset_typeTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    h305AntipodalCenterFinset R u hmode ⊆
      shoreTypeEdgeFinset R
        ((Finset.univ : Finset (ZMod 8)).image u) 2 := by
  classical
  intro a ha
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  simp only [shoreTypeEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, h305AntipodalCenter_toFinset]
  have hi : u (i.1 : ZMod 8) ∈
      (Finset.univ : Finset (ZMod 8)).image u := by simp
  have hi4 : u ((i.1 : ZMod 8) + 4) ∈
      (Finset.univ : Finset (ZMod 8)).image u := by simp
  have hne : u (i.1 : ZMod 8) ≠ u ((i.1 : ZMod 8) + 4) := by
    apply huinj.ne
    fin_cases i <;> decide
  simp [hi, hi4, hne]

/-- There are exactly eight nonantipodal targets on either corrected shore. -/
theorem h305SameShoreNonantipodalTargetFinset_card_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    (h305SameShoreNonantipodalTargetFinset R u hmode).card = 8 := by
  rw [h305SameShoreNonantipodalTargetFinset,
    Finset.card_sdiff_of_subset
      (h305AntipodalCenterFinset_subset_typeTwo R u huinj hmode),
    h305_correctShoreMode_typeTwo_card_twelve R u huinj hmode,
    h305AntipodalCenterFinset_card_four R u huinj hmode]

/-- An offset-four coordinate edge is one of the four canonical antipodal
centers. -/
theorem mem_h305AntipodalCenterFinset_of_offset_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u j}) (hij : j - i = 4) :
    a ∈ h305AntipodalCenterFinset R u hmode := by
  classical
  have hj : j = i + 4 := by
    rw [sub_eq_iff_eq_add] at hij
    simpa [add_comm] using hij
  subst j
  simp only [h305AntipodalCenterFinset, Finset.mem_image]
  let q : Fin 4 := ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  have hcoord : ({(q : ZMod 8), (q : ZMod 8) + 4} : Finset (ZMod 8)) =
      {i, i + 4} := by
    fin_cases i <;> native_decide
  have hpair : ({u (q : ZMod 8), u ((q : ZMod 8) + 4)} : Finset V) =
      {u i, u (i + 4)} := by
    simpa using congrArg (Finset.image u) hcoord
  refine ⟨q, Finset.mem_univ _, ?_⟩
  apply Subtype.ext
  apply Sym2.ext
  intro x
  rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset,
    h305AntipodalCenter_toFinset, ha]
  exact Finset.ext_iff.mp hpair x

/-- Every member of the canonical eight-target set has same-shore
coordinates at an odd offset, exactly the hypothesis needed by the cubic
row bound. -/
theorem h305SameShoreNonantipodalTarget_exists_oddCoordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (a : R.edgeFinset)
    (ha : a ∈ h305SameShoreNonantipodalTargetFinset R u hmode) :
    ∃ i j : ZMod 8, a.1.toFinset = {u i, u j} ∧
      (j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7) := by
  classical
  have hatype : a ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 2 :=
    (Finset.mem_sdiff.mp ha).1
  have han : a ∉ h305AntipodalCenterFinset R u hmode :=
    (Finset.mem_sdiff.mp ha).2
  obtain ⟨i, j, haij, hoff⟩ :=
    h305_typeTwoEdge_exists_coordinate_endpoints R u hmode a hatype
  refine ⟨i, j, haij, ?_⟩
  rcases hoff with h1 | h3 | h4 | h5 | h7
  · exact Or.inl h1
  · exact Or.inr (Or.inl h3)
  · exact False.elim (han
      (mem_h305AntipodalCenterFinset_of_offset_four
        R u huinj hmode a i j haij h4))
  · exact Or.inr (Or.inr (Or.inl h5))
  · exact Or.inr (Or.inr (Or.inr h7))

end


end Erdos85

#print axioms Erdos85.h305SameShoreNonantipodalTargetFinset_card_eight
#print axioms Erdos85.h305SameShoreNonantipodalTarget_exists_oddCoordinates

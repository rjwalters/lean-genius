import Proofs.Erdos85CubicStructuralExcessBaseline
import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCenters
import Proofs.Erdos85MuNegThreeZeroFiveGraphProfileLedger

/-! # The forty nonantipodal targets in the h305 two-shore model -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def h305NonantipodalTargetFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v) : Finset R.edgeFinset :=
  let U := (Finset.univ : Finset (ZMod 8)).image u
  shoreTypeEdgeFinset R U 1 ∪
    (shoreTypeEdgeFinset R U 2 \ h305AntipodalCenterFinset R u humode) ∪
    (shoreTypeEdgeFinset R U 0 \ h305AntipodalCenterFinset R v hvmode)

private theorem antipodalCenters_subset_typeTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    h305AntipodalCenterFinset R u hmode ⊆
      shoreTypeEdgeFinset R
        ((Finset.univ : Finset (ZMod 8)).image u) 2 := by
  classical
  intro a ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [h305AntipodalCenter_toFinset]
  have hq0 : u (q.1 : ZMod 8) ∈
      (Finset.univ : Finset (ZMod 8)).image u :=
    Finset.mem_image.mpr ⟨(q.1 : ZMod 8), Finset.mem_univ _, rfl⟩
  have hq4 : u ((q.1 : ZMod 8) + 4) ∈
      (Finset.univ : Finset (ZMod 8)).image u :=
    Finset.mem_image.mpr ⟨(q.1 : ZMod 8) + 4, Finset.mem_univ _, rfl⟩
  have hne : u (q.1 : ZMod 8) ≠ u ((q.1 : ZMod 8) + 4) := by
    intro h
    have hadj := (hmode.elim
      (fun hm ↦ (hm (q.1 : ZMod 8) ((q.1 : ZMod 8) + 4)).2
        (Or.inr (Or.inl (by ring_nf))))
      (fun hm ↦ (hm (q.1 : ZMod 8) ((q.1 : ZMod 8) + 4)).2
        (Or.inr (Or.inl (by ring_nf)))))
    exact R.loopless.irrefl _ (h ▸ hadj)
  simp [hq0, hq4, hne]

private theorem antipodalCenters_otherShore_subset_typeZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V) (hdisj : ∀ i j, u i ≠ v j)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v) :
    h305AntipodalCenterFinset R v hvmode ⊆
      shoreTypeEdgeFinset R
        ((Finset.univ : Finset (ZMod 8)).image u) 0 := by
  classical
  intro a ha
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [h305AntipodalCenter_toFinset]
  have hnot (k : ZMod 8) : v k ∉
      (Finset.univ : Finset (ZMod 8)).image u := by
    intro hk
    obtain ⟨i, hi, h⟩ := Finset.mem_image.mp hk
    exact hdisj i k h
  simp [hnot]

private theorem shoreTypeEdgeFinset_disjoint_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (U : Finset V)
    {r s : ℕ} (hrs : r ≠ s) :
    Disjoint (shoreTypeEdgeFinset R U r) (shoreTypeEdgeFinset R U s) := by
  rw [Finset.disjoint_left]
  intro a har has
  have hr := (Finset.mem_filter.mp har).2
  have hs := (Finset.mem_filter.mp has).2
  exact hrs (hr.symm.trans hs)

/-- The 24 cross targets and the eight nonantipodal targets on each shore
form a forty-element family. -/
theorem h305NonantipodalTargetFinset_card_forty
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ i j, u i ≠ v j)
    (hcover : ∀ x : V, (∃ i, x = u i) ∨ ∃ j, x = v j)
    (humode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hvmode : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hreg : ∀ x, R.degree x = 6) :
    (h305NonantipodalTargetFinset R u v humode hvmode).card = 40 := by
  classical
  let U := (Finset.univ : Finset (ZMod 8)).image u
  let T0 := shoreTypeEdgeFinset R U 0
  let T1 := shoreTypeEdgeFinset R U 1
  let T2 := shoreTypeEdgeFinset R U 2
  let AU := h305AntipodalCenterFinset R u humode
  let AV := h305AntipodalCenterFinset R v hvmode
  obtain ⟨hT2, hT1, hT0⟩ :=
    h305_correctShoreModes_typePopulations_of_coordinates
      R u v huinj hvinj hdisj hcover humode hvmode hreg
  have hAUcard : AU.card = 4 :=
    h305AntipodalCenterFinset_card_four R u huinj humode
  have hAVcard : AV.card = 4 :=
    h305AntipodalCenterFinset_card_four R v hvinj hvmode
  have hAUsub : AU ⊆ T2 := antipodalCenters_subset_typeTwo R u humode
  have hAVsub : AV ⊆ T0 :=
    antipodalCenters_otherShore_subset_typeZero R u v hdisj hvmode
  have h2diff : (T2 \ AU).card = 8 := by
    rw [Finset.card_sdiff_of_subset hAUsub, hT2, hAUcard]
  have h0diff : (T0 \ AV).card = 8 := by
    rw [Finset.card_sdiff_of_subset hAVsub, hT0, hAVcard]
  have h12 : Disjoint T1 (T2 \ AU) :=
    (shoreTypeEdgeFinset_disjoint_of_ne R U (by omega)).mono_right
      (Finset.sdiff_subset)
  have h10 : Disjoint T1 (T0 \ AV) :=
    (shoreTypeEdgeFinset_disjoint_of_ne R U (by omega)).mono_right
      (Finset.sdiff_subset)
  have h20 : Disjoint (T2 \ AU) (T0 \ AV) :=
    (shoreTypeEdgeFinset_disjoint_of_ne R U (by omega)).mono
      Finset.sdiff_subset Finset.sdiff_subset
  have hdisjUnion : Disjoint (T1 ∪ (T2 \ AU)) (T0 \ AV) :=
    Finset.disjoint_union_left.mpr ⟨h10, h20⟩
  change (T1 ∪ (T2 \ AU) ∪ (T0 \ AV)).card = 40
  rw [Finset.card_union_of_disjoint hdisjUnion,
    Finset.card_union_of_disjoint h12, hT1, h2diff, h0diff]

end

end Erdos85

#print axioms Erdos85.h305NonantipodalTargetFinset_card_forty

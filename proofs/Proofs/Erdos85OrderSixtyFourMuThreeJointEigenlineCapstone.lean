import Proofs.Erdos85OrderSixtyFourMuThreeMixedGridAssembly
import Proofs.Erdos85MuThreeKSymmetryCandidateSlots
import Proofs.Erdos85MuThreeMixedGridCodeNativeAdapter
import Proofs.Erdos85MuThreeFixedKSlotManifest

/-!
# Order-64 joint-eigenline `μ = 3` capstone

This is the final graph-facing socket for the signed size-two `μ = 3`
branch.  The structural argument constructs the actual mixed-grid code; a
shape/sector-specific `K`-classification and its checked certificates then
contradict that code.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Edge-status constancy on connected components is the usable form of
factor-cycle compatibility; for a two-regular relation it also reconstructs
the original componentwise all-or-none formulation. -/
theorem relationFactorCycleCompatible_of_twoRegular_of_edgeStatusComponentwise
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (hH : RelationTwoRegular H)
    (hstatus : RelationEdgeStatusComponentwise H K) :
    RelationFactorCycleCompatible H K := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h z =>
      cases z with
      | inl x =>
          have hcard := hH.1 x
          have hne : ((Finset.univ : Finset Y).filter fun y => H x y).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr (by
              intro he
              rw [he] at hcard
              simp at hcard)
          obtain ⟨y, hy⟩ := hne
          have hxy : H x y := (Finset.mem_filter.mp hy).2
          by_cases hk : K x y
          · left
            intro x' y' hx'y' hx'c
            have hreach : (relationBipartiteGraph H).Reachable
                (Sum.inl x) (Sum.inl x') := by
              apply SimpleGraph.ConnectedComponent.exact
              exact ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hx'c).symm
            exact (hstatus hxy hx'y' hreach).mp hk
          · right
            intro x' y' hx'y' hx'c
            intro hk'
            have hreach : (relationBipartiteGraph H).Reachable
                (Sum.inl x) (Sum.inl x') := by
              apply SimpleGraph.ConnectedComponent.exact
              exact ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hx'c).symm
            exact hk ((hstatus hxy hx'y' hreach).mpr hk')
      | inr y =>
          have hcard := hH.2 y
          have hne : ((Finset.univ : Finset X).filter fun x => H x y).Nonempty :=
            Finset.nonempty_iff_ne_empty.mpr (by
              intro he
              rw [he] at hcard
              simp at hcard)
          obtain ⟨x, hx⟩ := hne
          have hxy : H x y := (Finset.mem_filter.mp hx).2
          have hrep : Sum.inl x ∈
              ((relationBipartiteGraph H).connectedComponentMk (Sum.inr y)).supp := by
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
            exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
          by_cases hk : K x y
          · left
            intro x' y' hx'y' hx'c
            have hreach : (relationBipartiteGraph H).Reachable
                (Sum.inl x) (Sum.inl x') := by
              apply SimpleGraph.ConnectedComponent.exact
              exact ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hrep).trans
                (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hx'c).symm)
            exact (hstatus hxy hx'y' hreach).mp hk
          · right
            intro x' y' hx'y' hx'c
            intro hk'
            have hreach : (relationBipartiteGraph H).Reachable
                (Sum.inl x) (Sum.inl x') := by
              apply SimpleGraph.ConnectedComponent.exact
              exact ((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hrep).trans
                (((SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hx'c).symm)
            exact hk ((hstatus hxy hx'y' hreach).mpr hk')

/-- Coordinate relabeling induces an equivalence of occupied mixed cells. -/
def muThreeNormalizeCellEquiv
    {X Y : Type*} (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (K : X → Y → Prop) :
    muThreeMixedCell (mu3NormalizeRelation row column K) ≃
      muThreeMixedCell K where
  toFun p := ⟨(row.symm p.1.1, column.symm p.1.2), p.2⟩
  invFun p := ⟨(row p.1.1, column p.1.2), by
    simpa [mu3NormalizeRelation] using p.2⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

/-- A mixed-grid code is invariant under independent relabeling of its two
shores.  This is the bridge from graph-native shores to the certificate's
`Fin 8 × Fin 8` coordinates. -/
def MuThreeMixedGridCode.normalize
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    MuThreeMixedGridCode
      (mu3NormalizeRelation row column H)
      (mu3NormalizeRelation row column K)
      (C.comap (muThreeNormalizeCellEquiv row column K)) := by
  let e := muThreeNormalizeCellEquiv row column K
  let Hn := mu3NormalizeRelation row column H
  let Kn := mu3NormalizeRelation row column K
  let Cn := C.comap e
  have hHtwo : RelationTwoRegular Hn :=
    mu3NormalizeRelation_twoRegular row column H code.H_twoRegular
  have hKtwo : RelationTwoRegular Kn :=
    mu3NormalizeRelation_twoRegular row column K code.K_twoRegular
  refine {
    card_left := by simp
    card_right := by simp
    H_twoRegular := hHtwo
    K_twoRegular := hKtwo
    cycle_compatible := relationFactorCycleCompatible_of_twoRegular_of_edgeStatusComponentwise
      Hn Kn hHtwo
        ((code.cycle_compatible.edgeStatusComponentwise H K).normalize
          row column H K)
    row_hit := ?_
    column_hit := ?_
    rook := ?_
    c4Free := ?_ }
  · intro u x
    have hcard :
        ((Cn.neighborFinset u).filter fun v => v.1.1 = x).card =
          ((C.neighborFinset (e u)).filter fun v =>
            v.1.1 = row.symm x).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        have hp := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨by simpa [Cn] using hp.1, by
          change row.symm v.1.1 = row.symm x
          exact congrArg row.symm hp.2⟩
      · intro a _ b _ hab
        exact e.injective hab
      · intro v hv
        refine ⟨e.symm v, ?_, by simp⟩
        apply Finset.mem_filter.mpr
        have hp := Finset.mem_filter.mp hv
        exact ⟨by simpa [Cn] using hp.1, by
          change row v.1.1 = x
          simpa using congrArg row hp.2⟩
    rw [hcard, code.row_hit]
    rfl
  · intro u y
    have hcard :
        ((Cn.neighborFinset u).filter fun v => v.1.2 = y).card =
          ((C.neighborFinset (e u)).filter fun v =>
            v.1.2 = column.symm y).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        have hp := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨by simpa [Cn] using hp.1, by
          change column.symm v.1.2 = column.symm y
          exact congrArg column.symm hp.2⟩
      · intro a _ b _ hab
        exact e.injective hab
      · intro v hv
        refine ⟨e.symm v, ?_, by simp⟩
        apply Finset.mem_filter.mpr
        have hp := Finset.mem_filter.mp hv
        exact ⟨by simpa [Cn] using hp.1, by
          change column v.1.2 = y
          simpa using congrArg column hp.2⟩
    rw [hcard, code.column_hit]
    rfl
  · intro u v w huv huw hvw
    have h := code.rook (e u) (e v) (e w)
      (by simpa [Cn] using huv) (by simpa [Cn] using huw)
      (fun heq => hvw (e.injective heq))
    constructor
    · intro heq
      apply h.1
      change row.symm v.1.1 = row.symm w.1.1
      exact congrArg row.symm heq
    · intro heq
      apply h.2
      change column.symm v.1.2 = column.symm w.1.2
      exact congrArg column.symm heq
  · rintro ⟨f, hf, hadj⟩
    apply code.c4Free
    exact ⟨fun i => e (f i), e.injective.comp hf, fun i j hij => by
      simpa [Cn] using hadj i j hij⟩

/-- Package the H16 exhaustive provider once a certificate consumer for the
22 concrete slots has been supplied. -/
def muThreeKSymmetryClassification_H16
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H16Row x.val)
    (himpossible : ∀ (slot : Mu3KCandidateSlot)
      (dK : DecidableRel (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot))
      (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot)))
      [dC : DecidableRel C.Adj],
      ¬ @MuThreeMixedGridCode X Y _ _ _ _ H
        (muThreeKCandidateRel (mu3SlotCandidate row column) slot)
        _ dK C dC) :
    MuThreeKSymmetryClassification H where
  Index := Mu3KCandidateSlot
  candidate := mu3SlotCandidate row column
  exhaustive := by
    intro K dK data
    exact exists_mu3SlotCandidate_of_allSectorCandidate row column K
      (exists_mu3AllSectorCandidate_H16 row column H K
        data.H_twoRegular data.K_twoRegular data.cycle_compatible hHcoord
        data.row_symmetry data.column_symmetry)
  impossible := himpossible

/-- H88 version of `muThreeKSymmetryClassification_H16`. -/
def muThreeKSymmetryClassification_H88
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H88Row x.val)
    (himpossible : ∀ (slot : Mu3KCandidateSlot)
      (dK : DecidableRel (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot))
      (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot)))
      [dC : DecidableRel C.Adj],
      ¬ @MuThreeMixedGridCode X Y _ _ _ _ H
        (muThreeKCandidateRel (mu3SlotCandidate row column) slot)
        _ dK C dC) :
    MuThreeKSymmetryClassification H where
  Index := Mu3KCandidateSlot
  candidate := mu3SlotCandidate row column
  exhaustive := by
    intro K dK data
    exact exists_mu3SlotCandidate_of_allSectorCandidate row column K
      (exists_mu3AllSectorCandidate_H88 row column H K
        data.H_twoRegular data.K_twoRegular data.cycle_compatible hHcoord
        data.row_symmetry data.column_symmetry)
  impossible := himpossible

/-- H106 version of `muThreeKSymmetryClassification_H16`. -/
def muThreeKSymmetryClassification_H106
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (row : X ≃ Fin 8) (column : Y ≃ Fin 8)
    (H : X → Y → Prop) [DecidableRel H]
    (hHcoord : ∀ x y, mu3NormalizeRelation row column H x y ↔
      y.val ∈ mu3H106Row x.val)
    (himpossible : ∀ (slot : Mu3KCandidateSlot)
      (dK : DecidableRel (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot))
      (C : SimpleGraph (muThreeMixedCell (muThreeKCandidateRel
        (mu3SlotCandidate row column) slot)))
      [dC : DecidableRel C.Adj],
      ¬ @MuThreeMixedGridCode X Y _ _ _ _ H
        (muThreeKCandidateRel (mu3SlotCandidate row column) slot)
        _ dK C dC) :
    MuThreeKSymmetryClassification H where
  Index := Mu3KCandidateSlot
  candidate := mu3SlotCandidate row column
  exhaustive := by
    intro K dK data
    exact exists_mu3SlotCandidate_of_allSectorCandidate row column K
      (exists_mu3AllSectorCandidate_H106 row column H K
        data.H_twoRegular data.K_twoRegular data.cycle_compatible hHcoord
        data.row_symmetry data.column_symmetry)
  impossible := himpossible

/-- A complete `K`-symmetry classification for the internal signed factor
rules out the corresponding order-64 joint eigenline. -/
theorem false_of_orderSixtyFour_mu3_jointEigenline
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
      s y = 3 * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (classification : MuThreeKSymmetryClassification
      (orderSixtyFourMuThreeInternalRel G
        (cSupp := c.supp) (s := s))) : False := by
  obtain ⟨label, hinj, code⟩ := orderSixtyFour_muThree_exists_mixedGridCode
    G hfree hreg hcardV c hc s hs_in hs_out hsum hDs hA_in hA_out
  exact false_of_muThreeMixedGridCode_of_kSymmetryClassification
    (orderSixtyFourMuThreeInternalRel G)
    (orderSixtyFourMuThreeHole label)
    (orderSixtyFourMuThreeExteriorCellGraph G label hinj)
    classification code

end


end Erdos85

#print axioms Erdos85.false_of_orderSixtyFour_mu3_jointEigenline

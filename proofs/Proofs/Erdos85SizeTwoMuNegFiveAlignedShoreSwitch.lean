import Proofs.Erdos85SizeTwoMuNegFiveSectorSwitchRouting
import Proofs.Erdos85SizeTwoAlignedShoreSwitch
import Proofs.Erdos85EightEightCoordinateCover
import Proofs.Erdos85ComponentSignFlipEigenvector
import Proofs.Erdos85SizeTwoSwitchedJointExclusions
import Proofs.Erdos85SizeTwoSwitchedJointExtension

/-! # General aligned shore switch for the `mu=-5` lane -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- One shared `mu=-5` witness carrying the quotient and signed ledgers,
its exact six-cell classification, and the genuine switched joint
eigenvector. -/
theorem orderSixtyFour_sizeTwo_muNegFive_aligned_shoreSwitch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    ∃ k r : ℕ, MuNegFiveSectorCells k r ∧
      let B := (Finset.univ : Finset c.supp).filter
        (fun x ↦ H.connectedComponentMk x = b)
      let t : c.supp → ℤ := fun x ↦ if x ∈ B then -s x.1 else s x.1
      (K.adjMatrix ℤ).mulVec t = sizeTwoMuSwitchTarget (-5) k r • t ∧
      (H.adjMatrix ℤ).mulVec t = (-2 : ℤ) • t ∧ t ≠ 0 ∧
      (∀ x, t x = -1 ∨ t x = 1) ∧
      sizeTwoMuSwitchTarget (-5) k r ≠ 1 ∧
      MuNegFivePostMuOneSectorCells k r ∧
      (sizeTwoMuSwitchTarget (-5) k r = -3 ∨
       sizeTwoMuSwitchTarget (-5) k r = -1 ∨
       sizeTwoMuSwitchTarget (-5) k r = 3) ∧
      ((∃ s', IsAmbientSignedJoint G c (-3) s') ∨
       (∃ s', IsAmbientSignedJoint G c (-1) s') ∨
       (∃ s', IsAmbientSignedJoint G c 3 s')) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨ha8, hb8, r, hr2, hr7, haa, habq, hbaq, hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
  obtain ⟨k, hk, hAA, hBB, hAB, hBA⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
  have hdegree : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc x
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hcover : ∀ x : c.supp, x ∈ a.supp ∨ x ∈ b.supp :=
    eightEight_shores_cover G c (by simpa using hc) a b hab
      u v huinj hvinj hurange hvrange
  have hsign : ∀ x : c.supp, s x.1 = -1 ∨ s x.1 = 1 :=
    fun x ↦ hs_in x.1 x.2
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hvrangeB : Set.range v = ↑B := by
    rw [hvrange]
    ext x
    simp [B]
  have hu0A : u 0 ∈ A := by
    change u 0 ∈ (↑A : Set c.supp)
    rw [← hurangeA]
    exact ⟨0, rfl⟩
  let N : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  have hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (u j)) by
      ext j; simp [N, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K A u huinj hurangeA (u 0)]
    have hq : (componentNeighborFinset K H a (u 0)).card = 7 - r := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hdegree hcomm
        a a (by simpa [A] using hu0A)]
      exact haa
    have heq : A.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K H a (u 0) := by
      ext y
      simp [A, H, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hq
  have hMrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      M 0 j = 1).card = r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K B v hvinj hvrangeB (u 0)]
    have hq : (componentNeighborFinset K H b (u 0)).card = r := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hdegree hcomm
        a b (by simpa [A] using hu0A)]
      exact habq
    have heq : B.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K H b (u 0) := by
      ext y
      simp [B, H, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hq
  have hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j).1 = s (u 0).1 ∧ N 0 j = 1).card = k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u 0).1 ∧ N 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (u j).1 = s (u 0).1 ∧ K.Adj (u 0) (u j)) by
      ext j; simp [N, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) 0]
    exact hAA (u 0) hu0A
  have hMsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (v j).1 = s (u 0).1 ∧ M 0 j = 1).card = 1 - k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (u 0).1 ∧ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (v j).1 = s (u 0).1 ∧ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support_from K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) (u 0)]
    exact hAB (u 0) hu0A
  have hfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hflip (w : ZMod 8 → c.supp)
      (hw : ∀ z, H.neighborFinset (w z) = {w (z - 1), w (z + 1)}) :
      ∀ i, s (w (i + 1)).1 = -s (w i).1 := by
    intro i
    have hadj : H.Adj (w i) (w (i + 1)) := by
      rw [← H.mem_neighborFinset, hw]
      simp
    have hmem : (w (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (w i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (w (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hfull (w i).2).2 _ hmem
  have hbounds := alternating_C8_internal_cross_parameter_bounds_one N M
    (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r hk
    (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
    (hflip u hu) (hflip v hv) hNrow hNsame hMrow hMsame
  have hcell := muNegFive_sector_cells_of_bounds k r hk hr2 hr7
    hbounds.1 hbounds.2.1 hbounds.2.2.1 hbounds.2.2.2
  have same_eq (p : H.ConnectedComponent)
      (P : Finset c.supp) (hP : P = Finset.univ.filter fun y ↦ y ∈ p.supp)
      (x : c.supp) :
      (P.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1) =
        (componentNeighborFinset K H p x).filter
          (fun y ↦ s y.1 = s x.1) := by
    subst P
    ext y
    simp [componentNeighborFinset, H, and_left_comm, and_assoc]
  have hAA' : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset K H a x).filter
        (fun y ↦ s y.1 = s x.1)).card = k := by
    intro x hx
    rw [← same_eq a A rfl x]
    exact hAA x (by simpa [A] using hx)
  have hAB' : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset K H b x).filter
        (fun y ↦ s y.1 = s x.1)).card = 1 - k := by
    intro x hx
    rw [← same_eq b B rfl x]
    exact hAB x (by simpa [A] using hx)
  have hBB' : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset K H b x).filter
        (fun y ↦ s y.1 = s x.1)).card = k := by
    intro x hx
    rw [← same_eq b B rfl x]
    exact hBB x (by simpa [B] using hx)
  have hBA' : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset K H a x).filter
        (fun y ↦ s y.1 = s x.1)).card = 1 - k := by
    intro x hx
    rw [← same_eq a A rfl x]
    exact hBA x (by simpa [B] using hx)
  let t : c.supp → ℤ := fun x ↦ if x ∈
      (Finset.univ : Finset c.supp).filter
        (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1
  have htKraw := twoComponent_quotient_signSwitch_adjMatrix_eigen_sub_of_card
    K H a b hab hdegree hcomm hcover (fun x ↦ s x.1)
      (7-r) k r (1-k) hsign haa habq hbaq hbb hAA' hAB' hBB' hBA'
  have hcoeff :
      (2 * (k : ℤ) - (7-r : ℕ)) - (2 * (1-k : ℕ) - (r : ℤ)) =
        sizeTwoMuSwitchTarget (-5) k r := by
    rcases hcell with h | h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]
  have htK : (K.adjMatrix ℤ).mulVec t =
      sizeTwoMuSwitchTarget (-5) k r • t := by
    simpa only [t, hcoeff] using htKraw
  have hsH : (H.adjMatrix ℤ).mulVec (fun x : c.supp ↦ s x.1) =
      (-2 : ℤ) • (fun x : c.supp ↦ s x.1) := by
    funext x
    rw [induce_adjMatrix_mulVec_restrict_apply]
    simpa [ConnectedComponent.mem_supp_iff, smul_eq_mul] using hH x.1 x.2
  have htH : (H.adjMatrix ℤ).mulVec t = (-2 : ℤ) • t := by
    simpa [t, Finset.mem_filter] using
      (connectedComponent_signFlip_adjMatrix_eigenvector
        H b (fun x : c.supp ↦ s x.1) (-2) hsH)
  have htsign : ∀ x, t x = -1 ∨ t x = 1 := by
    intro x
    have hx := hs_in x.1 x.2
    by_cases hm : x ∈ (Finset.univ : Finset c.supp).filter
        (fun y ↦ H.connectedComponentMk y = b)
    · change (if x ∈ (Finset.univ : Finset c.supp).filter
          (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) = -1 ∨
        (if x ∈ (Finset.univ : Finset c.supp).filter
          (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) = 1
      simp only [hm, if_true]
      omega
    · change (if x ∈ (Finset.univ : Finset c.supp).filter
          (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) = -1 ∨
        (if x ∈ (Finset.univ : Finset c.supp).filter
          (fun y ↦ H.connectedComponentMk y = b) then -s x.1 else s x.1) = 1
      simpa only [hm, if_false] using hx
  have htne : t ≠ 0 := by
    intro hz
    have hx := congrFun hz (u 0)
    rcases htsign (u 0) with h | h <;> rw [h] at hx <;> norm_num at hx
  have hneOne := orderSixtyFour_sizeTwoPart_inducedSignedJoint_switchTarget_ne_one
    G hfree hreg hcard c hc t htsign (sizeTwoMuSwitchTarget (-5) k r)
      (by simpa [H] using htH) (by simpa [K] using htK)
  have hpost := muNegFive_postMuOne_sector_cells_of_target_ne_one
    k r hcell hneOne
  have hroute := muNegFive_inducedSwitch_ambientCrossLane
    G c k r hpost t htsign (by simpa [H] using htH) (by simpa [K] using htK)
  exact ⟨k, r, hcell, htK, htH, htne, htsign, hneOne, hpost,
    muNegFive_postMuOne_switch_target k r hpost, hroute⟩

/-- Hide the aligned induced switch and expose only the three ambient
cross-lane witnesses consumed by the final callbacks. -/
theorem orderSixtyFour_sizeTwo_muNegFive_ambientCrossLane
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    (∃ w, IsAmbientSignedJoint G c (-3) w) ∨
      (∃ w, IsAmbientSignedJoint G c (-1) w) ∨
      (∃ w, IsAmbientSignedJoint G c 3 w) := by
  obtain ⟨k, r, _hcell, hK, hHt, _htne, htsign, _hneOne, hpost, _htargets⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_aligned_shoreSwitch
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  exact muNegFive_inducedSwitch_ambientCrossLane
    G c k r hpost _ htsign hHt hK

/-- Final callback form of the general `mu=-5` C8+C8 switch route. -/
theorem false_of_orderSixtyFour_sizeTwo_muNegFive_eightEight_of_crossLane_terminals
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (h3 : ∀ w, IsAmbientSignedJoint G c (-3) w → False)
    (h1 : ∀ w, IsAmbientSignedJoint G c (-1) w → False)
    (hpos : ∀ w, IsAmbientSignedJoint G c 3 w → False) : False := by
  apply false_of_muNegFive_ambientCrossLane G c
    (orderSixtyFour_sizeTwo_muNegFive_ambientCrossLane
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv)
    h3 h1 hpos

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_aligned_shoreSwitch
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_ambientCrossLane
#print axioms Erdos85.false_of_orderSixtyFour_sizeTwo_muNegFive_eightEight_of_crossLane_terminals

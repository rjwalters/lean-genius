import Proofs.Erdos85SizeTwoMuNegThreeEightEightDiagonalSameShape
import Proofs.Erdos85SizeTwoMuNegFiveEightEightSignedParameter

/-! # The two signed diagonal shapes in the `mu=-5` eight-plus-eight stratum -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxHeartbeats 1200000 in
/-- In normalized coordinates for the two ambient C8 components at
`mu=-5`, both diagonal defect blocks have the same one of the two signed
shapes controlled by a single `k ≤ 1`. -/
theorem orderSixtyFour_sizeTwo_muNegFive_eightEight_diagonalSame_shapes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
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
    let K := (secondOrderDefectGraph G).induce c.supp
    ∃ k : ℕ, k ≤ 1 ∧
      ZModEightSameSignShape
        (fun i j ↦ K.adjMatrix ℤ (u i) (u j))
        (fun i ↦ s (u i).1) k ∧
      ZModEightSameSignShape
        (fun i j ↦ K.adjMatrix ℤ (v i) (v j))
        (fun i ↦ s (v i).1) k := by
  classical
  dsimp only
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨k, hk, hA, hB, _hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
  have hcomm : K.adjMatrix ℤ * Hc.adjMatrix ℤ =
      Hc.adjMatrix ℤ * K.adjMatrix ℤ := by
    exact (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have flip_of_coordinates
      (w : ZMod 8 → c.supp)
      (hw : ∀ z, Hc.neighborFinset (w z) = {w (z - 1), w (z + 1)}) :
      ∀ i, s (w (i + 1)).1 = -s (w i).1 := by
    intro i
    have hadj : Hc.Adj (w i) (w (i + 1)) := by
      rw [← Hc.mem_neighborFinset, hw]
      simp
    have hmem : (w (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (w i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (w (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (w i).2).2 _ hmem
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hvrangeB : Set.range v = ↑B := by
    rw [hvrange]
    ext x
    simp [B]
  have hdegreeU : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u i).1 ∧ K.Adj (u i) (u j)).card = k := by
    intro i
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) i]
    exact hA (u i) (by
      change u i ∈ A
      change u i ∈ (↑A : Set c.supp)
      rw [← hurangeA]
      exact ⟨i, rfl⟩)
  have hdegreeV : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (v i).1 ∧ K.Adj (v i) (v j)).card = k := by
    intro i
    rw [coordinate_sameSign_adj_card_eq_support K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) i]
    exact hB (v i) (by
      change v i ∈ B
      change v i ∈ (↑B : Set c.supp)
      rw [← hvrangeB]
      exact ⟨i, rfl⟩)
  refine ⟨k, hk, ?_, ?_⟩
  · exact graph_zmodEight_sameSign_shape_of_comm Hc K u huinj hu
      (fun x : c.supp ↦ s x.1) k (by omega) (fun i ↦ hs_in _ (u i).2)
      (flip_of_coordinates u hu) hcomm hdegreeU
  · exact graph_zmodEight_sameSign_shape_of_comm Hc K v hvinj hv
      (fun x : c.supp ↦ s x.1) k (by omega) (fun i ↦ hs_in _ (v i).2)
      (flip_of_coordinates v hv) hcomm hdegreeV

set_option maxHeartbeats 1200000 in
/-- Coordinate-free package: two distinct internal components in the
`mu=-5` size-two branch admit simultaneous C8 coordinates in which both
diagonal signed defect blocks have the same classified shape. -/
theorem orderSixtyFour_sizeTwo_muNegFive_eightEight_exists_diagonalSame_shapes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
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
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    let Hc := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    ∃ (u v : ZMod 8 → c.supp) (k : ℕ),
      Function.Injective u ∧ Function.Injective v ∧
      Set.range u = a.supp ∧ Set.range v = b.supp ∧
      (∀ z, Hc.neighborFinset (u z) = {u (z - 1), u (z + 1)}) ∧
      (∀ z, Hc.neighborFinset (v z) = {v (z - 1), v (z + 1)}) ∧
      k ≤ 1 ∧
      ZModEightSameSignShape
        (fun i j ↦ K.adjMatrix ℤ (u i) (u j))
        (fun i ↦ s (u i).1) k ∧
      ZModEightSameSignShape
        (fun i j ↦ K.adjMatrix ℤ (v i) (v j))
        (fun i ↦ s (v i).1) k := by
  classical
  dsimp only
  let Hc := G.induce c.supp
  obtain ⟨ha8, hb8, _r, _hr2, _hr7, _haa, _habq, _hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
  have hHdegree : ∀ z : c.supp, Hc.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  obtain ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv⟩ :=
    exists_zmodEight_twoComponent_coordinates Hc hHdegree a b ha8 hb8
  obtain ⟨k, hk, hshapeU, hshapeV⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_eightEight_diagonalSame_shapes
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
      u v huinj hvinj hurange hvrange hu hv
  exact ⟨u, v, k, huinj, hvinj, hurange, hvrange, hu, hv,
    hk, hshapeU, hshapeV⟩


end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_eightEight_diagonalSame_shapes
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_eightEight_exists_diagonalSame_shapes

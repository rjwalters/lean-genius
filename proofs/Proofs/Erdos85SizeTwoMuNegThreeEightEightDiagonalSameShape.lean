import Proofs.Erdos85SizeTwoMuNegThreeEightEightSignedParameterConsumer
import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalMatching
import Proofs.Erdos85ZModEightMixedSelfIntertwinerExclusion
import Proofs.Erdos85EightEightNormalizedCoordinates

/-! # The three signed diagonal shapes in the `mu=-3` eight-plus-eight stratum -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The three possible same-sign supports of a loopless signed C8 block. -/
def ZModEightSameSignShape
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f : ZMod 8 → ℤ) (k : ℕ) : Prop :=
  (k = 0 ∧ ∀ i j, f j = f i → M i j ≠ 1) ∨
  (k = 1 ∧ ∀ i j, f j = f i → (M i j = 1 ↔ j - i = 4)) ∨
  (k = 2 ∧ ∀ i j, f j = f i →
    (M i j = 1 ↔ j - i = 2 ∨ j - i = 6))

/-- A symmetric loopless C8 self-intertwiner whose alternating-line
same-sign degree is at most two has exactly one of three shapes: empty,
the antipodal matching, or the offset `±2` cycle. -/
theorem zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_two
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (k : ℕ) (hk : k ≤ 2)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hdiag : ∀ i, M i i = 0)
    (hsymm : ∀ i j, M i j = M j i)
    (hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1))
    (hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f i ∧ M i j = 1).card = k) :
    ZModEightSameSignShape M f k := by
  classical
  dsimp [ZModEightSameSignShape]
  have heven := zmodEight_alternating_sign_eq_iff_evenOffset f hsign hflip
  interval_cases k
  · left
    refine ⟨rfl, ?_⟩
    intro i j hsame hm
    have hjmem : j ∈ (Finset.univ : Finset (ZMod 8)).filter
        (fun z ↦ f z = f i ∧ M i z = 1) := by simp [hsame, hm]
    have hpos := Finset.card_pos.mpr ⟨j, hjmem⟩
    rw [hdegree i] at hpos
    omega
  · right; left
    refine ⟨rfl, ?_⟩
    have hdegree' : ∀ i,
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 1 := by
      intro i
      calc
        _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            f j = f i ∧ M i j = 1).card := by
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← heven i j]
        _ = 1 := hdegree i
    have hshape := zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
      M hdiag hsymm hinter hdegree'
    intro i j hsame
    exact hshape i j ((heven i j).mp hsame)
  · right; right
    refine ⟨rfl, ?_⟩
    have hdegree' : ∀ i,
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 2 := by
      intro i
      calc
        _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
            f j = f i ∧ M i j = 1).card := by
          congr 1
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← heven i j]
        _ = 2 := hdegree i
    have hshape := zmodEight_selfIntertwiner_sameParity_degreeTwo_offset_two_six
      M hdiag hsymm hinter hdegree'
    intro i j hsame
    exact hshape i j ((heven i j).mp hsame)

/-- Pulling a filtered graph row back through an injective coordinate map
preserves its cardinality. -/
theorem coordinate_sameSign_adj_card_eq_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (K : SimpleGraph X) [DecidableRel K.Adj]
    (A : Finset X) (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hurange : Set.range u = ↑A) (s : X → ℤ) (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j) = s (u i) ∧ K.Adj (u i) (u j)).card =
    (A.filter fun y ↦ K.Adj (u i) y ∧ s y = s (u i)).card := by
  classical
  apply Finset.card_bij (fun j _ ↦ u j)
  · intro j hj
    have hj' := Finset.mem_filter.mp hj
    rw [Finset.mem_filter]
    refine ⟨?_, hj'.2.2, hj'.2.1⟩
    change u j ∈ (↑A : Set X)
    rw [← hurange]
    exact ⟨j, rfl⟩
  · intro j₁ hj₁ j₂ hj₂ h
    exact huinj h
  · intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hxS : x ∈ (↑A : Set X) := hx'.1
    rw [← hurange] at hxS
    obtain ⟨j, rfl⟩ := hxS
    refine ⟨j, ?_, rfl⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hx'.2.2, hx'.2.1⟩

/-- Graph-facing wrapper for the signed C8 classifier. -/
theorem graph_zmodEight_sameSign_shape_of_comm
    {X : Type*} [Fintype X] [DecidableEq X]
    (H K : SimpleGraph X) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (s : X → ℤ) (k : ℕ) (hk : k ≤ 2)
    (hsign : ∀ i, s (u i) = -1 ∨ s (u i) = 1)
    (hflip : ∀ i, s (u (i + 1)) = -s (u i))
    (hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ)
    (hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j) = s (u i) ∧ K.Adj (u i) (u j)).card = k) :
    ZModEightSameSignShape
      (fun i j ↦ K.adjMatrix ℤ (u i) (u j)) (fun i ↦ s (u i)) k := by
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcomm hu hu hupair hupair
  have hdiag : ∀ i, M i i = 0 := by
    intro i
    simp [M, SimpleGraph.adjMatrix_apply]
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    by_cases hij : K.Adj (u i) (u j)
    · have hji : K.Adj (u j) (u i) := (K.adj_comm _ _).mp hij
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
    · have hji : ¬ K.Adj (u j) (u i) := by
        intro h
        exact hij ((K.adj_comm _ _).mp h)
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
  have hdegreeM : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j) = s (u i) ∧ M i j = 1).card = k := by
    intro i
    calc
      _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (u j) = s (u i) ∧ K.Adj (u i) (u j)).card := by
        congr 1
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp [M, SimpleGraph.adjMatrix_apply]
      _ = k := hdegree i
  exact zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_two
    M (fun i ↦ s (u i)) k hk hsign hflip hdiag hsymm hinter hdegreeM

set_option maxHeartbeats 1200000 in
/-- In normalized coordinates for the two ambient C8 components at
`mu=-3`, both diagonal defect blocks have the same one of the three signed
shapes controlled by a single `k ≤ 2`. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_diagonalSame_shapes
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    ∃ k : ℕ, k ≤ 2 ∧
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
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
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
      (fun x : c.supp ↦ s x.1) k hk (fun i ↦ hs_in _ (u i).2)
      (flip_of_coordinates u hu) hcomm hdegreeU
  · exact graph_zmodEight_sameSign_shape_of_comm Hc K v hvinj hv
      (fun x : c.supp ↦ s x.1) k hk (fun i ↦ hs_in _ (v i).2)
      (flip_of_coordinates v hv) hcomm hdegreeV

set_option maxHeartbeats 1200000 in
/-- Coordinate-free package: two distinct internal components in the
`mu=-3` size-two branch admit simultaneous C8 coordinates in which both
diagonal signed defect blocks have the same classified shape. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_exists_diagonalSame_shapes
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    let Hc := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    ∃ (u v : ZMod 8 → c.supp) (k : ℕ),
      Function.Injective u ∧ Function.Injective v ∧
      Set.range u = a.supp ∧ Set.range v = b.supp ∧
      (∀ z, Hc.neighborFinset (u z) = {u (z - 1), u (z + 1)}) ∧
      (∀ z, Hc.neighborFinset (v z) = {v (z - 1), v (z + 1)}) ∧
      k ≤ 2 ∧
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
    orderSixtyFour_sizeTwo_muNegThree_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hHdegree : ∀ z : c.supp, Hc.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  obtain ⟨u, v, huinj, hvinj, hurange, hvrange, hu, hv⟩ :=
    exists_zmodEight_twoComponent_coordinates Hc hHdegree a b ha8 hb8
  obtain ⟨k, hk, hshapeU, hshapeV⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_diagonalSame_shapes
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
      u v huinj hvinj hurange hvrange hu hv
  exact ⟨u, v, k, huinj, hvinj, hurange, hvrange, hu, hv,
    hk, hshapeU, hshapeV⟩

end

end Erdos85

#print axioms Erdos85.zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_two
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_diagonalSame_shapes
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_exists_diagonalSame_shapes

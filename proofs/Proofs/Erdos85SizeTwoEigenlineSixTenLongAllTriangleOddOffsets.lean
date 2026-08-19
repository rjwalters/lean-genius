import Proofs.Erdos85ZModTenOddSelfIntertwiner
import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTriangleAntipodal

/-!
# Odd antipodal offsets on the all-triangle C10 shore

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In cyclic coordinates on an all-triangle long shore of a `6+10`
size-two configuration, the two opposite-sign antipodal neighbors occur
exactly at offsets `{±3}`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_odd_antipodal_offsets
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
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) :
    ∀ i j, ¬ ZModTenEvenOffset (j - i) →
      ((antipodalGraph G).Adj (v i).1 (v j).1 ↔
        j - i = 3 ∨ j - i = 7) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let M : Matrix (ZMod 10) (ZMod 10) ℤ :=
    fun i j => K.adjMatrix ℤ (v i) (v j)
  have hvsign : ∀ j : ZMod 10, s (v (j + 1)).1 = -s (v j).1 := by
    intro j
    have hH : H.Adj (v j) (v (j + 1)) := by
      rw [← H.mem_neighborFinset, hv]
      simp
    have hmem : (v (j + 1)).1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c (v j).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (v (j + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v j).2).2 _ hmem
  have hsignParity : ∀ i j,
      s (v j).1 = s (v i).1 ↔ ZModTenEvenOffset (j - i) :=
    zmodTen_alternating_sign_eq_iff_evenOffset_sub
      (fun j => s (v j).1) hvsign (fun j => hs_in _ (v j).2)
  have hsignOdd : ∀ i j, ¬ ZModTenEvenOffset (j - i) ↔
      s (v j).1 = -s (v i).1 := by
    intro i j
    rw [← hsignParity]
    rcases hs_in _ (v i).2 with hi | hi <;>
      rcases hs_in _ (v j).2 with hj | hj <;> simp [hi, hj]
  obtain ⟨_hHdegree, _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcommKH : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  have hvpair : ∀ z : ZMod 10, v (z - 1) ≠ v (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := hvinj heq
    exact (by decide : (2 : ZMod 10) ≠ 0) (by
      calc
        (2 : ZMod 10) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    exact entry_cycleIntertwine_of_adjMatrix_comm K H v v
      (1 : ZMod 10) (1 : ZMod 10) hcommKH hv hv hvpair hvpair
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    simp [M, SimpleGraph.adjMatrix_apply, K.adj_comm]
  have hsuper : ∀ i, M i (i + 1) = 0 := by
    intro i
    have hi : v i ∈ b.supp := by rw [← hvrange]; exact ⟨i, rfl⟩
    have hanti : ¬ (antipodalGraph G).Adj (v i).1 (v (i + 1)).1 := by
      intro hanti
      have hG : G.Adj (v i).1 (v (i + 1)).1 := by
        have : H.Adj (v i) (v (i + 1)) := by
          rw [← H.mem_neighborFinset, hv]
          simp
        exact this
      have hmem :=
        (antipodalGraph_adj G (v i).1 (v (i + 1)).1).mp hanti
      exact ((mem_antipodalNeighbors G (v i).1 (v (i + 1)).1).mp hmem).2.1 hG
    have hK : ¬ K.Adj (v i) (v (i + 1)) := by
      intro hK
      have := (binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_defectAdj_iff_antipodal
        G c b hball (v i) (v (i + 1)) hi).mp hK
      exact hanti this
    simp [M, SimpleGraph.adjMatrix_apply, hK]
  have hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 10)).filter fun j =>
        ¬ ZModTenEvenOffset (j - i) ∧ M i j = 1).card = 2 := by
    intro i
    let S := (Finset.univ : Finset (ZMod 10)).filter fun j =>
      ¬ ZModTenEvenOffset (j - i) ∧ M i j = 1
    let T := (componentNeighborFinset K H b (v i)).filter fun z =>
      s z.1 = -s (v i).1
    have himage : S.image v = T := by
      ext z
      simp only [S, T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, componentNeighborFinset]
      constructor
      · rintro ⟨j, ⟨ho, hM⟩, rfl⟩
        have hK : K.Adj (v i) (v j) := by
          simpa [M, SimpleGraph.adjMatrix_apply] using hM
        refine ⟨⟨(K.mem_neighborFinset _ _).mpr hK, ?_⟩, (hsignOdd i j).1 ho⟩
        exact (ConnectedComponent.mem_supp_iff b (v j)).mp
          (by rw [← hvrange]; exact ⟨j, rfl⟩)
      · rintro ⟨⟨hzK, hzb⟩, hzsign⟩
        have hzb' : z ∈ b.supp :=
          (ConnectedComponent.mem_supp_iff b z).mpr hzb
        rw [← hvrange] at hzb'
        obtain ⟨j, rfl⟩ := hzb'
        refine ⟨j, ⟨(hsignOdd i j).2 hzsign, ?_⟩, rfl⟩
        have hK : K.Adj (v i) (v j) :=
          (K.mem_neighborFinset _ _).mp hzK
        simp [M, SimpleGraph.adjMatrix_apply, hK]
    have hScard : S.card = T.card := by
      calc
        S.card = (S.image v).card :=
          (Finset.card_image_of_injective _ hvinj).symm
        _ = T.card := congrArg Finset.card himage
    have hTcard : T.card = 2 := by
      simpa [T, K, H] using
        (binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
            (v i) (by rw [← hvrange]; exact ⟨i, rfl⟩)).2
    simpa [S, hTcard] using hScard
  have hoff := zmodTen_selfIntertwiner_odd_degreeTwo_offset_three_seven
    M hsymm hinter hsuper hdegree
  intro i j hodd
  have hKanti := binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_defectAdj_iff_antipodal
    G c b hball (v i) (v j) (by rw [← hvrange]; exact ⟨i, rfl⟩)
  rw [← hKanti]
  simpa [M, K, SimpleGraph.adjMatrix_apply] using hoff i j hodd

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_odd_antipodal_offsets

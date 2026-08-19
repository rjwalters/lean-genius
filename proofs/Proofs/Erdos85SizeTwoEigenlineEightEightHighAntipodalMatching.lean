import Proofs.Erdos85SizeTwoEigenlineEightEightHighSignSplit
import Proofs.Erdos85ZModEightSameParitySingleIntertwiner

/-!
# Antipodal diagonal matching in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The exact high-sector sign split supplies one same-parity diagonal defect
neighbour per row.  Commutation with the internal C8 and the degree-one C8
self-intertwiner classifier then force that neighbour to be the half-turn.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- Equality of an alternating sign on `ZMod 8` is exactly even coordinate
difference. -/
theorem zmodEight_alternating_sign_eq_iff_evenOffset
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i) :
    ∀ x y, f y = f x ↔ ZModEightEvenOffset (y - x) := by
  have h1 : f 1 = -f 0 := by simpa using hflip 0
  have h2 : f 2 = f 0 := by
    calc
      f 2 = -f 1 := by
        simpa only [show (1 : ZMod 8) + 1 = 2 by decide] using hflip 1
      _ = f 0 := by rw [h1]; ring
  have h3 : f 3 = -f 0 := by
    calc
      f 3 = -f 2 := by
        simpa only [show (2 : ZMod 8) + 1 = 3 by decide] using hflip 2
      _ = -f 0 := by rw [h2]
  have h4 : f 4 = f 0 := by
    calc
      f 4 = -f 3 := by
        simpa only [show (3 : ZMod 8) + 1 = 4 by decide] using hflip 3
      _ = f 0 := by rw [h3]; ring
  have h5 : f 5 = -f 0 := by
    calc
      f 5 = -f 4 := by
        simpa only [show (4 : ZMod 8) + 1 = 5 by decide] using hflip 4
      _ = -f 0 := by rw [h4]
  have h6 : f 6 = f 0 := by
    calc
      f 6 = -f 5 := by
        simpa only [show (5 : ZMod 8) + 1 = 6 by decide] using hflip 5
      _ = f 0 := by rw [h5]; ring
  have h7 : f 7 = -f 0 := by
    calc
      f 7 = -f 6 := by
        simpa only [show (6 : ZMod 8) + 1 = 7 by decide] using hflip 6
      _ = -f 0 := by rw [h6]
  have hne : f 0 ≠ -f 0 := by
    rcases hsign 0 with hneg | hpos <;> omega
  have hne' : -f 0 ≠ f 0 := Ne.symm hne
  intro x y
  have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨
      x = 6 ∨ x = 7 := by revert x; decide
  have hy : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨
      y = 6 ∨ y = 7 := by revert y; decide
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [ZModEightEvenOffset, h1, h2, h3, h4, h5, h6, h7, hne, hne'] <;>
      decide

/-- In the first cyclic C8 coordinate of a high `8+8` component at `r=6`,
diagonal defect adjacency is exactly the half-turn matching. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_defectAdj_iff_halfTurn
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6) :
    ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 4 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let M : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j => K.adjMatrix ℤ (u i) (u j)
  obtain ⟨_hHdegree, _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z =>
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcomm hu hu hupair hupair
  have hdiag : ∀ z, M z z = 0 := by
    intro z
    simp [M, SimpleGraph.adjMatrix_apply]
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    by_cases hij : K.Adj (u i) (u j)
    · have hji : K.Adj (u j) (u i) := (K.adj_comm _ _).mp hij
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
    · have hji : ¬K.Adj (u j) (u i) := by
        intro h
        exact hij ((K.adj_comm _ _).mp h)
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
  have huflip : ∀ i : ZMod 8, s (u (i + 1)).1 = -s (u i).1 := by
    intro i
    have hH : H.Adj (u i) (u (i + 1)) := by
      rw [← H.mem_neighborFinset, hu]
      simp
    have hmem : (u (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (u i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (u (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (u i).2).2 _ hmem
  have hsignEven := zmodEight_alternating_sign_eq_iff_evenOffset
    (fun i => s (u i).1) (fun i => hs_in _ (u i).2) huflip
  have hsplit :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_signSplit
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv hab6
  have hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 1 := by
    intro i
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j =>
      ZModEightEvenOffset (j - i) ∧ M i j = 1
    let A := (componentNeighborFinset K H a (u i)).filter
      fun z => s z.1 = s (u i).1
    have himage : T.image u = A := by
      ext z
      constructor
      · simp only [Finset.mem_image, T, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rintro ⟨j, ⟨heven, hm⟩, rfl⟩
        have hadj : K.Adj (u i) (u j) := by
          simpa [M, SimpleGraph.adjMatrix_apply] using hm
        have hmemA : u j ∈ a.supp := by
          rw [← hurange]
          exact ⟨j, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨(K.mem_neighborFinset _ _).mpr hadj, hmemA⟩,
            (hsignEven i j).mpr heven⟩
      · intro hz
        have hzA := (Finset.mem_filter.mp hz).1
        have hzSign := (Finset.mem_filter.mp hz).2
        have hza : z ∈ a.supp := (Finset.mem_filter.mp hzA).2
        rw [← hurange] at hza
        obtain ⟨j, rfl⟩ := hza
        have hadj := (K.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hzA).1
        refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          (hsignEven i j).mp hzSign,
          by simpa [M, SimpleGraph.adjMatrix_apply, hadj]⟩
    rw [← Finset.card_image_of_injective T huinj, himage]
    simpa [A, K, H] using (hsplit i).1
  have hoff := zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
    M hdiag hsymm hinter hdegree
  change ∀ i j, K.Adj (u i) (u j) ↔ j - i = 4
  intro i j
  have hsame_of_adj (hij : K.Adj (u i) (u j)) :
      s (u j).1 = s (u i).1 := by
    have hmem : u j ∈ componentNeighborFinset K H a (u i) := by
      rw [componentNeighborFinset, Finset.mem_filter]
      refine ⟨(K.mem_neighborFinset _ _).mpr hij, ?_⟩
      apply (ConnectedComponent.mem_supp_iff a (u j)).mp
      rw [← hurange]
      exact ⟨j, rfl⟩
    have hzero : ((componentNeighborFinset K H a (u i)).filter
        fun z => s z.1 = -s (u i).1).card = 0 := by
      simpa [K, H] using (hsplit i).2.1
    by_contra hne
    have hopp : s (u j).1 = -s (u i).1 := by
      rcases hs_in (u j).1 (u j).2 with hjNeg | hjPos <;>
        rcases hs_in (u i).1 (u i).2 with hiNeg | hiPos <;> simp_all
    have : u j ∈ (componentNeighborFinset K H a (u i)).filter
        fun z => s z.1 = -s (u i).1 := Finset.mem_filter.mpr ⟨hmem, hopp⟩
    have hpos := Finset.card_pos.mpr ⟨u j, this⟩
    rw [hzero] at hpos
    omega
  constructor
  · intro hij
    have heven := (hsignEven i j).mp (hsame_of_adj hij)
    exact (hoff i j heven).mp (by
      simp [M, SimpleGraph.adjMatrix_apply, hij])
  · intro hhalf
    have heven : ZModEightEvenOffset (j - i) := Or.inr (Or.inr (Or.inl hhalf))
    have hm : M i j = 1 := (hoff i j heven).mpr hhalf
    simpa [M, SimpleGraph.adjMatrix_apply] using hm

end

end Erdos85

#print axioms Erdos85.zmodEight_alternating_sign_eq_iff_evenOffset
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_defectAdj_iff_halfTurn

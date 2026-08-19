import Proofs.Erdos85ZModEightMixedSelfIntertwinerExclusion
import Proofs.Erdos85SizeTwoEigenlineEightEightLowAntipodalTrace
import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalMatching

open Finset SimpleGraph

/-!
# Diagonal kernels for the low `8+8` quotient parameters

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

For an all-triangle-free C8 shore, the two cycle edges are the two
opposite-sign defect edges.  The remaining diagonal defect entries therefore
have even offset.  At quotient parameters three and two their row degrees
are respectively two and three.  Degree two was classified previously as
offsets `±2`; this file supplies the degree-three endpoint: every nonzero
even offset occurs.
-/

namespace Erdos85

/-- A loopless binary matrix on `ZMod 8` with three even-offset entries in
each row contains precisely the three nonzero even offsets `2,4,6`.

No intertwining hypothesis is needed at this maximal even-offset degree;
there are only three available nonzero even differences. -/
theorem zmodEight_sameParity_degreeThree_offset_two_four_six
    (H : Matrix (ZMod 8) (ZMod 8) ℤ)
    (hdiag : ∀ z, H z z = 0)
    (hdegree : ∀ x,
      ((Finset.univ : Finset (ZMod 8)).filter fun y =>
        ZModEightEvenOffset (y - x) ∧ H x y = 1).card = 3) :
    ∀ x y, ZModEightEvenOffset (y - x) →
      (H x y = 1 ↔ y - x = 2 ∨ y - x = 4 ∨ y - x = 6) := by
  classical
  intro x y heven
  let S := (Finset.univ : Finset (ZMod 8)).filter fun z =>
    ZModEightEvenOffset (z - x) ∧ H x z = 1
  let T : Finset (ZMod 8) := {x + 2, x + 4, x + 6}
  have hSsub : S ⊆ T := by
    intro z hz
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz'.1 with h0 | h2 | h4 | h6
    · have hzEq : z = x := by linear_combination h0
      subst z
      rw [hdiag] at hz'
      omega
    · have hzEq : z = x + 2 := by linear_combination h2
      simp [T, hzEq]
    · have hzEq : z = x + 4 := by linear_combination h4
      simp [T, hzEq]
    · have hzEq : z = x + 6 := by linear_combination h6
      simp [T, hzEq]
  have hScard : S.card = 3 := by simpa [S] using hdegree x
  have hTcard : T.card = 3 := by
    dsimp only [T]
    have h24 : x + (2 : ZMod 8) ≠ x + 4 := by
      intro h
      have : (2 : ZMod 8) = 4 := add_left_cancel h
      contradiction
    have h26 : x + (2 : ZMod 8) ≠ x + 6 := by
      intro h
      have : (2 : ZMod 8) = 6 := add_left_cancel h
      contradiction
    have h46 : x + (4 : ZMod 8) ≠ x + 6 := by
      intro h
      have : (4 : ZMod 8) = 6 := add_left_cancel h
      contradiction
    simp [h24, h26, h46]
  have hST : S = T := Finset.eq_of_subset_of_card_le hSsub (by omega)
  have hyMem : y ∈ S ↔ H x y = 1 := by simp [S, heven]
  rw [← hyMem, hST]
  simp only [T, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rcases h with h | h | h
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h
  · intro h
    rcases h with h | h | h
    · left; linear_combination h
    · right; left; linear_combination h
    · right; right; linear_combination h

/-- On an all-triangle-free C8 shore, the same-parity part of a diagonal
defect row has cardinality `d - 2`, where `d` is the diagonal quotient.
The two deleted entries are exactly the ambient cycle neighbors. -/
theorem binarySquare_regular_sizeTwoPart_eight_allTriangleFree_diagonal_sameParity_card
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
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp)
    (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (d : ℕ) (hdiagQ : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = d) :
    ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ (u i) (u j) = 1).card =
        d - 2 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
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
  intro i
  let B := componentNeighborFinset K H a (u i)
  let N := H.neighborFinset (u i)
  let A := B.filter fun z => s z.1 = s (u i).1
  have huiA : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hBcard : B.card = d := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal a a huiA]
    simpa [K, H] using hdiagQ
  have hNcard : N.card = 2 := by
    simpa [N] using H.card_neighborFinset_eq_degree (u i) |>.trans (hHdegree (u i))
  have hNsubB : N ⊆ B := by
    intro z hz
    have hiz : H.Adj (u i) z := (H.mem_neighborFinset _ _).mp hz
    have hzA : z ∈ a.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hiz).symm.trans
        ((ConnectedComponent.mem_supp_iff a (u i)).mp huiA)
    have htfEdge : (triangleFreeEdgeGraph G).Adj (u i).1 z.1 :=
      sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree (u i) z hiz
        (htf (u i) huiA)
    change z ∈ componentNeighborFinset K H a (u i)
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(K.mem_neighborFinset _ _).mpr (Or.inr htfEdge),
      (ConnectedComponent.mem_supp_iff a z).mp hzA⟩
  have hAeq : A = B \ N := by
    ext z
    constructor
    · intro hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzsign := (Finset.mem_filter.mp hz).2
      refine Finset.mem_sdiff.mpr ⟨hzB, ?_⟩
      intro hzN
      have hiz : H.Adj (u i) z := (H.mem_neighborFinset _ _).mp hzN
      have hmem : z.1 ∈ componentNeighborFinset G
          (secondOrderDefectGraph G) c (u i).1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hiz, z.2⟩
      have hopp := (internal_alternation G hfree (by omega) hreg hcard c hc s
        hs_in hs_out hA_in (u i).2).2 _ hmem
      rcases hs_in (u i).1 (u i).2 with hiNeg | hiPos <;> omega
    · intro hz
      have hzB := (Finset.mem_sdiff.mp hz).1
      have hzNotN := (Finset.mem_sdiff.mp hz).2
      have hzK := (Finset.mem_filter.mp hzB).1
      have hzsign :=
        binarySquare_regular_sizeTwoPart_allTriangleFree_nonambient_defect_preserves_sign
          G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in hDs a htf
            (u i) z huiA ((K.mem_neighborFinset _ _).mp hzK)
            (by simpa [N, H] using hzNotN)
      exact Finset.mem_filter.mpr ⟨hzB, hzsign⟩
  have hAcard : A.card = d - 2 := by
    rw [hAeq, Finset.card_sdiff, Finset.inter_eq_left.mpr hNsubB,
      hBcard, hNcard]
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j =>
    ZModEightEvenOffset (j - i) ∧ K.adjMatrix ℤ (u i) (u j) = 1
  have himage : T.image u = A := by
    ext z
    constructor
    · simp only [Finset.mem_image, T, Finset.mem_filter, Finset.mem_univ,
        true_and]
      rintro ⟨j, ⟨heven, hm⟩, rfl⟩
      have hadj : K.Adj (u i) (u j) := by
        simpa [SimpleGraph.adjMatrix_apply] using hm
      have hujA : u j ∈ a.supp := by
        rw [← hurange]
        exact ⟨j, rfl⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr
          ⟨(K.mem_neighborFinset _ _).mpr hadj,
            (ConnectedComponent.mem_supp_iff a (u j)).mp hujA⟩,
          (hsignEven i j).mpr heven⟩
    · intro hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzSign := (Finset.mem_filter.mp hz).2
      have hza : z ∈ a.supp :=
        (ConnectedComponent.mem_supp_iff a z).mpr (Finset.mem_filter.mp hzB).2
      rw [← hurange] at hza
      obtain ⟨j, rfl⟩ := hza
      have hadj := (K.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hzB).1
      refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
        (hsignEven i j).mp hzSign,
        by simpa [SimpleGraph.adjMatrix_apply, hadj]⟩
  change T.card = d - 2
  rw [← Finset.card_image_of_injective T huinj, himage]
  exact hAcard

end Erdos85

#print axioms Erdos85.zmodEight_sameParity_degreeThree_offset_two_four_six
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_allTriangleFree_diagonal_sameParity_card

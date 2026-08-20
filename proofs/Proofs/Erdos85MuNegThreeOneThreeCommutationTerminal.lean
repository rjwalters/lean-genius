import Proofs.Erdos85MuNegThreeOneThreeShoreGeometry
import Proofs.Erdos85SizeTwoMuNegThreeSelfCellZeroFour
import Proofs.Erdos85SizeTwoMuNegThreeSelfCellZeroFourRouter

/-! # Algebraic commutation kill for the `mu=-3`, `(k,r)=(1,3)` endpoint -/

open Finset Matrix

namespace Erdos85

noncomputable section

def zmodEightAntipodeMatrix : Matrix (ZMod 8) (ZMod 8) ℤ :=
  fun i j ↦ if j - i = 4 then 1 else 0

theorem zmodEightAntipodeMatrix_symm (i j : ZMod 8) :
    zmodEightAntipodeMatrix i j = zmodEightAntipodeMatrix j i := by
  revert i j
  decide

theorem zmodEightAntipodeMatrix_entry_intertwine (i j : ZMod 8) :
    zmodEightAntipodeMatrix (i - 1) j +
      zmodEightAntipodeMatrix (i + 1) j =
    zmodEightAntipodeMatrix i (j + 1) +
      zmodEightAntipodeMatrix i (j - 1) := by
  revert i j
  decide

theorem zmodEightAntipodeMatrix_row_sum (i : ZMod 8) :
    ∑ j, zmodEightAntipodeMatrix i j = 1 := by
  revert i
  decide

/-- Removing the forced antipodal matching from h313 leaves precisely the
impossible opposite-sign row-three cycle intertwiner. -/
theorem MuNegThreeExplicitParameterLedger.oneThree_false_of_intertwine
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ} {f g : ZMod 8 → ℤ}
    (L : MuNegThreeExplicitParameterLedger N M f g 1 3)
    (hshape : ZModEightSameSignShape N f 1)
    (hcycle : ∀ i, N i (i - 1) = 1 ∧ N i (i + 1) = 1)
    (hsymm : ∀ i j, N i j = N j i)
    (hinter : ∀ i j,
      N (i - 1) j + N (i + 1) j = N i (j + 1) + N i (j - 1))
    (hbinary : ∀ i j, N i j = 0 ∨ N i j = 1) : False := by
  classical
  let A := zmodEightAntipodeMatrix
  let P := N - A
  have honeShape : ∀ i j, f j = f i → (N i j = 1 ↔ j - i = 4) := by
    rcases hshape with hzero | hone | htwo
    · omega
    · exact hone.2
    · omega
  have hAone : ∀ i j, j - i = 4 → N i j = 1 := by
    intro i j hoff
    have heven : ZModEightEvenOffset (j - i) := by rw [hoff]; decide
    have hsame := (zmodEight_alternating_sign_eq_iff_evenOffset
      f L.f_sign L.f_flip i j).mpr heven
    exact (honeShape i j hsame).mpr hoff
  have hPinter : ∀ i j,
      P (i - 1) j + P (i + 1) j = P i (j + 1) + P i (j - 1) := by
    intro i j
    have hN := hinter i j
    have hA := zmodEightAntipodeMatrix_entry_intertwine i j
    dsimp only [P, A]
    simp only [Matrix.sub_apply]
    linear_combination hN - hA
  have hPsymm : ∀ i j, P i j = P j i := by
    intro i j
    dsimp only [P, A]
    simp only [Matrix.sub_apply, hsymm, zmodEightAntipodeMatrix_symm]
  have hPbinary : ∀ i j, P i j = 0 ∨ P i j = 1 := by
    intro i j
    by_cases hoff : j - i = 4
    · left
      simp [P, A, zmodEightAntipodeMatrix, hoff, hAone i j hoff]
    · have hAz : A i j = 0 := by simp [A, zmodEightAntipodeMatrix, hoff]
      rcases hbinary i j with hz | ho
      · left; simp [P, Matrix.sub_apply, hz, hAz]
      · right; simp [P, Matrix.sub_apply, ho, hAz]
  have hNrow : ∀ i, ∑ j, N i j = 4 := by
    intro i
    have hsum : ∑ j, N i j =
        (((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N i j = 1).card : ℤ) := by
      calc
        ∑ j, N i j = ∑ j, if N i j = 1 then (1 : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          rcases hbinary i j with hz | ho
          · simp [hz]
          · simp [ho]
        _ = _ := by simpa using
          (Finset.sum_boole (R := ℤ) (fun j : ZMod 8 ↦ N i j = 1) Finset.univ)
    rw [hsum, L.internal_row]
    norm_num
  have hProw : ∀ i, ∑ j, P i j = 3 := by
    intro i
    calc
      ∑ j, P i j = (∑ j, N i j) - ∑ j, A i j := by
        simp [P, Matrix.sub_apply, Finset.sum_sub_distrib]
      _ = 4 - 1 := by rw [hNrow, zmodEightAntipodeMatrix_row_sum]
      _ = 3 := by norm_num
  have hPeven0 : ∀ i j, ZModEightEvenOffset (j - i) → P i j = 0 := by
    intro i j heven
    have hsame := (zmodEight_alternating_sign_eq_iff_evenOffset
      f L.f_sign L.f_flip i j).mpr heven
    by_cases hoff : j - i = 4
    · simp [P, A, zmodEightAntipodeMatrix, hoff, hAone i j hoff]
    · have hNne : N i j ≠ 1 := fun h ↦ hoff ((honeShape i j hsame).mp h)
      have hNz : N i j = 0 := (hbinary i j).resolve_right hNne
      simp [P, A, zmodEightAntipodeMatrix, hoff, hNz]
  have hPcycle : ∀ i, P i (i - 1) = 1 ∧ P i (i + 1) = 1 := by
    intro i
    rcases hcycle i with ⟨hm, hp⟩
    constructor
    · have hoff : (i - 1) - i ≠ (4 : ZMod 8) := by
        intro h
        have : ¬ ((-1 : ZMod 8) = 4) := by decide
        apply this
        linear_combination h
      have hA0 : A i (i - 1) = 0 := by
        simp only [A, zmodEightAntipodeMatrix, hoff, if_false]
      change N i (i - 1) - A i (i - 1) = 1
      rw [hm, hA0]
      norm_num
    · have hoff : (i + 1) - i ≠ (4 : ZMod 8) := by
        intro h
        have : ¬ ((1 : ZMod 8) = 4) := by decide
        apply this
        linear_combination h
      have hA0 : A i (i + 1) = 0 := by
        simp only [A, zmodEightAntipodeMatrix, hoff, if_false]
      change N i (i + 1) - A i (i + 1) = 1
      rw [hp, hA0]
      norm_num
  exact zmodEight_selfIntertwiner_oppositeOnly_rowThree_with_cycle_impossible
    P hPsymm hPinter hPbinary hProw hPeven0 hPcycle

open SimpleGraph

/-- Graph-facing h313 terminal from the exact first-shore row ledger. -/
theorem muNegThreeOneThree_graph_false_of_rowLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (L : MuNegThreeExplicitParameterLedger
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (u j)) M f g 1 3)
    (hone : C8CycleEntriesOne
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (u j))) : False := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let N : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  change MuNegThreeExplicitParameterLedger N M f g 1 3 at L
  change C8CycleEntriesOne N at hone
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ :=
    (adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c).symm
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z ↦
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      N (i - 1) j + N (i + 1) j = N i (j + 1) + N i (j - 1) := by
    simpa only [N] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcomm hu hu hupair hupair
  have hsymm : ∀ i j, N i j = N j i := by
    intro i j
    simp [N, SimpleGraph.adjMatrix_apply, K.adj_comm]
  have hbinary : ∀ i j, N i j = 0 ∨ N i j = 1 := by
    intro i j
    by_cases h : K.Adj (u i) (u j)
    · right; simp [N, SimpleGraph.adjMatrix_apply, h]
    · left; simp [N, SimpleGraph.adjMatrix_apply, h]
  have hdiag : ∀ i, N i i = 0 := by
    intro i
    simp [N, SimpleGraph.adjMatrix_apply]
  have hshape : ZModEightSameSignShape N f 1 :=
    zmodEight_selfIntertwiner_sameSign_shape_of_degree_le_two
      N f 1 (by omega) L.f_sign L.f_flip hdiag hsymm hinter L.internal_same
  have htf2 :=
    binarySquare_regular_sizeTwoPart_eight_cycleEntriesOne_forces_allTriangleFree
      G hfree hreg hcard c hc a u hurange hu (by simpa [N, K] using hone)
  have hcycAdj : ∀ i, K.Adj (u i) (u (i + 1)) := by
    intro i
    let T := (Finset.univ : Finset c.supp).filter fun y ↦
      (triangleFreeEdgeGraph G).Adj (u i).1 y.1
    have himage : Finset.image Subtype.val T =
        (triangleFreeEdgeGraph G).neighborFinset (u i).1 := by
      ext y
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro htf
        have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u i).1 y := by
          rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
          exact htf
        have hyc : y ∈ c.supp := by
          rw [ConnectedComponent.mem_supp_iff c y]
          exact (ConnectedComponent.connectedComponentMk_eq_of_adj
            hpair.2).symm.trans
              ((ConnectedComponent.mem_supp_iff c (u i).1).mp (u i).2)
        exact ⟨⟨y, hyc⟩, htf, rfl⟩
    have hTcard : T.card = 2 := by
      rw [← Finset.card_image_of_injective T Subtype.val_injective,
        himage, (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact htf2 (u i) ((ConnectedComponent.mem_supp_iff a (u i)).mp (by
        rw [← hurange]; exact ⟨i, rfl⟩))
    have hTsub : T ⊆ H.neighborFinset (u i) := by
      intro y hy
      have htf := (Finset.mem_filter.mp hy).2
      have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u i).1 y.1 := by
        rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact htf
      exact (H.mem_neighborFinset (u i) y).mpr hpair.1
    have hHdegree : H.degree (u i) = 2 := by
      exact binarySquare_regular_degree_induce_defectComponent_eq_part
        G hfree (by omega) hreg hcard c (m := 2) hc (u i)
    have hTeq : T = H.neighborFinset (u i) := by
      apply Finset.eq_of_subset_of_card_le hTsub
      rw [hTcard, H.card_neighborFinset_eq_degree, hHdegree]
    have hHi : H.Adj (u i) (u (i + 1)) := by
      rw [← H.mem_neighborFinset, hu]
      simp
    have huiT : u (i + 1) ∈ T := by
      rw [hTeq]
      exact (H.mem_neighborFinset _ _).mpr hHi
    have htf := (Finset.mem_filter.mp huiT).2
    have hpair : (G ⊓ secondOrderDefectGraph G).Adj
        (u i).1 (u (i + 1)).1 := by
      rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
      exact htf
    exact hpair.2
  have hcycle : ∀ i, N i (i - 1) = 1 ∧ N i (i + 1) = 1 := by
    intro i
    constructor
    · have h := hcycAdj (i - 1)
      rw [show i - 1 + 1 = i by ring] at h
      have h' := (K.adj_comm _ _).mp h
      simp [N, SimpleGraph.adjMatrix_apply, h']
    · simp [N, SimpleGraph.adjMatrix_apply, hcycAdj i]
  exact L.oneThree_false_of_intertwine hshape hcycle hsymm hinter hbinary

end

end Erdos85

#print axioms Erdos85.MuNegThreeExplicitParameterLedger.oneThree_false_of_intertwine
#print axioms Erdos85.muNegThreeOneThree_graph_false_of_rowLedger

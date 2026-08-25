import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry
import Proofs.Erdos85MuNegThreeZeroFiveCorrectCrossProfile
import Proofs.Erdos85MuNegThreeZeroFiveCorrectGraphTerminal
import Proofs.Erdos85MuNegThreeZeroFiveOwnerProfile
import Proofs.Erdos85MuNegThreeExplicitParameters
import Proofs.Erdos85MuNegOneOneFourGraphC4Intertwine
import Proofs.Erdos85NegativeOrbitAssembly
import Proofs.Erdos85SizeTwoMuNegThreeEightEightSectorParameterGrid
import Proofs.Erdos85SizeTwoMuNegOneCycleDefectSectorUniformity

/-! # Correct ledger-to-shore geometry for the `mu = -3`, `(k,r) = (0,5)` endpoint -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

/-
private theorem h305_crossExteriorSplit_of_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (su sv : ZMod 8 → ℤ)
    (hprofile : MuNegFiveCrossExteriorProfile
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (v j)) su sv 3 2) :
    MuNegThreeZeroFiveCrossExteriorSplit
      (exteriorPairGraph G c.supp) u v su sv := by
  classical
  let K := (secondOrderDefectGraph G).induce c.supp
  have hcomp := sizeTwo_distinctCycle_cross_exteriorPair_iff_not_defect
    G hfree c a b hab u v hurange hvrange
  refine ⟨?_, ?_⟩
  · intro i
    let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (exteriorPairGraph G c.supp).Adj (u i) (v j)
    have htotal : S.card = 3 := by
      simpa [S, K, SimpleGraph.adjMatrix_apply, hcomp i] using
        hprofile.row_total i
    have hsame : (S.filter fun j ↦ sv j = su i).card = 2 := by
      change (((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j)).filter
          fun j ↦ sv j = su i).card = 2
      rw [Finset.filter_filter]
      simpa [K, SimpleGraph.adjMatrix_apply, hcomp i, and_comm] using
        hprofile.row_same i
    have hsplit := S.card_filter_add_card_filter_not (fun j ↦ sv j = su i)
    constructor
    · simpa [S, Finset.filter_filter, and_comm] using hsame
    · have hsum : (S.filter fun j ↦ sv j = su i).card +
          (S.filter fun j ↦ sv j ≠ su i).card = S.card := by
        simpa using hsplit
      have : (S.filter fun j ↦ sv j ≠ su i).card = 1 := by omega
      simpa [S, Finset.filter_filter, and_comm] using this
  · intro j
    let S := (Finset.univ : Finset (ZMod 8)).filter fun i ↦
      (exteriorPairGraph G c.supp).Adj (u i) (v j)
    have htotal : S.card = 3 := by
      simpa [S, K, SimpleGraph.adjMatrix_apply, hcomp] using
        hprofile.col_total j
    have hsame : (S.filter fun i ↦ su i = sv j).card = 2 := by
      change (((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        (exteriorPairGraph G c.supp).Adj (u i) (v j)).filter
          fun i ↦ su i = sv j).card = 2
      rw [Finset.filter_filter]
      simpa [K, SimpleGraph.adjMatrix_apply, hcomp, and_comm] using
        hprofile.col_same j
    have hsplit := S.card_filter_add_card_filter_not (fun i ↦ su i = sv j)
    constructor
    · simpa [S, Finset.filter_filter, and_comm] using hsame
    · have hsum : (S.filter fun i ↦ su i = sv j).card +
          (S.filter fun i ↦ su i ≠ sv j).card = S.card := by
        simpa using hsplit
      have : (S.filter fun i ↦ su i ≠ sv j).card = 1 := by omega
      simpa [S, Finset.filter_filter, and_comm] using this
-/

theorem h305_ledger_correct_shore_modes
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
    (M : Matrix (ZMod 8) (ZMod 8) ℤ) (f g : ZMod 8 → ℤ)
    (L : MuNegThreeExplicitParameterLedger
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (u j)) M f g 0 5) :
    (C8CycleEntriesZero
        (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
          (u i) (u j)) →
      MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u) ∧
    (C8CycleEntriesOne
        (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
          (u i) (u j)) →
      MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u) := by
  classical
  let K := (secondOrderDefectGraph G).induce c.supp
  let N : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  have hsector := binarySquare_regular_sizeTwoPart_eight_cycleDefect_allZero_or_allOne
    G hfree hreg hcard c hc a u hurange hu
  have hsame : ∀ i j, f j = f i → ¬ K.Adj (u i) (u j) := by
    intro i j hs hK
    change (secondOrderDefectGraph G).Adj (u i).1 (u j).1 at hK
    have hj : j ∈ (Finset.univ : Finset (ZMod 8)).filter fun z ↦
        f z = f i ∧ N i z = 1 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs, by
        simp [N, K, SimpleGraph.adjMatrix_apply, hK]⟩
    have hp := Finset.card_pos.mpr ⟨j, hj⟩
    have hz : ((Finset.univ : Finset (ZMod 8)).filter fun z ↦
        f z = f i ∧ N i z = 1).card = 0 := by
      simpa [N, K] using L.internal_same i
    rw [hz] at hp
    omega
  have hrowCard : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        K.Adj (u i) (u j)).card = 2 := by
    intro i
    simpa [N, K, SimpleGraph.adjMatrix_apply] using L.internal_row i
  have hdiffSame : ∀ i j, (j - i = 0 ∨ j - i = 2 ∨
      j - i = 4 ∨ j - i = 6) → f j = f i := by
    intro i j heven
    exact (zmodEight_alternating_sign_eq_iff_evenOffset
      f L.f_sign L.f_flip i j).mpr heven
  have exactOne (hall : ∀ i, K.Adj (u i) (u (i - 1)) ∧
      K.Adj (u i) (u (i + 1))) :
      ∀ i j, K.Adj (u i) (u j) ↔ j - i = 1 ∨ j - i = 7 := by
    intro i j
    let D := (Finset.univ : Finset (ZMod 8)).filter fun z ↦ K.Adj (u i) (u z)
    have hsub : ({i - 1, i + 1} : Finset (ZMod 8)) ⊆ D := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hall i).1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hall i).2⟩
    have hDcard : D.card = 2 := hrowCard i
    have hpaircard : ({i - 1, i + 1} : Finset (ZMod 8)).card = 2 := by
      simp [zmodEight_pred_ne_succ]
    have heq : ({i - 1, i + 1} : Finset (ZMod 8)) = D := by
      apply Finset.eq_of_subset_of_card_le hsub
      omega
    have hmem : K.Adj (u i) (u j) ↔ j ∈ D := by simp [D]
    rw [hmem, ← heq]
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · right
        calc
          i - 1 - i = -1 := by ring
          _ = 7 := by decide
      · left; ring
    · intro h
      rcases h with h | h
      · right
        have hj : j = i + 1 := by
          calc
            j = 1 + i := sub_eq_iff_eq_add.mp h
            _ = i + 1 := by ring
        exact hj
      · left
        have hm : j - i = -1 := h.trans (by decide)
        calc
          j = -1 + i := sub_eq_iff_eq_add.mp hm
          _ = i - 1 := by ring
  have exactZero (hall : ∀ i, ¬ K.Adj (u i) (u (i - 1)) ∧
      ¬ K.Adj (u i) (u (i + 1))) :
      ∀ i j, K.Adj (u i) (u j) ↔ j - i = 3 ∨ j - i = 5 := by
    intro i j
    let D := (Finset.univ : Finset (ZMod 8)).filter fun z ↦ K.Adj (u i) (u z)
    have hDsub : D ⊆ ({i + 3, i + 5} : Finset (ZMod 8)) := by
      intro z hz
      have hK := (Finset.mem_filter.mp hz).2
      have hnotEven : ¬ (z - i = 0 ∨ z - i = 2 ∨
          z - i = 4 ∨ z - i = 6) := fun he ↦ hsame i z (hdiffSame i z he) hK
      have hnotOne : z - i ≠ 1 := by
        intro h
        have hz : z = i + 1 := by
          calc
            z = 1 + i := sub_eq_iff_eq_add.mp h
            _ = i + 1 := by ring
        exact (hall i).2 (by simpa [hz] using hK)
      have hnotSeven : z - i ≠ 7 := by
        intro h
        have hm : z - i = -1 := h.trans (by decide)
        have hz : z = i - 1 := by
          calc
            z = -1 + i := sub_eq_iff_eq_add.mp hm
            _ = i - 1 := by ring
        exact (hall i).1 (by simpa [hz] using hK)
      have : z - i = 3 ∨ z - i = 5 := by
        generalize z - i = d at hnotEven hnotOne hnotSeven ⊢
        revert d
        decide
      rcases this with h | h
      · have hz : z = i + 3 := by
          calc
            z = 3 + i := sub_eq_iff_eq_add.mp h
            _ = i + 3 := by ring
        simp [hz]
      · have hz : z = i + 5 := by
          calc
            z = 5 + i := sub_eq_iff_eq_add.mp h
            _ = i + 5 := by ring
        simp [hz]
    have hDcard : D.card = 2 := hrowCard i
    have hpaircard : ({i + 3, i + 5} : Finset (ZMod 8)).card = 2 := by
      have hne : i + 3 ≠ i + 5 := by
        rw [add_comm i 3, add_comm i 5]
        exact fun h ↦ (by decide : (3 : ZMod 8) ≠ 5) (add_right_cancel h)
      simp [hne]
    have heq : D = ({i + 3, i + 5} : Finset (ZMod 8)) := by
      apply Finset.eq_of_subset_of_card_le hDsub
      omega
    have hmem : K.Adj (u i) (u j) ↔ j ∈ D := by simp [D]
    rw [hmem, heq]
    simp only [D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl)
      · left; ring
      · right; ring
    · intro h
      rcases h with h | h
      · left
        calc
          j = 3 + i := sub_eq_iff_eq_add.mp h
          _ = i + 3 := by ring
      · right
        calc
          j = 5 + i := sub_eq_iff_eq_add.mp h
          _ = i + 5 := by ring
  have exteriorOfOne (hD : ∀ i j, K.Adj (u i) (u j) ↔
      j - i = 1 ∨ j - i = 7) :
      MuNegThreeZeroFiveTfShoreMode (exteriorPairGraph G c.supp) u := by
    intro i j
    by_cases hij : i = j
    · subst j; simp <;> decide
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
    have hcommon : (∃ z : c.supp,
        G.Adj (u i).1 z.1 ∧ G.Adj (u j).1 z.1) ↔
        j - i = 2 ∨ j - i = 6 := by
      simpa using zmodEight_cycle_internalCommon_iff_offset_two_six
        (G.induce c.supp) u huinj hu i j hij
    rw [show (secondOrderDefectGraph G).Adj (u i).1 (u j).1 ↔
        j - i = 1 ∨ j - i = 7 by simpa [K] using hD i j, hcommon]
    have hne : u i ≠ u j := fun h ↦ hij (huinj h)
    rw [and_iff_right hne]
    have hd0 : j - i ≠ 0 := fun h ↦ hij (sub_eq_zero.mp h).symm
    generalize j - i = d at hd0 ⊢
    revert d
    decide
  have exteriorOfZero (hD : ∀ i j, K.Adj (u i) (u j) ↔
      j - i = 3 ∨ j - i = 5) :
      MuNegThreeZeroFiveTriangleShoreMode (exteriorPairGraph G c.supp) u := by
    intro i j
    by_cases hij : i = j
    · subst j; simp <;> decide
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
    have hcommon : (∃ z : c.supp,
        G.Adj (u i).1 z.1 ∧ G.Adj (u j).1 z.1) ↔
        j - i = 2 ∨ j - i = 6 := by
      simpa using zmodEight_cycle_internalCommon_iff_offset_two_six
        (G.induce c.supp) u huinj hu i j hij
    rw [show (secondOrderDefectGraph G).Adj (u i).1 (u j).1 ↔
        j - i = 3 ∨ j - i = 5 by simpa [K] using hD i j, hcommon]
    have hne : u i ≠ u j := fun h ↦ hij (huinj h)
    rw [and_iff_right hne]
    have hd0 : j - i ≠ 0 := fun h ↦ hij (sub_eq_zero.mp h).symm
    generalize j - i = d at hd0 ⊢
    revert d
    decide
  constructor
  · intro hzero
    rcases hsector with hall0 | hall1
    · exact exteriorOfZero (exactZero hall0)
    · exfalso
      exact hzero.2 (by simpa [N, K, SimpleGraph.adjMatrix_apply] using (hall1 0).2)
  · intro hone
    rcases hsector with hall0 | hall1
    · exfalso
      exact (hall0 0).2 (by simpa [N, K, SimpleGraph.adjMatrix_apply] using hone.2)
    · exact exteriorOfOne (exactOne hall1)

/-- The remaining `(-3,0,5)` direct-or-transported endpoint is impossible.
The exact orbit ledger supplies the uniform cross profile; the two cycle
entry bits select the corresponding graph shore modes. -/
theorem false_of_h305_source_or_transported
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
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    Nonempty (NegativeEightEightSourceWitness G c a b N₁ N₂ (-3) 0 5) ∨
      NegativeEightEightTransportedWitness G c a N₁ N₂ (-3) 0 5 → False := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let M₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  let M₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (u j)
  intro h
  obtain ⟨s, _hs, hcell, L₁, L₂⟩ :=
    exists_muNegThree_exact_data_of_source_or_transported
      G hfree hreg hcard c hc a b hab u v huinj hvinj hurange hvrange
        hu hv 0 5 (by omega) h
  have htranspose : ∀ i j, M₂ j i = M₁ i j := by
    intro i j
    simp only [M₁, M₂, K, SimpleGraph.adjMatrix_apply]
    simp [SimpleGraph.adj_comm]
  have hprofile := muNegThree_zeroFive_ownerProfile
    hcell L₁ L₂ htranspose
  have hcross := h305_crossExteriorSplit_of_profile
    G hfree c a b hab u v hurange hvrange
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) hprofile.2
  have humode := h305_ledger_correct_shore_modes G hfree hreg hcard c hc a u huinj
    hurange hu M₁ (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) L₁
  have hvmode := h305_ledger_correct_shore_modes G hfree hreg hcard c hc b v hvinj
    hvrange hv M₂ (fun j ↦ s (v j).1) (fun i ↦ s (u i).1) L₂
  rcases hprofile.1 with hzero | hmixed | hone
  · exact muNegThreeZeroFiveCorrect_graph_false_of_exterior
      G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange hu hv
        (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
        L₁.f_sign L₂.f_sign L₁.f_flip L₂.f_flip hcross true true
        (Or.inr (Or.inr ⟨rfl, rfl⟩)) (humode.1 hzero.1) (hvmode.1 hzero.2)
  · rcases hmixed with huv | hvu
    · have htranspose' : ∀ i j, M₁ j i = M₂ i j := by
        intro i j
        exact (htranspose j i).symm
      have hprofile' := muNegThree_zeroFive_crossExteriorProfile
        L₂ L₁ htranspose'
      have hcross' := h305_crossExteriorSplit_of_profile
        G hfree c b a (Ne.symm hab) v u hvrange hurange
          (fun j ↦ s (v j).1) (fun i ↦ s (u i).1) hprofile'
      exact muNegThreeZeroFiveCorrect_graph_false_of_exterior
        G c hfree hreg hcard hc b a (Ne.symm hab) v u hvinj huinj
          hvrange hurange hv hu (fun j ↦ s (v j).1) (fun i ↦ s (u i).1)
          L₂.f_sign L₁.f_sign L₂.f_flip L₁.f_flip hcross' false true
          (Or.inr (Or.inl ⟨rfl, rfl⟩)) (hvmode.2 huv.2) (humode.1 huv.1)
    · exact muNegThreeZeroFiveCorrect_graph_false_of_exterior
        G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange hu hv
          (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
          L₁.f_sign L₂.f_sign L₁.f_flip L₂.f_flip hcross false true
          (Or.inr (Or.inl ⟨rfl, rfl⟩)) (humode.2 hvu.1) (hvmode.1 hvu.2)
  · exact muNegThreeZeroFiveCorrect_graph_false_of_exterior
      G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange hu hv
        (fun i ↦ s (u i).1) (fun j ↦ s (v j).1)
        L₁.f_sign L₂.f_sign L₁.f_flip L₂.f_flip hcross false false
        (Or.inl ⟨rfl, rfl⟩) (humode.2 hone.1) (hvmode.2 hone.2)

end

end Erdos85

#print axioms Erdos85.h305_ledger_correct_shore_modes
#print axioms Erdos85.false_of_h305_source_or_transported

import Proofs.Erdos85MuNegFiveOneTwoShoreGeometry

/-!
# Within-shore geometry at the canonical `mu = -5`, `(k,r) = (0,4)` endpoint

Every diagonal defect row has three entries, all at odd offsets.  At the
normalized anchor row the two recorded cycle offsets are defects, so exactly
one of offsets `3,5` is a nondefect.  This is the local seed of the extra
same-shore matching omitted by the old 72-owner h504 encoding.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- At h504 all diagonal defects have odd offset. -/
theorem MuNegFiveExplicitRowParameterLedger.zeroFour_internal_imp_odd
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 4)
    (hshape : ZModEightSameSignShape N f 0) :
    ∀ i j : ZMod 8, N i j = 1 →
      j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7 := by
  rcases hshape with hzero | hone | htwo
  · obtain ⟨_, hzero⟩ := hzero
    intro i j hij
    by_contra hodd
    have heven := zmodEight_not_oddOffset_imp_evenOffset (j - i) hodd
    have hsame := (zmodEight_alternating_sign_eq_iff_evenOffset
      f L.f_sign L.f_flip i j).mpr heven
    exact hzero i j hsame hij
  · omega
  · omega

/-- The normalized h504 row has exactly one nondefect among offsets `3,5`. -/
theorem MuNegFiveExplicitRowParameterLedger.zeroFour_anchor_middleOdd_nondefect_card
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 0 4)
    (hshape : ZModEightSameSignShape N f 0)
    (hcycle : C8CycleEntriesOne N) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (j - 0 = 3 ∨ j - 0 = 5) ∧ N 0 j ≠ 1).card = 1 := by
  classical
  let A := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1
  let O := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    j - 0 = 1 ∨ j - 0 = 3 ∨ j - 0 = 5 ∨ j - 0 = 7
  have hAcard : A.card = 3 := by
    simpa [A] using L.internal_row 0
  have hOcard : O.card = 4 := by
    simpa [O] using zmodEight_oddOffset_card_four 0
  have hAO : A ⊆ O := by
    intro j hj
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      L.zeroFour_internal_imp_odd hshape 0 j hj⟩
  have hdiff : (O \ A).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAO, hOcard, hAcard]
  have heq : (O \ A) =
      (Finset.univ : Finset (ZMod 8)).filter (fun j ↦
        (j - 0 = 3 ∨ j - 0 = 5) ∧ N 0 j ≠ 1) := by
    ext j
    simp only [O, A, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hoff, hnot⟩
      rcases hoff with h1 | h3 | h5 | h7
      · exfalso
        apply hnot
        have hj : j = 1 := by simpa using h1
        simpa [hj] using hcycle.2
      · exact ⟨Or.inl h3, hnot⟩
      · exact ⟨Or.inr h5, hnot⟩
      · exfalso
        apply hnot
        have hj : j = -1 := by
          calc
            j = 7 := by simpa using h7
            _ = -1 := by decide
        simpa [hj] using hcycle.1
    · rintro ⟨hmid, hnot⟩
      exact ⟨hmid.elim (fun h ↦ Or.inr (Or.inl h))
        (fun h ↦ Or.inr (Or.inr (Or.inl h))), hnot⟩
  rw [← heq]
  exact hdiff

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- At either eligible middle-odd anchor offset, exterior adjacency is
exactly nondefectness. -/
theorem exteriorPairGraph_anchor_middleOdd_iff_not_defect
    (hfree : ¬ containsC4 V G)
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    (j : ZMod 8) (hj : j - 0 = 3 ∨ j - 0 = 5) :
    (exteriorPairGraph G c.supp).Adj (w 0) (w j) ↔
      ¬ ((secondOrderDefectGraph G).induce c.supp).Adj (w 0) (w j) := by
  let H := G.induce c.supp
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have hne : (0 : ZMod 8) ≠ j := by
    intro h
    subst j
    rcases hj with hj | hj
    · exact (by decide : ¬ ((0 : ZMod 8) = 3)) hj
    · exact (by decide : ¬ ((0 : ZMod 8) = 5)) hj
  have hvertex : w 0 ≠ w j := hwinj.ne hne
  refine ⟨fun h ↦ h.2.1, fun hnotD ↦ ⟨hvertex, hnotD, ?_⟩⟩
  intro hex
  have hc := (zmodEight_cycle_internalCommon_iff_offset_two_six
    H w hwinj hw 0 j hne).mp (by simpa [H] using hex)
  rcases hj with hj | hj <;> rw [hj] at hc <;> revert hc <;> decide

/-- The normalized h504 vertex has exactly one same-shore exterior candidate
among offsets `3,5`; hence a pair-complete encoding must include this shore
owner in addition to its 64 cross candidates. -/
theorem muNegFiveZeroFour_anchor_middleOdd_exterior_card
    (hfree : ¬ containsC4 V G)
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (L : MuNegFiveExplicitRowParameterLedger
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (w i) (w j)) M f g 0 4)
    (hshape : ZModEightSameSignShape
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (w i) (w j)) f 0)
    (hcycle : C8CycleEntriesOne
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (w i) (w j))) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (j - 0 = 3 ∨ j - 0 = 5) ∧
        (exteriorPairGraph G c.supp).Adj (w 0) (w j)).card = 1 := by
  have hcard := L.zeroFour_anchor_middleOdd_nondefect_card hshape hcycle
  rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      (j - 0 = 3 ∨ j - 0 = 5) ∧
        (exteriorPairGraph G c.supp).Adj (w 0) (w j)) =
      (Finset.univ : Finset (ZMod 8)).filter fun j ↦
        (j - 0 = 3 ∨ j - 0 = 5) ∧
          (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
            (w i) (w j)) 0 j ≠ 1 by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hj, hR⟩
      refine ⟨hj, ?_⟩
      have hn := (exteriorPairGraph_anchor_middleOdd_iff_not_defect
        G c hfree w hwinj hw j hj).mp hR
      simpa [SimpleGraph.adjMatrix_apply] using hn
    · rintro ⟨hj, hn⟩
      refine ⟨hj, (exteriorPairGraph_anchor_middleOdd_iff_not_defect
        G c hfree w hwinj hw j hj).mpr ?_⟩
      simpa [SimpleGraph.adjMatrix_apply] using hn]
  exact hcard

end

end Erdos85

#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroFour_internal_imp_odd
#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.zeroFour_anchor_middleOdd_nondefect_card
#print axioms Erdos85.exteriorPairGraph_anchor_middleOdd_iff_not_defect
#print axioms Erdos85.muNegFiveZeroFour_anchor_middleOdd_exterior_card

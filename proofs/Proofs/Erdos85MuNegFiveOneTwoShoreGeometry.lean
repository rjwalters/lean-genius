import Proofs.Erdos85MuNegFiveZeroThreeGraphRealization
import Proofs.Erdos85KOneOffsetTwoNondefect

/-!
# Within-shore geometry at the canonical `mu = -5`, `(k,r) = (1,2)` endpoint

The diagonal defect row has five entries.  Its unique same-sign entry is the
antipode, while all four odd offsets are opposite-sign.  Hence every pair
which could avoid an internal C8 common neighbor is already a defect pair:
the exterior-pair graph has no edge within either shore.  The h512 owner
universe is therefore cross-only.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem zmodEight_oddOrFour_card_five (i : ZMod 8) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 5 ∨ j - i = 7).card = 5 := by
  revert i
  decide

/-- Exact diagonal defect support at h512. -/
theorem MuNegFiveExplicitRowParameterLedger.oneTwo_internal_iff_oddOrFour
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitRowParameterLedger N M f g 1 2)
    (hshape : ZModEightSameSignShape N f 1) :
    ∀ i j : ZMod 8, N i j = 1 ↔
      j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 5 ∨ j - i = 7 := by
  rcases hshape with hzero | hone | htwo
  · omega
  · obtain ⟨_, hone⟩ := hone
    intro i
    let A := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N i j = 1
    let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
      j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 5 ∨ j - i = 7
    have hAcard : A.card = 5 := by
      simpa [A] using L.internal_row i
    have hScard : S.card = 5 := by
      simpa [S] using zmodEight_oddOrFour_card_five i
    have hsub : A ⊆ S := by
      intro j hj
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hodd : j - i = 1 ∨ j - i = 3 ∨
          j - i = 5 ∨ j - i = 7
      · rcases hodd with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · have heven := zmodEight_not_oddOffset_imp_evenOffset (j - i) hodd
        have hsame := (zmodEight_alternating_sign_eq_iff_evenOffset
          f L.f_sign L.f_flip i j).mpr heven
        exact Or.inr (Or.inr (Or.inl ((hone i j hsame).mp hj)))
    have hAS : A = S := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro j
    have := Finset.ext_iff.mp hAS j
    simpa [A, S] using this
  · omega

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- If the diagonal defect support is all odd offsets plus the antipode,
there are no within-cycle exterior pairs. -/
theorem exteriorPairGraph_cycle_false_of_oddOrFour_defect
    (hfree : ¬ containsC4 V G)
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    (hD : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (w i) (w j) ↔
        j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
          j - i = 5 ∨ j - i = 7) :
    ∀ i j : ZMod 8, ¬ (exteriorPairGraph G c.supp).Adj (w i) (w j) := by
  let H := G.induce c.supp
  intro i j hR
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
    G hfree c] at hR
  obtain ⟨hij, hnotD, hnoCommon⟩ := hR
  have hij' : i ≠ j := fun h ↦ hij (congrArg w h)
  have hall : j - i = 1 ∨ j - i = 2 ∨ j - i = 3 ∨
      j - i = 4 ∨ j - i = 5 ∨ j - i = 6 ∨ j - i = 7 := by
    have hzero : j - i ≠ 0 := by
      intro h
      exact hij' (sub_eq_zero.mp h).symm
    generalize j - i = d at hzero ⊢
    revert d
    decide
  rcases hall with h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact hnotD ((hD i j).mpr (Or.inl h1))
  · apply hnoCommon
    simpa [H] using
      (zmodEight_cycle_internalCommon_iff_offset_two_six
        H w hwinj hw i j hij').mpr (Or.inl h2)
  · exact hnotD ((hD i j).mpr (Or.inr (Or.inl h3)))
  · exact hnotD ((hD i j).mpr (Or.inr (Or.inr (Or.inl h4))))
  · exact hnotD ((hD i j).mpr
      (Or.inr (Or.inr (Or.inr (Or.inl h5)))))
  · apply hnoCommon
    simpa [H] using
      (zmodEight_cycle_internalCommon_iff_offset_two_six
        H w hwinj hw i j hij').mpr (Or.inr h6)
  · exact hnotD ((hD i j).mpr
      (Or.inr (Or.inr (Or.inr (Or.inr h7)))))

/-- Graph-facing h512 shore conclusion from an actual every-row ledger. -/
theorem muNegFiveOneTwo_no_sameShoreExterior_of_rowLedger
    (hfree : ¬ containsC4 V G)
    (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
    (hw : ∀ z, (G.induce c.supp).neighborFinset (w z) =
      {w (z - 1), w (z + 1)})
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (L : MuNegFiveExplicitRowParameterLedger
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (w i) (w j)) M f g 1 2)
    (hshape : ZModEightSameSignShape
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (w i) (w j)) f 1) :
    ∀ i j : ZMod 8, ¬ (exteriorPairGraph G c.supp).Adj (w i) (w j) := by
  apply exteriorPairGraph_cycle_false_of_oddOrFour_defect G c hfree w hwinj hw
  intro i j
  rw [← L.oneTwo_internal_iff_oddOrFour hshape i j]
  simp [SimpleGraph.adjMatrix_apply]

end

end Erdos85

#print axioms Erdos85.MuNegFiveExplicitRowParameterLedger.oneTwo_internal_iff_oddOrFour
#print axioms Erdos85.exteriorPairGraph_cycle_false_of_oddOrFour_defect
#print axioms Erdos85.muNegFiveOneTwo_no_sameShoreExterior_of_rowLedger

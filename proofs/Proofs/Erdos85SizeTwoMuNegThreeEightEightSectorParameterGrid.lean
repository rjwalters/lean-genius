import Proofs.Erdos85SizeTwoMuNegThreeEightEightAllTriangleFreeParameterBounds
import Proofs.Erdos85SizeTwoMuNegThreeEightEightNormalForm
import Proofs.Erdos85SizeTwoEigenlineInternalCycleSectorDichotomy

/-! # The shared signed-parameter grid for two C8 sectors -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- The two distinguished cycle entries of a normalized C8 row vanish. -/
def C8CycleEntriesZero (N : Matrix (ZMod 8) (ZMod 8) ℤ) : Prop :=
  N 0 (-1) ≠ 1 ∧ N 0 1 ≠ 1

/-- The two distinguished cycle entries of a normalized C8 row occur. -/
def C8CycleEntriesOne (N : Matrix (ZMod 8) (ZMod 8) ℤ) : Prop :=
  N 0 (-1) = 1 ∧ N 0 1 = 1

/-- With one common `(k,r)` ledger, the two shore colors give a three-cell
parameter grid: both all-triangle, mixed (forcing capacity five), or both
all-triangle-free. -/
theorem alternating_C8_twoShore_sector_parameter_grid
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f₁ f₂ : ZMod 8 → ℤ) (k r : ℕ)
    (hsign₁ : ∀ i, f₁ i = -1 ∨ f₁ i = 1)
    (hsign₂ : ∀ i, f₂ i = -1 ∨ f₂ i = 1)
    (hflip₁ : ∀ i, f₁ (i + 1) = -f₁ i)
    (hflip₂ : ∀ i, f₂ (i + 1) = -f₂ i)
    (hrow₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₁ 0 j = 1).card = 7 - r)
    (hrow₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₂ 0 j = 1).card = 7 - r)
    (hsame₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f₁ j = f₁ 0 ∧ N₁ 0 j = 1).card = k)
    (hsame₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f₂ j = f₂ 0 ∧ N₂ 0 j = 1).card = k)
    (hsector₁ : C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁)
    (hsector₂ : C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂) :
    (C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧ 5 ≤ r + k) ∨
      (((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧ r + k = 5) ∨
      (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧ r + k ≤ 5) := by
  rcases hsector₁ with hz₁ | ho₁ <;> rcases hsector₂ with hz₂ | ho₂
  · left
    exact ⟨hz₁, hz₂,
      alternating_C8_allTriangle_internal_parameter_lower
        N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ hz₁.1 hz₁.2⟩
  · right; left
    refine ⟨Or.inl ⟨hz₁, ho₂⟩, ?_⟩
    have hlo := alternating_C8_allTriangle_internal_parameter_lower
      N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ hz₁.1 hz₁.2
    have hhi := alternating_C8_allTriangleFree_internal_parameter_upper
      N₂ f₂ k r hsign₂ hflip₂ hrow₂ hsame₂ ho₂.1 ho₂.2
    omega
  · right; left
    refine ⟨Or.inr ⟨ho₁, hz₂⟩, ?_⟩
    have hlo := alternating_C8_allTriangle_internal_parameter_lower
      N₂ f₂ k r hsign₂ hflip₂ hrow₂ hsame₂ hz₂.1 hz₂.2
    have hhi := alternating_C8_allTriangleFree_internal_parameter_upper
      N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ ho₁.1 ho₁.2
    omega
  · right; right
    exact ⟨ho₁, ho₂,
      alternating_C8_allTriangleFree_internal_parameter_upper
        N₁ f₁ k r hsign₁ hflip₁ hrow₁ hsame₁ ho₁.1 ho₁.2⟩

/-- The graph-level internal-cycle dichotomy is exactly the zero/one
dichotomy for the two normalized cycle entries of the defect row. -/
theorem binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector
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
    (hc : c.supp.ncard = 8 * 2)
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)}) :
    let N : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ (u i) (u j)
    C8CycleEntriesZero N ∨ C8CycleEntriesOne N := by
  classical
  dsimp only
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let N : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  have hsector := binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
    G hfree (q := 8) (by omega) (by decide) hreg hcard c hc a
  have hu0a : u 0 ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  rcases hsector with hall0 | hall2
  · left
    constructor <;> intro hNj
    · have hDadj : (secondOrderDefectGraph G).Adj (u 0).1 (u (-1)).1 := by
        simpa [N, SimpleGraph.adjMatrix_apply] using hNj
      have hK : K.Adj (u 0) (u (-1)) := hDadj
      have hH : Hc.Adj (u 0) (u (-1)) := by
        rw [← Hc.mem_neighborFinset, hu]
        simp
      have htf : (triangleFreeEdgeGraph G).Adj (u 0).1 (u (-1)).1 := by
        rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact ⟨hH, hK⟩
      have hpos : 0 < (triangleFreeEdgeGraph G).degree (u 0).1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨(u (-1)).1,
          ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
      rw [hall0 (u 0) hu0a] at hpos
      omega
    · have hDadj : (secondOrderDefectGraph G).Adj (u 0).1 (u 1).1 := by
        simpa [N, SimpleGraph.adjMatrix_apply] using hNj
      have hK : K.Adj (u 0) (u 1) := hDadj
      have hH : Hc.Adj (u 0) (u 1) := by
        rw [← Hc.mem_neighborFinset, hu]
        simp
      have htf : (triangleFreeEdgeGraph G).Adj (u 0).1 (u 1).1 := by
        rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact ⟨hH, hK⟩
      have hpos : 0 < (triangleFreeEdgeGraph G).degree (u 0).1 := by
        rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact Finset.card_pos.mpr ⟨(u 1).1,
          ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
      rw [hall0 (u 0) hu0a] at hpos
      omega
  · right
    have hcycle (j : ZMod 8) (hj : j = -1 ∨ j = 1) : N 0 j = 1 := by
      let T := (Finset.univ : Finset c.supp).filter fun y ↦
        (triangleFreeEdgeGraph G).Adj (u 0).1 y.1
      have himage : Finset.image Subtype.val T =
          (triangleFreeEdgeGraph G).neighborFinset (u 0).1 := by
        ext y
        simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
          true_and, SimpleGraph.mem_neighborFinset]
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact hz
        · intro htf
          have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u 0).1 y := by
            rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
            exact htf
          have hyc : y ∈ c.supp := by
            rw [SimpleGraph.ConnectedComponent.mem_supp_iff c y]
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              hpair.2).symm.trans
                ((SimpleGraph.ConnectedComponent.mem_supp_iff c (u 0).1).mp
                  (u 0).2)
          exact ⟨⟨y, hyc⟩, htf, rfl⟩
      have hTcard : T.card = 2 := by
        rw [← Finset.card_image_of_injective T Subtype.val_injective,
          himage, (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
        exact hall2 (u 0) hu0a
      have hHdegree : Hc.degree (u 0) = 2 := by
        exact binarySquare_regular_degree_induce_defectComponent_eq_part
          G hfree (by omega) hreg hcard c (m := 2)
            (by simpa [Nat.mul_comm] using hc) (u 0)
      have hTsub : T ⊆ Hc.neighborFinset (u 0) := by
        intro y hy
        have htf := (Finset.mem_filter.mp hy).2
        have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u 0).1 y.1 := by
          rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
          exact htf
        exact (Hc.mem_neighborFinset (u 0) y).mpr hpair.1
      have hTeq : T = Hc.neighborFinset (u 0) := by
        apply Finset.eq_of_subset_of_card_le hTsub
        rw [hTcard, Hc.card_neighborFinset_eq_degree, hHdegree]
      have hHj : Hc.Adj (u 0) (u j) := by
        rw [← Hc.mem_neighborFinset, hu]
        rcases hj with rfl | rfl <;> simp
      have hujT : u j ∈ T := by
        rw [hTeq]
        exact (Hc.mem_neighborFinset (u 0) (u j)).mpr hHj
      have htf := (Finset.mem_filter.mp hujT).2
      have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u 0).1 (u j).1 := by
        rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact htf
      have hK : K.Adj (u 0) (u j) := hpair.2
      simp [N, SimpleGraph.adjMatrix_apply, hK]
    exact ⟨hcycle (-1) (Or.inl rfl), hcycle 1 (Or.inr rfl)⟩

end


end Erdos85

#print axioms Erdos85.alternating_C8_twoShore_sector_parameter_grid
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector

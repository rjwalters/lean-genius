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

set_option maxHeartbeats 1200000 in
/-- Graph-facing shared-parameter sector grid for the normalized `mu=-3`
C8+C8 branch. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_sector_parameter_grid
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
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ, k ≤ 1 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      3 ≤ r + k ∧ r + k ≤ 6 ∧
      ((C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧ 5 ≤ r + k) ∨
        ((((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
            (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧
              r + k = 5) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧ r + k ≤ 5))) := by
  classical
  dsimp only
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨_ha8, _hb8, r, hr2, hr7, haa, habq, _hbaq, hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨k, hk, hA, hB, hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hHdegree : ∀ z : c.supp, Hc.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcommReal : K.adjMatrix ℝ * Hc.adjMatrix ℝ =
      Hc.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hvrangeB : Set.range v = ↑B := by
    rw [hvrange]
    ext x
    simp [B]
  have hu0A : u 0 ∈ A := by
    change u 0 ∈ (↑A : Set c.supp)
    rw [← hurangeA]
    exact ⟨0, rfl⟩
  have hv0B : v 0 ∈ B := by
    change v 0 ∈ (↑B : Set c.supp)
    rw [← hvrangeB]
    exact ⟨0, rfl⟩
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  have hrow₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₁ 0 j = 1).card = 7 - r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N₁ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (u j)) by
      ext j; simp [N₁, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K A u huinj hurangeA (u 0)]
    have hqcard : (componentNeighborFinset K Hc a (u 0)).card = 7 - r := by
      rw [← componentQuotientMatrix_apply_eq K Hc 2 hHdegree hcommReal
        a a (by simpa [A] using hu0A)]
      exact haa
    have heq : A.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K Hc a (u 0) := by
      ext y
      simp [A, Hc, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hrow₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₂ 0 j = 1).card = 7 - r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N₂ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (v 0) (v j)) by
      ext j; simp [N₂, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K B v hvinj hvrangeB (v 0)]
    have hqcard : (componentNeighborFinset K Hc b (v 0)).card = 7 - r := by
      rw [← componentQuotientMatrix_apply_eq K Hc 2 hHdegree hcommReal
        b b (by simpa [B] using hv0B)]
      exact hbb
    have heq : B.filter (fun y ↦ K.Adj (v 0) y) =
        componentNeighborFinset K Hc b (v 0) := by
      ext y
      simp [B, Hc, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hsame₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j).1 = s (u 0).1 ∧ N₁ 0 j = 1).card = k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u 0).1 ∧ N₁ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (u j).1 = s (u 0).1 ∧ K.Adj (u 0) (u j)) by
      ext j; simp [N₁, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) 0]
    exact hA (u 0) hu0A
  have hsame₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (v j).1 = s (v 0).1 ∧ N₂ 0 j = 1).card = k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (v 0).1 ∧ N₂ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (v j).1 = s (v 0).1 ∧ K.Adj (v 0) (v j)) by
      ext j; simp [N₂, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) 0]
    exact hB (v 0) hv0B
  have hMrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      M 0 j = 1).card = r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K B v hvinj hvrangeB (u 0)]
    have hqcard : (componentNeighborFinset K Hc b (u 0)).card = r := by
      rw [← componentQuotientMatrix_apply_eq K Hc 2 hHdegree hcommReal
        a b (by simpa [A] using hu0A)]
      exact habq
    have heq : B.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K Hc b (u 0) := by
      ext y
      simp [B, Hc, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hMsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (v j).1 = s (u 0).1 ∧ M 0 j = 1).card = 2 - k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (u 0).1 ∧ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (v j).1 = s (u 0).1 ∧ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support_from K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) (u 0)]
    exact hcrossA (u 0) hu0A
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
  have hbounds := alternating_C8_internal_cross_parameter_bounds N₁ M
    (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r hk
    (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
    (flip_of_coordinates u hu) (flip_of_coordinates v hv)
    hrow₁ hsame₁ hMrow hMsame
  have hk1 : k ≤ 1 := by
    have hkne2 : k ≠ 2 := by
      intro hk2
      obtain ⟨k', r', _hk', _hr2', _hr7', hnf⟩ :=
        orderSixtyFour_sizeTwo_muNegThree_eightEight_signed_normalForm
          G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
            u v huinj hvinj hurange hvrange hu hv
      rcases hnf with ⟨_hk'0, hrowsA, _hrowsB⟩ |
          ⟨_hk'1, φ, hφ, _horient⟩
      · have hc0 := hcrossA (u 0) hu0A
        rw [hk2] at hc0
        have hc2 := hrowsA (u 0) (by simpa [A] using hu0A)
        have hc2' : (B.filter fun y ↦
            K.Adj (u 0) y ∧ s y.1 = s (u 0).1).card = 2 := by
          simpa [B, K] using hc2
        rw [hc0] at hc2'
        omega
      · have hvφB : v (φ 0) ∈ B := by
          change v (φ 0) ∈ (↑B : Set c.supp)
          rw [← hvrangeB]
          exact ⟨φ 0, rfl⟩
        have hedge := (hφ 0 (φ 0)).2 rfl
        have hmem : v (φ 0) ∈ B.filter fun y ↦
            K.Adj (u 0) y ∧ s y.1 = s (u 0).1 := by
          rw [Finset.mem_filter]
          exact ⟨hvφB, hedge.2, hedge.1.symm⟩
        have hpos := Finset.card_pos.mpr ⟨v (φ 0), hmem⟩
        have hc0 := hcrossA (u 0) hu0A
        rw [hk2] at hc0
        rw [hc0] at hpos
        omega
    omega
  have hsector₁ : C8CycleEntriesZero N₁ ∨ C8CycleEntriesOne N₁ := by
    simpa [N₁, K] using
      (binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector
        G hfree hreg hcard c hc a u hurange hu)
  have hsector₂ : C8CycleEntriesZero N₂ ∨ C8CycleEntriesOne N₂ := by
    simpa [N₂, K] using
      (binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector
        G hfree hreg hcard c hc b v hvrange hv)
  refine ⟨k, r, hk1, hr2, hr7, hbounds.1, hbounds.2.1, ?_⟩
  exact alternating_C8_twoShore_sector_parameter_grid N₁ N₂
    (fun i ↦ s (u i).1) (fun i ↦ s (v i).1) k r
      (fun i ↦ hs_in _ (u i).2) (fun i ↦ hs_in _ (v i).2)
      (flip_of_coordinates u hu) (flip_of_coordinates v hv)
      hrow₁ hrow₂ hsame₁ hsame₂ hsector₁ hsector₂

end


end Erdos85

#print axioms Erdos85.alternating_C8_twoShore_sector_parameter_grid
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_sector_parameter_grid

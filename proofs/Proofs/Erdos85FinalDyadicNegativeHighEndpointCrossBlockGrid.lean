import Proofs.Erdos85FinalDyadicNegativeHighEndpointBlockPartition

/-!
# Cross-block grid saturation at the negative-high endpoint

The exact defect matching between two empty blocks forces all remaining
cross-block pairs to use their unique graph-common-neighbor slot.  After
double counting, every non-center neighbor of a point in the first block
meets the second block exactly once.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Fix distinct empty centers `e,f`, a point `x∈N(e)`, and a graph neighbor
`z` of `x` other than `e`.  At saturated support, `z` has exactly one graph
neighbor in the block `N(f)`. -/
theorem finalDyadic_endpoint_otherEmptyBlock_grid_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j r : ℕ} (hq : 8 ≤ q)
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hdisp : 2 * (S.card : ℤ) - Fintype.card V = 2 * r)
    (hr : 0 < r) (hrhalf : r < 2 ^ j)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {e f x z : V} (he : e ∈ emptyLineCenters G S)
    (hf : f ∈ emptyLineCenters G S) (hef : e ≠ f)
    (hx : x ∈ G.neighborFinset e)
    (hz : z ∈ G.neighborFinset x) (hze : z ≠ e) :
    (G.neighborFinset z ∩ G.neighborFinset f).card = 1 := by
  let D := secondOrderDefectGraph G
  let B := G.neighborFinset f
  have hefD : D.Adj e f := hemptyClique he hf hef
  have hblocks : G.neighborFinset e ∩ B = ∅ := by
    apply Finset.card_eq_zero.mp
    exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hef).mp hefD
  have hxNotB : x ∉ B := by
    intro hxf
    have : x ∈ G.neighborFinset e ∩ B :=
      Finset.mem_inter.mpr ⟨hx, hxf⟩
    simpa [hblocks] using this
  have hmatch :=
    finalDyadic_endpoint_otherEmptyBlock_defectNeighbor_card_eq_one
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique he hf hef hx
  change (D.neighborFinset x ∩ B).card = 1 at hmatch
  have hindicator :
      (∑ y ∈ B, if y ∈ D.neighborFinset x then 1 else 0) =
        (D.neighborFinset x ∩ B).card := by
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext y
    simp only [Finset.mem_filter, Finset.mem_inter]
    tauto
  have hcommonSumAdd :
      (∑ y ∈ B, (G.neighborFinset y ∩ G.neighborFinset x).card) +
          (D.neighborFinset x ∩ B).card = B.card := by
    rw [← hindicator, ← Finset.sum_add_distrib]
    calc
      (∑ y ∈ B,
          ((G.neighborFinset y ∩ G.neighborFinset x).card +
            if y ∈ D.neighborFinset x then 1 else 0)) =
          ∑ _y ∈ B, 1 := by
            apply Finset.sum_congr rfl
            intro y hy
            have hxy : x ≠ y := fun h => hxNotB (h ▸ hy)
            rw [Finset.inter_comm,
              card_common_eq_if_secondOrderDefect G hfree x y hxy]
            by_cases hyD : y ∈ D.neighborFinset x
            · have hyAdj : (secondOrderDefectGraph G).Adj x y :=
                (D.mem_neighborFinset x y).mp hyD
              simp [hyD, hyAdj]
            · have hyNotAdj : ¬(secondOrderDefectGraph G).Adj x y := fun h =>
                hyD ((D.mem_neighborFinset x y).mpr h)
              simp [hyD, hyNotAdj]
      _ = B.card := by simp
  have hBcard : B.card = q := by
    dsimp only [B]
    rw [G.card_neighborFinset_eq_degree, hreg]
  have hcommonSum :
      (∑ y ∈ B, (G.neighborFinset y ∩ G.neighborFinset x).card) = q - 1 := by
    rw [hmatch, hBcard] at hcommonSumAdd
    omega
  have hcomm := sum_card_neighbor_inter_comm G
    (G.neighborFinset x) B
  rw [hcommonSum] at hcomm
  have heN : e ∈ G.neighborFinset x :=
    (G.mem_neighborFinset x e).mpr
      ((G.mem_neighborFinset e x).mp hx).symm
  have heTerm : (G.neighborFinset e ∩ B).card = 0 := by simp [hblocks]
  have heraseSum :
      ∑ w ∈ (G.neighborFinset x).erase e,
          (G.neighborFinset w ∩ B).card = q - 1 := by
    have hsplit := Finset.sum_erase_add (G.neighborFinset x)
      (fun w => (G.neighborFinset w ∩ B).card) heN
    rw [heTerm, add_zero, hcomm] at hsplit
    exact hsplit
  have heraseCard : ((G.neighborFinset x).erase e).card = q - 1 := by
    rw [Finset.card_erase_of_mem heN,
      G.card_neighborFinset_eq_degree, hreg]
  have htermLe : ∀ w ∈ (G.neighborFinset x).erase e,
      (G.neighborFinset w ∩ B).card ≤ 1 := by
    intro w hw
    have hwNotF : w ≠ f := by
      intro h
      subst w
      have hfx : f ∈ G.neighborFinset x := Finset.mem_of_mem_erase hw
      exact hxNotB ((G.mem_neighborFinset f x).mpr
        ((G.mem_neighborFinset x f).mp hfx).symm)
    exact common_le_one_of_not_containsC4 hfree w f hwNotF
  have hall := eq_bound_of_sum_eq_card_mul
    ((G.neighborFinset x).erase e)
    (fun w => (G.neighborFinset w ∩ B).card) 1 htermLe
    (by rw [heraseSum, heraseCard]; simp)
  exact hall z (Finset.mem_erase.mpr ⟨hze, hz⟩)

end


end Erdos85

#print axioms Erdos85.finalDyadic_endpoint_otherEmptyBlock_grid_card_eq_one

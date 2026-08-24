import Proofs.Erdos85FinalDyadicEndpointResidualSeparation

/-!
# Perfect neighborhood grids between residual vertices and empty blocks

For a residual vertex `w` and an empty center `e`, the punctured second-layer
partition under `e` partitions all `q` neighbors of `w` among the `q` branches
rooted at `N(e)`.  C4-freeness gives capacity one in every branch, so every
branch is occupied exactly once.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every point of an empty block has exactly one common graph neighbor with
every endpoint residual-cell vertex. -/
theorem finalDyadic_endpoint_residual_emptyBlock_commonNeighbor_card_eq_one
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
    {w e x : V}
    (hw : w ∈ (Finset.univ : Finset V) \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r))
    (he : e ∈ emptyLineCenters G S)
    (hx : x ∈ G.neighborFinset e) :
    (G.neighborFinset x ∩ G.neighborFinset w).card = 1 := by
  let B := G.neighborFinset e
  let C := G.neighborFinset w
  have hCnonexceptional : ∀ z ∈ C,
      z ∉ exceptionalSignedSupport G S q := by
    intro z hz
    have hzH :=
      finalDyadic_endpoint_residual_neighborFinset_subset_nonexceptional
        G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
          hsupport hemptyClique hw hz
    exact (Finset.mem_sdiff.mp hzH).2
  have hbranch : ∀ z : {z // z ∈ C}, ∃! y,
      y ∈ B ∧ z.1 ∈ (G.neighborFinset y).erase e := by
    intro z
    exact (finalDyadic_endpoint_nonexceptional_existsUnique_emptyBranch
      G hfree hqa hreg hcard S hdiv hsupport hemptyClique he).mp
        (hCnonexceptional z z.2)
  let f : {z // z ∈ C} → {y // y ∈ B} := fun z =>
    ⟨Classical.choose (hbranch z), (Classical.choose_spec (hbranch z)).1.1⟩
  have hfprop : ∀ z : {z // z ∈ C},
      z.1 ∈ (G.neighborFinset (f z).1).erase e := by
    intro z
    exact (Classical.choose_spec (hbranch z)).1.2
  have hBM : B ⊆ finalDyadicNegativeHighCutCenters G S j r := by
    intro y hy
    exact finalDyadic_emptyCenter_neighborFinset_subset_negativeHigh
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique he hy
  have hfw : ∀ z : {z // z ∈ C}, (f z).1 ≠ w := by
    intro z h
    have hwNotM : w ∉ finalDyadicNegativeHighCutCenters G S j r := by
      intro hwM
      exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_right S hwM)
    exact hwNotM (h ▸ hBM (f z).2)
  have hfinj : Function.Injective f := by
    intro z₁ z₂ hf
    apply Subtype.ext
    have hz₁ : z₁.1 ∈ G.neighborFinset (f z₁).1 ∩ G.neighborFinset w := by
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_of_mem_erase (hfprop z₁), z₁.2⟩
    have hz₂ : z₂.1 ∈ G.neighborFinset (f z₁).1 ∩ G.neighborFinset w := by
      have hz₂' := hfprop z₂
      rw [← hf] at hz₂'
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_of_mem_erase hz₂', z₂.2⟩
    exact Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree (f z₁).1 w (hfw z₁))
        z₁.1 hz₁ z₂.1 hz₂
  have hcardCB : Fintype.card {z // z ∈ C} =
      Fintype.card {y // y ∈ B} := by
    simp only [Fintype.card_coe]
    dsimp only [B, C]
    rw [G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree,
      hreg, hreg]
  have hfsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hfinj, hcardCB⟩).2
  obtain ⟨z, hz⟩ := hfsurj ⟨x, hx⟩
  have hxw : x ≠ w := by
    have hwNotM : w ∉ finalDyadicNegativeHighCutCenters G S j r := by
      intro hwM
      exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_right S hwM)
    intro h
    exact hwNotM (h ▸ hBM hx)
  have hzcommon : z.1 ∈ G.neighborFinset x ∩ G.neighborFinset w := by
    have hzbranch := hfprop z
    have hzval : (f z).1 = x := congrArg Subtype.val hz
    rw [hzval] at hzbranch
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_of_mem_erase hzbranch, z.2⟩
  have hpos : 1 ≤ (G.neighborFinset x ∩ G.neighborFinset w).card :=
    Finset.one_le_card.mpr ⟨z.1, hzcommon⟩
  have hle := common_le_one_of_not_containsC4 hfree x w hxw
  omega

end

end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_residual_emptyBlock_commonNeighbor_card_eq_one

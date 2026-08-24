import Proofs.Erdos85FinalDyadicEmptySecondLayerEndpointPartition

/-!
# Equitable incidence from the half layer to empty blocks

At saturated exceptional support, every nonexceptional vertex has exactly one
graph neighbor in each empty-center block.  Since those blocks partition the
negative-high class, its degree into that class is the empty population.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A nonexceptional vertex has exactly one graph neighbor in the block of
each empty center. -/
theorem finalDyadic_endpoint_nonexceptional_neighbor_inter_emptyBlock_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q j : ℕ}
    (hqa : q = 2 * 2 ^ j) (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hsupport : (exceptionalSignedSupport G S q).card = q)
    (hemptyClique : ∀ ⦃u v⦄,
      u ∈ emptyLineCenters G S → v ∈ emptyLineCenters G S → u ≠ v →
        (secondOrderDefectGraph G).Adj u v)
    {f z : V} (hf : f ∈ emptyLineCenters G S)
    (hz : z ∉ exceptionalSignedSupport G S q) :
    (G.neighborFinset z ∩ G.neighborFinset f).card = 1 := by
  have huniq :=
    (finalDyadic_endpoint_nonexceptional_existsUnique_emptyBranch
      G hfree hqa hreg hcard S hdiv hsupport hemptyClique hf).mp hz
  obtain ⟨x, hx, hxUnique⟩ := huniq
  have hfSupport : f ∈ exceptionalSignedSupport G S q := by
    rw [exceptionalSignedSupport_eq_full_union_empty]
    exact Finset.mem_union_right _ hf
  have hzf : z ≠ f := fun h => hz (h ▸ hfSupport)
  apply Finset.card_eq_one.mpr
  refine ⟨x, ?_⟩
  ext y
  constructor
  · intro hy
    have hyData := Finset.mem_inter.mp hy
    have hzy : z ∈ G.neighborFinset y :=
      (G.mem_neighborFinset y z).mpr
        ((G.mem_neighborFinset z y).mp hyData.1).symm
    have hyCoord : y ∈ G.neighborFinset f ∧
        z ∈ (G.neighborFinset y).erase f :=
      ⟨hyData.2, Finset.mem_erase.mpr ⟨hzf, hzy⟩⟩
    have hyx : y = x := hxUnique y hyCoord
    simpa [hyx]
  · intro hy
    have hyx : y = x := Finset.mem_singleton.mp hy
    subst y
    have hxData := hx.1
    have hzxData := Finset.mem_erase.mp hx.2
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z x).mpr
          ((G.mem_neighborFinset x z).mp hzxData.2).symm,
        hxData⟩

/-- Therefore a nonexceptional vertex has exactly `|E|` graph neighbors in
the negative-high class `M`. -/
theorem finalDyadic_endpoint_nonexceptional_neighbor_inter_negativeHigh_card_eq_empty
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
    {z : V} (hz : z ∉ exceptionalSignedSupport G S q) :
    (G.neighborFinset z ∩
      finalDyadicNegativeHighCutCenters G S j r).card =
        (emptyLineCenters G S).card := by
  let E := emptyLineCenters G S
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hpair : (↑E : Set V).PairwiseDisjoint
      (fun f => G.neighborFinset z ∩ G.neighborFinset f) := by
    intro f hf g hg hfg
    exact (finalDyadic_emptyCenter_neighborFinset_disjoint
      G hfree S hemptyClique hf hg hfg).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hunion : E.biUnion
      (fun f => G.neighborFinset z ∩ G.neighborFinset f) =
        G.neighborFinset z ∩ M := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_inter]
    constructor
    · rintro ⟨f, hfE, hyz, hyf⟩
      exact ⟨hyz,
        (finalDyadic_mem_negativeHigh_iff_exists_empty_neighbor
          G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
            hsupport hemptyClique y).mpr ⟨f, hfE, hyf⟩⟩
    · rintro ⟨hyz, hyM⟩
      obtain ⟨f, hfE, hyf⟩ :=
        (finalDyadic_mem_negativeHigh_iff_exists_empty_neighbor
          G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
            hsupport hemptyClique y).mp hyM
      exact ⟨f, hfE, hyz, hyf⟩
  rw [← hunion, Finset.card_biUnion hpair]
  calc
    (∑ f ∈ E, (G.neighborFinset z ∩ G.neighborFinset f).card) =
        ∑ _f ∈ E, 1 := by
          apply Finset.sum_congr rfl
          intro f hf
          exact finalDyadic_endpoint_nonexceptional_neighbor_inter_emptyBlock_card_eq_one
            G hfree hqa hreg hcard S hdiv hsupport hemptyClique hf hz
    _ = E.card := by simp

end


end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_nonexceptional_neighbor_inter_emptyBlock_card_eq_one
#print axioms
  Erdos85.finalDyadic_endpoint_nonexceptional_neighbor_inter_negativeHigh_card_eq_empty

import Proofs.Erdos85FinalDyadicEndpointHalfToEmptyIncidence

/-!
# Residual degree profile of the endpoint half layer

For a nonexceptional vertex, the graph neighborhood splits into the shore,
the negative-high block union, and a residual set of size exactly `r`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At saturated support, every nonexceptional vertex has shore degree
`2^j`, negative-high degree `2^j-r`, and residual degree `r`. -/
theorem finalDyadic_endpoint_nonexceptional_residual_degree_profile
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
    (G.neighborFinset z ∩ S).card = 2 ^ j ∧
    (G.neighborFinset z ∩
      finalDyadicNegativeHighCutCenters G S j r).card = 2 ^ j - r ∧
    (G.neighborFinset z \ (S ∪
      finalDyadicNegativeHighCutCenters G S j r)).card = r := by
  let M := finalDyadicNegativeHighCutCenters G S j r
  have hzOcc : (G.neighborFinset z ∩ S).card = 2 ^ j := by
    rcases finalDyadic_occupancy_trichotomy G hqa hreg S hdiv z with
      hzero | hhalf | hfull
    · have hzE : z ∈ emptyLineCenters G S :=
        (mem_emptyLineCenters G S z).mpr hzero
      exact (hz (by
        rw [exceptionalSignedSupport_eq_full_union_empty]
        exact Finset.mem_union_right _ hzE)).elim
    · omega
    · have hzF : z ∈ fullLineCenters G S q :=
        (mem_fullLineCenters G S q z).mpr hfull
      exact (hz (by
        rw [exceptionalSignedSupport_eq_full_union_empty]
        exact Finset.mem_union_left _ hzF)).elim
  have hzMcard :=
    finalDyadic_endpoint_nonexceptional_neighbor_inter_negativeHigh_card_eq_empty
      G hfree hq hqa hreg hcard S hdiv hdisp hr hrhalf
        hsupport hemptyClique hz
  have hpop := finalDyadic_endpoint_full_empty_card_eq
    G hqa hreg S hdiv hdisp (by omega) hsupport
  have hEpop := hpop.1
  change (emptyLineCenters G S).card = 2 ^ j - r at hEpop
  change (G.neighborFinset z ∩ M).card =
    (emptyLineCenters G S).card at hzMcard
  have hzM : (G.neighborFinset z ∩ M).card = 2 ^ j - r := by
    omega
  have hMS : Disjoint M S := by
    rw [Finset.disjoint_left]
    intro x hxM hxS
    have hxNotS : x ∉ S :=
      Finset.mem_compl.mp (Finset.mem_filter.mp hxM).1
    exact hxNotS hxS
  have hsplitSet : G.neighborFinset z ∩ (S ∪ M) =
      (G.neighborFinset z ∩ S) ∪ (G.neighborFinset z ∩ M) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hpartsDisj : Disjoint (G.neighborFinset z ∩ S)
      (G.neighborFinset z ∩ M) := by
    exact Finset.disjoint_left.mpr fun x hxS hxM =>
      Finset.disjoint_left.mp hMS
        (Finset.mem_inter.mp hxM).2 (Finset.mem_inter.mp hxS).2
  have hinterCard : (G.neighborFinset z ∩ (S ∪ M)).card =
      2 ^ j + (2 ^ j - r) := by
    rw [hsplitSet, Finset.card_union_of_disjoint hpartsDisj,
      hzOcc, hzM]
  have hdegree : (G.neighborFinset z).card = q := by
    rw [G.card_neighborFinset_eq_degree, hreg]
  have hpartition := Finset.card_sdiff_add_card_inter
    (G.neighborFinset z) (S ∪ M)
  rw [hdegree, hinterCard, hqa] at hpartition
  have hresidual : (G.neighborFinset z \ (S ∪ M)).card = r := by
    omega
  exact ⟨hzOcc, hzM, hresidual⟩

end


end Erdos85

#print axioms
  Erdos85.finalDyadic_endpoint_nonexceptional_residual_degree_profile

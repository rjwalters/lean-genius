import Proofs.Erdos85BinarySquareMuThreeExteriorGrid
import Proofs.Erdos85CrossEdgeTriangleDichotomy
import Proofs.Erdos85BinarySquareSizeTwoJointEigenvectorMuOneExclusion

/-! # Row-pair balance at a normalized size-two component

Summing the row-hit law over one exterior row and double-counting the exterior
edges between two rows gives a symmetric internal-obstruction count.  In grid
coordinates this is the graph-facing form of
`|N_H(x') ∩ K(x)| = |N_H(x) ∩ K(x')|`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- **Row-pair balance.**  For two vertices `x,x'` of a normalized size-two
defect component, sum over the exterior neighbours of `x` the number of
internal neighbours of `x'` also adjacent to that exterior vertex.  This is
symmetric in `x,x'`. -/
theorem binarySquare_regular_sizeTwoComponent_rowPair_internalHit_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q)
    (hcardV : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x x' : c.supp) :
    let R : c.supp → Finset V := fun z =>
      (G.neighborFinset z.1).filter
        (fun u => (secondOrderDefectGraph G).connectedComponentMk u ≠ c)
    (∑ u ∈ R x,
      ((G.neighborFinset x'.1).filter
        (fun y => y ∈ c.supp ∧ G.Adj u y)).card) =
    ∑ u ∈ R x',
      ((G.neighborFinset x.1).filter
        (fun y => y ∈ c.supp ∧ G.Adj u y)).card := by
  classical
  let R : c.supp → Finset V := fun z =>
    (G.neighborFinset z.1).filter
      (fun u => (secondOrderDefectGraph G).connectedComponentMk u ≠ c)
  let I : c.supp → V → ℕ := fun z u =>
    ((G.neighborFinset z.1).filter
      (fun y => y ∈ c.supp ∧ G.Adj u y)).card
  let E : c.supp → V → ℕ := fun z u =>
    ((G.neighborFinset u).filter
      (fun y => y ∉ c.supp ∧ G.Adj z.1 y)).card
  have hRcard : ∀ z : c.supp, (R z).card = q - 2 := by
    intro z
    exact binarySquare_regular_sizeTwoComponent_exteriorNeighborCard
      G hfree hq hreg hcardV c hc z
  have hrow : ∀ z : c.supp, ∀ u ∈ R x,
      I z u + E z u = 1 := by
    intro z u hu
    have huout : u ∉ c.supp := by
      intro huc
      have heq := (ConnectedComponent.mem_supp_iff c u).mp huc
      exact (Finset.mem_filter.mp hu).2 heq
    exact card_internal_common_add_card_exterior_common_eq_one
      G hfree c z.2 huout
  have hrow' : ∀ z : c.supp, ∀ u ∈ R x',
      I z u + E z u = 1 := by
    intro z u hu
    have huout : u ∉ c.supp := by
      intro huc
      have heq := (ConnectedComponent.mem_supp_iff c u).mp huc
      exact (Finset.mem_filter.mp hu).2 heq
    exact card_internal_common_add_card_exterior_common_eq_one
      G hfree c z.2 huout
  have hE_as_row : ∀ z : c.supp, ∀ u : V,
      E z u = ((G.neighborFinset u).filter (fun y => y ∈ R z)).card := by
    intro z u
    apply congrArg Finset.card
    ext y
    simp only [R, Finset.mem_filter, mem_neighborFinset]
    rw [ConnectedComponent.mem_supp_iff]
    tauto
  have hedgeZ := sum_sum_filter_neighborFinset_comm
    G (R x) (R x') (fun _ _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hedgeZ
  have hedge : (∑ u ∈ R x, E x' u) = ∑ u ∈ R x', E x u := by
    simp_rw [hE_as_row]
    exact_mod_cast hedgeZ
  have hsumRow : (∑ u ∈ R x, I x' u) + (∑ u ∈ R x, E x' u) = (R x).card := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ u ∈ R x, (I x' u + E x' u) = ∑ _u ∈ R x, 1 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hrow x' u hu
      _ = (R x).card := by simp
  have hsumRow' : (∑ u ∈ R x', I x u) + (∑ u ∈ R x', E x u) = (R x').card := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ u ∈ R x', (I x u + E x u) = ∑ _u ∈ R x', 1 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hrow' x u hu
      _ = (R x').card := by simp
  change (∑ u ∈ R x, I x' u) = ∑ u ∈ R x', I x u
  rw [hRcard x] at hsumRow
  rw [hRcard x'] at hsumRow'
  omega

end


end Erdos85

#print axioms
  Erdos85.binarySquare_regular_sizeTwoComponent_rowPair_internalHit_balance

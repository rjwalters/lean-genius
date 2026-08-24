import Proofs.Erdos85FinalDyadicExceptionalSupportBridge

/-!
# Shore-complement symmetry at the final dyadic scale

Complementing a shore swaps its full and empty line-center populations.
At the final scale it leaves the odd dyadic occupancy support unchanged.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Full centers of the complementary shore are exactly the original empty
centers. -/
theorem fullLineCenters_compl_eq_emptyLineCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q) (S : Finset V) :
    fullLineCenters G (Sᶜ : Finset V) q = emptyLineCenters G S := by
  ext v
  rw [mem_fullLineCenters, mem_emptyLineCenters]
  have hcomp := neighbor_inter_complement_card G S v
  change (G.neighborFinset v ∩ (Sᶜ : Finset V)).card =
    G.degree v - (G.neighborFinset v ∩ S).card at hcomp
  rw [hcomp, hreg]
  have hnle : (G.neighborFinset v ∩ S).card ≤ q := by
    calc
      (G.neighborFinset v ∩ S).card ≤ (G.neighborFinset v).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  omega

/-- Empty centers of the complementary shore are exactly the original full
centers. -/
theorem emptyLineCenters_compl_eq_fullLineCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q) (S : Finset V) :
    emptyLineCenters G (Sᶜ : Finset V) = fullLineCenters G S q := by
  ext v
  rw [mem_emptyLineCenters, mem_fullLineCenters]
  have hcomp := neighbor_inter_complement_card G S v
  change (G.neighborFinset v ∩ (Sᶜ : Finset V)).card =
    G.degree v - (G.neighborFinset v ∩ S).card at hcomp
  rw [hcomp, hreg]
  have hnle : (G.neighborFinset v ∩ S).card ≤ q := by
    calc
      (G.neighborFinset v ∩ S).card ≤ (G.neighborFinset v).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  omega

/-- The unsigned exceptional support is invariant under shore complement. -/
theorem exceptionalSignedSupport_compl_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q : ℕ} (hreg : ∀ v, G.degree v = q) (S : Finset V) :
    exceptionalSignedSupport G (Sᶜ : Finset V) q =
      exceptionalSignedSupport G S q := by
  rw [exceptionalSignedSupport_eq_full_union_empty,
    exceptionalSignedSupport_eq_full_union_empty,
    fullLineCenters_compl_eq_emptyLineCenters G hreg S,
    emptyLineCenters_compl_eq_fullLineCenters G hreg S,
    Finset.union_comm]

/-- Final-scale specialization of the existing dyadic complement law. -/
theorem finalDyadicSupport_compl_shore_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    dyadicOccupancySupport G (Sᶜ : Finset V) j =
      dyadicOccupancySupport G S j := by
  apply dyadicOccupancySupport_compl G hreg S j hdiv
  refine ⟨1, ?_⟩
  rw [hqa, pow_succ]
  ring

end

end Erdos85

#print axioms Erdos85.fullLineCenters_compl_eq_emptyLineCenters
#print axioms Erdos85.emptyLineCenters_compl_eq_fullLineCenters
#print axioms Erdos85.exceptionalSignedSupport_compl_eq
#print axioms Erdos85.finalDyadicSupport_compl_shore_eq

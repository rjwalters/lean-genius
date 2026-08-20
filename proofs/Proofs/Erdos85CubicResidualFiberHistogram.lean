import Proofs.Erdos85EdgeIndexedServiceCubicCensus
import Proofs.Erdos85C4FreeRegularAdjacencyCube
import Proofs.Erdos85BoundedHistogramMoments

/-! # Cubic histograms on endpoint-incidence residual fibers -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def incidentEdgeFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (u : V) : Finset R.edgeFinset :=
  Finset.univ.filter fun b ↦ u ∈ b.1.toFinset

def incidentServiceNeighborFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) : Finset R.edgeFinset :=
  (incidentEdgeFiber R u).filter fun b ↦ Cedge.Adj b a

/-- Edges incident to `u` whose corresponding service vertices are not
adjacent to the target `a`; this includes `a` itself when `u` is an endpoint. -/
def cubicResidualFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) : Finset R.edgeFinset :=
  (incidentEdgeFiber R u).filter fun b ↦ ¬ Cedge.Adj b a

theorem incidentServiceNeighborFiber_eq_localLawFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) :
    incidentServiceNeighborFiber R Cedge u a =
      incidentServiceNeighborFinset R Cedge u a := by
  classical
  ext b
  simp [incidentServiceNeighborFiber, incidentEdgeFiber,
    incidentServiceNeighborFinset, SimpleGraph.mem_neighborFinset,
    Cedge.adj_comm, and_comm]

/-- Local service law in the residual-fiber vocabulary. -/
theorem internalEndpointNeighbor_card_add_incidentServiceNeighborFiber_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : V) (a : R.edgeFinset) :
    (internalEndpointNeighborFinset H R u a).card +
      (incidentServiceNeighborFiber R Cedge u a).card = 1 := by
  rw [incidentServiceNeighborFiber_eq_localLawFinset]
  exact edgeIndexedService_localLaw H R Cedge hservice u a

theorem incidentEdgeFiber_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (u : V) :
    (incidentEdgeFiber R u).card = R.degree u := by
  classical
  let eR : R.edgeFinset ↪ Sym2 V := Function.Embedding.subtype _
  have hmap : (incidentEdgeFiber R u).map eR = R.incidenceFinset u := by
    ext e
    simp only [incidentEdgeFiber, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [R.incidenceFinset_eq_filter]
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, by simpa [eR] using hb⟩
    · rintro ⟨he, hu⟩
      exact ⟨⟨e, he⟩, by simpa [eR] using hu, rfl⟩
  have hc := congrArg Finset.card hmap
  rw [Finset.card_map, R.card_incidenceFinset_eq_degree] at hc
  exact hc

theorem cubicResidualFiber_card_add_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) :
    (cubicResidualFiber R Cedge u a).card +
      (incidentServiceNeighborFiber R Cedge u a).card = R.degree u := by
  rw [cubicResidualFiber, incidentServiceNeighborFiber, add_comm,
    Finset.card_filter_add_card_filter_not, incidentEdgeFiber_card]

def residualFiberCubicWalkCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a b : R.edgeFinset) : ℕ :=
  Fintype.card {p : Cedge.Walk b a | p.length = 3}

def cubicResidualFiberHistogram
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) (t : ℕ) : ℕ :=
  boundedHistogram (cubicResidualFiber R Cedge u a)
    (residualFiberCubicWalkCount R Cedge a) t

theorem incidentServiceCubicWalkMass_eq_sum_incidentEdgeFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) :
    incidentServiceCubicWalkMass R Cedge u a =
      ∑ b ∈ incidentEdgeFiber R u,
        residualFiberCubicWalkCount R Cedge a b := by
  classical
  unfold incidentServiceCubicWalkMass incidentEdgeFiber
  rw [← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  rfl

theorem sixRegular_c4Free_residualFiberCubicWalkCount_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    {a b : R.edgeFinset} (hba : Cedge.Adj b a) :
    residualFiberCubicWalkCount R Cedge a b = 11 := by
  have hwalk := Cedge.adjMatrix_pow_apply_eq_card_walk
    (α := ℤ) 3 b a
  have hedge := c4Free_regular_adjMatrix_cube_apply_of_adj
    Cedge hfree 6 hreg hba
  change (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ *
    Cedge.adjMatrix ℤ) b a = 11 at hedge
  have hcast :
      ((residualFiberCubicWalkCount R Cedge a b : ℕ) : ℤ) = 11 := by
    rw [← hedge]
    simpa [residualFiberCubicWalkCount, pow_succ] using hwalk.symm
  exact_mod_cast hcast

/-- Removing the fixed service-neighbor entries (each equal to eleven) from
the incident cubic budget leaves the residual-fiber first moment. -/
theorem cubicResidualFiber_sum_eq_incidentMass_sub_eleven_neighborCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset) :
    (∑ b ∈ cubicResidualFiber R Cedge u a,
      residualFiberCubicWalkCount R Cedge a b) =
      incidentServiceCubicWalkMass R Cedge u a -
        11 * (incidentServiceNeighborFiber R Cedge u a).card := by
  classical
  let F := incidentEdgeFiber R u
  let f := residualFiberCubicWalkCount R Cedge a
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := F) (p := fun b ↦ Cedge.Adj b a) (f := f)
  have hneighbor :
      (∑ b ∈ incidentServiceNeighborFiber R Cedge u a, f b) =
        11 * (incidentServiceNeighborFiber R Cedge u a).card := by
    calc
      _ = ∑ _b ∈ incidentServiceNeighborFiber R Cedge u a, 11 := by
        apply Finset.sum_congr rfl
        intro b hb
        exact sixRegular_c4Free_residualFiberCubicWalkCount_of_adj
          R Cedge hfree hreg (Finset.mem_filter.mp hb).2
      _ = _ := by simp; ring
  change (∑ b ∈ incidentServiceNeighborFiber R Cedge u a, f b) +
      ∑ b ∈ cubicResidualFiber R Cedge u a, f b = ∑ b ∈ F, f b at hsplit
  have htotal : incidentServiceCubicWalkMass R Cedge u a =
      11 * (incidentServiceNeighborFiber R Cedge u a).card +
        ∑ b ∈ cubicResidualFiber R Cedge u a, f b := by
    calc
      _ = ∑ b ∈ F, f b :=
        incidentServiceCubicWalkMass_eq_sum_incidentEdgeFiber R Cedge u a
      _ = (∑ b ∈ incidentServiceNeighborFiber R Cedge u a, f b) +
          ∑ b ∈ cubicResidualFiber R Cedge u a, f b := hsplit.symm
      _ = _ := by rw [hneighbor]
  change incidentServiceCubicWalkMass R Cedge u a =
      11 * (incidentServiceNeighborFiber R Cedge u a).card +
        ∑ b ∈ cubicResidualFiber R Cedge u a,
          residualFiberCubicWalkCount R Cedge a b at htotal
  omega

/-- Complete seven-bin histogram interface for a cubic residual fiber. -/
theorem cubicResidualFiberHistogram_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    (u : V) (a : R.edgeFinset) :
    let c := cubicResidualFiberHistogram R Cedge u a
    (∑ t ∈ Finset.range 7, c t) =
        (cubicResidualFiber R Cedge u a).card ∧
      (∑ t ∈ Finset.range 7, t * c t) =
        incidentServiceCubicWalkMass R Cedge u a -
          11 * (incidentServiceNeighborFiber R Cedge u a).card ∧
      (∑ t ∈ Finset.range 7, t ^ 2 * c t) =
        ∑ b ∈ cubicResidualFiber R Cedge u a,
          (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  classical
  dsimp only
  let Q := cubicResidualFiber R Cedge u a
  let f := residualFiberCubicWalkCount R Cedge a
  let c := cubicResidualFiberHistogram R Cedge u a
  have hf : ∀ b ∈ Q, f b ≤ 6 := by
    intro b hb
    have hnab := (Finset.mem_filter.mp hb).2
    have hle := c4Free_regular_adjMatrix_cube_apply_of_not_adj_le
      Cedge hfree 6 hreg hnab
    have hwalk := Cedge.adjMatrix_pow_apply_eq_card_walk
      (α := ℤ) 3 b a
    have hcast : ((f b : ℕ) : ℤ) =
        (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ *
          Cedge.adjMatrix ℤ) b a := by
      simpa [f, residualFiberCubicWalkCount, pow_succ] using hwalk.symm
    omega
  obtain ⟨hzero, hone, htwo⟩ := boundedHistogram_moments_six Q f hf
  have hsum := cubicResidualFiber_sum_eq_incidentMass_sub_eleven_neighborCard
    R Cedge hfree hreg u a
  simpa [c, cubicResidualFiberHistogram, Q, f] using
    (show
      (∑ t ∈ Finset.range 7, boundedHistogram Q f t) = Q.card ∧
      (∑ t ∈ Finset.range 7, t * boundedHistogram Q f t) =
        incidentServiceCubicWalkMass R Cedge u a -
          11 * (incidentServiceNeighborFiber R Cedge u a).card ∧
      (∑ t ∈ Finset.range 7, t ^ 2 * boundedHistogram Q f t) =
        ∑ b ∈ Q, (f b) ^ 2 from ⟨hzero, hone.trans hsum, htwo⟩)

end

end Erdos85

#print axioms Erdos85.incidentEdgeFiber_card
#print axioms Erdos85.incidentServiceNeighborFiber_eq_localLawFinset
#print axioms
  Erdos85.internalEndpointNeighbor_card_add_incidentServiceNeighborFiber_card
#print axioms Erdos85.cubicResidualFiber_card_add_neighbor_card
#print axioms
  Erdos85.cubicResidualFiber_sum_eq_incidentMass_sub_eleven_neighborCard
#print axioms Erdos85.cubicResidualFiberHistogram_ledger

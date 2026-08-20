import Proofs.Erdos85CubicResidualFiberDoubleCount

/-! # Cubic residual-fiber histograms at arbitrary regular degree

This removes the degree-six constants from the residual-fiber first/second
moment interface.  In a `d`-regular C4-free service graph, adjacent cubic
entries are `2d-1`, nonadjacent entries are at most `d`, and hence every
residual endpoint fiber has a complete histogram on `0, ..., d`.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- All weighted moments of a bounded natural-valued function are recovered
from its finite histogram. -/
theorem boundedHistogram_weighted_sum
    {α : Type*} [DecidableEq α]
    (T : Finset α) (f : α → ℕ) (B : ℕ)
    (hf : ∀ x ∈ T, f x ≤ B) (w : ℕ → ℕ) :
    (∑ t ∈ Finset.range (B + 1), w t * boundedHistogram T f t) =
      ∑ x ∈ T, w (f x) := by
  classical
  simp_rw [boundedHistogram, Finset.card_eq_sum_ones, Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem : f x ∈ Finset.range (B + 1) := by
    simp only [Finset.mem_range]
    have hfx := hf x hx
    omega
  rw [Finset.sum_eq_single (f x)]
  · simp
  · intro t ht hne
    rw [if_neg (fun heq ↦ hne heq.symm)]
  · exact fun hnot ↦ (hnot hmem).elim

/-- Zeroth, first and second moments of a histogram with arbitrary bound. -/
theorem boundedHistogram_moments
    {α : Type*} [DecidableEq α]
    (T : Finset α) (f : α → ℕ) (B : ℕ)
    (hf : ∀ x ∈ T, f x ≤ B) :
    (∑ t ∈ Finset.range (B + 1), boundedHistogram T f t) = T.card ∧
      (∑ t ∈ Finset.range (B + 1), t * boundedHistogram T f t) =
        ∑ x ∈ T, f x ∧
      (∑ t ∈ Finset.range (B + 1), t ^ 2 * boundedHistogram T f t) =
        ∑ x ∈ T, (f x) ^ 2 := by
  have hzero := boundedHistogram_weighted_sum T f B hf (fun _ ↦ 1)
  have hone := boundedHistogram_weighted_sum T f B hf id
  have htwo := boundedHistogram_weighted_sum T f B hf (fun t ↦ t ^ 2)
  simpa using And.intro hzero (And.intro hone htwo)

/-- The cubic walk count on an adjacent service pair is `2d-1`. -/
theorem regular_c4Free_residualFiberCubicWalkCount_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge) (d : ℕ)
    (hreg : ∀ b, Cedge.degree b = d)
    {a b : R.edgeFinset} (hba : Cedge.Adj b a) :
    residualFiberCubicWalkCount R Cedge a b = 2 * d - 1 := by
  have hwalk := Cedge.adjMatrix_pow_apply_eq_card_walk
    (α := ℤ) 3 b a
  have hedge := c4Free_regular_adjMatrix_cube_apply_of_adj
    Cedge hfree d hreg hba
  have hcast :
      ((residualFiberCubicWalkCount R Cedge a b : ℕ) : ℤ) =
        2 * (d : ℤ) - 1 := by
    rw [← hedge]
    simpa [residualFiberCubicWalkCount, pow_succ] using hwalk.symm
  have hd : 1 ≤ d := by
    have ha : a ∈ Cedge.neighborFinset b :=
      (Cedge.mem_neighborFinset b a).mpr hba
    have hbpos : 0 < (Cedge.neighborFinset b).card :=
      Finset.card_pos.mpr ⟨a, ha⟩
    rw [Cedge.card_neighborFinset_eq_degree, hreg b] at hbpos
    omega
  have hcast' :
      ((residualFiberCubicWalkCount R Cedge a b : ℕ) : ℤ) =
        ((2 * d - 1 : ℕ) : ℤ) := by
    rw [hcast]
    omega
  exact_mod_cast hcast'

/-- Removing the fixed adjacent entries `2d-1` leaves the residual-fiber
first moment, at arbitrary regular degree. -/
theorem regular_c4Free_cubicResidualFiber_sum_eq_incidentMass_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge) (d : ℕ)
    (hreg : ∀ b, Cedge.degree b = d)
    (u : V) (a : R.edgeFinset) :
    (∑ b ∈ cubicResidualFiber R Cedge u a,
      residualFiberCubicWalkCount R Cedge a b) =
      incidentServiceCubicWalkMass R Cedge u a -
        (2 * d - 1) * (incidentServiceNeighborFiber R Cedge u a).card := by
  classical
  let F := incidentEdgeFiber R u
  let f := residualFiberCubicWalkCount R Cedge a
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (s := F) (p := fun b ↦ Cedge.Adj b a) (f := f)
  have hneighbor :
      (∑ b ∈ incidentServiceNeighborFiber R Cedge u a, f b) =
        (2 * d - 1) * (incidentServiceNeighborFiber R Cedge u a).card := by
    calc
      _ = ∑ _b ∈ incidentServiceNeighborFiber R Cedge u a, (2 * d - 1) := by
        apply Finset.sum_congr rfl
        intro b hb
        exact regular_c4Free_residualFiberCubicWalkCount_of_adj
          R Cedge hfree d hreg (Finset.mem_filter.mp hb).2
      _ = _ := by simp; ring
  change (∑ b ∈ incidentServiceNeighborFiber R Cedge u a, f b) +
      ∑ b ∈ cubicResidualFiber R Cedge u a, f b = ∑ b ∈ F, f b at hsplit
  have htotal : incidentServiceCubicWalkMass R Cedge u a =
      (2 * d - 1) * (incidentServiceNeighborFiber R Cedge u a).card +
        ∑ b ∈ cubicResidualFiber R Cedge u a, f b := by
    calc
      _ = ∑ b ∈ F, f b :=
        incidentServiceCubicWalkMass_eq_sum_incidentEdgeFiber R Cedge u a
      _ = (∑ b ∈ incidentServiceNeighborFiber R Cedge u a, f b) +
          ∑ b ∈ cubicResidualFiber R Cedge u a, f b := hsplit.symm
      _ = _ := by rw [hneighbor]
  change (∑ b ∈ cubicResidualFiber R Cedge u a, f b) = _
  exact Nat.eq_sub_of_add_eq (by simpa [Nat.add_comm] using htotal.symm)

/-- Complete arbitrary-degree histogram interface for a cubic residual fiber. -/
theorem regular_c4Free_cubicResidualFiberHistogram_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge) (d : ℕ)
    (hreg : ∀ b, Cedge.degree b = d)
    (u : V) (a : R.edgeFinset) :
    let c := cubicResidualFiberHistogram R Cedge u a
    (∑ t ∈ Finset.range (d + 1), c t) =
        (cubicResidualFiber R Cedge u a).card ∧
      (∑ t ∈ Finset.range (d + 1), t * c t) =
        incidentServiceCubicWalkMass R Cedge u a -
          (2 * d - 1) * (incidentServiceNeighborFiber R Cedge u a).card ∧
      (∑ t ∈ Finset.range (d + 1), t ^ 2 * c t) =
        ∑ b ∈ cubicResidualFiber R Cedge u a,
          (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  classical
  dsimp only
  let Q := cubicResidualFiber R Cedge u a
  let f := residualFiberCubicWalkCount R Cedge a
  let c := cubicResidualFiberHistogram R Cedge u a
  have hf : ∀ b ∈ Q, f b ≤ d := by
    intro b hb
    have hnab := (Finset.mem_filter.mp hb).2
    have hle := c4Free_regular_adjMatrix_cube_apply_of_not_adj_le
      Cedge hfree d hreg hnab
    have hwalk := Cedge.adjMatrix_pow_apply_eq_card_walk
      (α := ℤ) 3 b a
    have hcast : ((f b : ℕ) : ℤ) =
        (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ *
          Cedge.adjMatrix ℤ) b a := by
      simpa [f, residualFiberCubicWalkCount, pow_succ] using hwalk.symm
    omega
  obtain ⟨hzero, hone, htwo⟩ := boundedHistogram_moments Q f d hf
  have hsum := regular_c4Free_cubicResidualFiber_sum_eq_incidentMass_sub
    R Cedge hfree d hreg u a
  simpa [c, cubicResidualFiberHistogram, Q, f] using
    (show
      (∑ t ∈ Finset.range (d + 1), boundedHistogram Q f t) = Q.card ∧
      (∑ t ∈ Finset.range (d + 1), t * boundedHistogram Q f t) =
        incidentServiceCubicWalkMass R Cedge u a -
          (2 * d - 1) * (incidentServiceNeighborFiber R Cedge u a).card ∧
      (∑ t ∈ Finset.range (d + 1), t ^ 2 * boundedHistogram Q f t) =
        ∑ b ∈ Q, (f b) ^ 2 from ⟨hzero, hone.trans hsum, htwo⟩)

/-- The established seven-bin degree-six ledger is recovered verbatim. -/
theorem sixRegular_cubicResidualFiberHistogram_ledger_from_general
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
  simpa using regular_c4Free_cubicResidualFiberHistogram_ledger
    R Cedge hfree 6 hreg u a

end

end Erdos85

#print axioms Erdos85.boundedHistogram_weighted_sum
#print axioms Erdos85.boundedHistogram_moments
#print axioms Erdos85.regular_c4Free_residualFiberCubicWalkCount_of_adj
#print axioms Erdos85.regular_c4Free_cubicResidualFiber_sum_eq_incidentMass_sub
#print axioms Erdos85.regular_c4Free_cubicResidualFiberHistogram_ledger
#print axioms Erdos85.sixRegular_cubicResidualFiberHistogram_ledger_from_general

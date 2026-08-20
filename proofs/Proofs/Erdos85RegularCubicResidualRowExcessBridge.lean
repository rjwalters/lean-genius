import Proofs.Erdos85CubicResidualRowExcessBridge
import Proofs.Erdos85RegularCubicRowExcessLedger

/-! # Arbitrary-degree residual square mass versus row excess

The edge-indexed residual sector is the diagonal together with all
nonneighbors.  This file identifies its square mass with the arbitrary-center
row-excess ledger, without fixing degree, order, or histogram center.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Exact arbitrary-parameter scalar bridge for the residual cubic sector. -/
theorem regular_c4Free_cubicResidualEdge_squareMass_eq_baseline_add_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge) (d : ℕ)
    (hreg : ∀ b, Cedge.degree b = d) (c : ℤ)
    (a : R.edgeFinset) :
    let A3 := Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ
    let Q := cubicNonneighborFinset Cedge a
    ((∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2 : ℕ) : ℤ) =
      (A3 a a) ^ 2 +
      (2 * c + 1) *
        ((d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a) -
      c * (c + 1) * (Q.card : ℤ) +
      ∑ b ∈ Q, (A3 a b - c) * (A3 a b - (c + 1)) := by
  classical
  dsimp only
  let A3 := Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ
  let Q := cubicNonneighborFinset Cedge a
  have haQ : a ∉ Q := by simp [Q, cubicNonneighborFinset]
  have hentry (b : R.edgeFinset) :
      ((residualFiberCubicWalkCount R Cedge a b : ℕ) : ℤ) = A3 a b :=
    residualFiberCubicWalkCount_cast_eq_cube_apply R Cedge a b
  have hmass := c4Free_regular_cubicNonneighborMass_eq
    Cedge hfree d hreg a
  change (∑ b ∈ Q, A3 a b) =
    (d : ℤ) ^ 3 - (d : ℤ) * (2 * (d : ℤ) - 1) - A3 a a at hmass
  have hsquare : (∑ b ∈ Q, (A3 a b) ^ 2) =
      (2 * c + 1) * (∑ b ∈ Q, A3 a b) -
        c * (c + 1) * (Q.card : ℤ) +
        ∑ b ∈ Q, (A3 a b - c) * (A3 a b - (c + 1)) := by
    calc
      _ = ∑ b ∈ Q,
          ((2 * c + 1) * A3 a b - c * (c + 1) +
            (A3 a b - c) * (A3 a b - (c + 1))) := by
              apply Finset.sum_congr rfl
              intro b _
              ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp
        rw [Finset.mul_sum]
        ring
  calc
    ((∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2 : ℕ) : ℤ) =
        (A3 a a) ^ 2 + ∑ b ∈ Q, (A3 a b) ^ 2 := by
      rw [cubicResidualEdgeFinset_eq_insert_cubicNonneighborFinset,
        Finset.sum_insert haQ]
      push_cast
      rw [hentry a]
      congr 1
      apply Finset.sum_congr rfl
      intro b hb
      rw [hentry b]
    _ = _ := by
      rw [hsquare, hmass]
      simp only [A3, Q]
      ring

/-- At degree six, order 48 and center three, the arbitrary bridge recovers
the established constant `546` and traditional row-excess expression. -/
theorem sixRegular_fortyEight_cubicResidualEdge_squareMass_of_general
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hcard : Fintype.card R.edgeFinset = 48)
    (hreg : ∀ b, Cedge.degree b = 6)
    (a : R.edgeFinset) :
    ((∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2 : ℕ) : ℤ) =
      546 + cubicRowHistogramExcess Cedge a := by
  have hgeneral :=
    regular_c4Free_cubicResidualEdge_squareMass_eq_baseline_add_excess
      R Cedge hfree 6 hreg 3 a
  have hq := sixRegular_fortyEight_cubicNonneighborFinset_card
    Cedge hcard hreg a
  rw [hgeneral]
  simp only [cubicRowHistogramExcess]
  rw [hq]
  norm_num
  ring

end

end Erdos85

#print axioms
  Erdos85.regular_c4Free_cubicResidualEdge_squareMass_eq_baseline_add_excess
#print axioms
  Erdos85.sixRegular_fortyEight_cubicResidualEdge_squareMass_of_general

import Proofs.Erdos85CrossCubicFiberBounds
import Proofs.Erdos85CubicTraceHistogramExcess

/-! # Residual cubic square mass versus row histogram excess -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def cubicRowHistogramExcess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (a : V) : ℤ :=
  let A3 := G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ
  (A3 a a) ^ 2 - 7 * A3 a a + 12 +
    ∑ b ∈ cubicNonneighborFinset G a,
      (A3 a b - 3) * (A3 a b - 4)

theorem cubicResidualEdgeFinset_eq_insert_cubicNonneighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) :
    cubicResidualEdgeFinset R Cedge a =
      insert a (cubicNonneighborFinset Cedge a) := by
  classical
  ext b
  by_cases hba : b = a
  · subst b
    simp [cubicResidualEdgeFinset, cubicNonneighborFinset]
  · simp [cubicResidualEdgeFinset, cubicNonneighborFinset, hba,
      Cedge.adj_comm]

theorem residualFiberCubicWalkCount_cast_eq_cube_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a b : R.edgeFinset) :
    ((residualFiberCubicWalkCount R Cedge a b : ℕ) : ℤ) =
      (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ) a b := by
  change ((Fintype.card {p : Cedge.Walk b a | p.length = 3} : ℕ) : ℤ) = _
  have hwalk := Cedge.adjMatrix_pow_apply_eq_card_walk (α := ℤ) 3 b a
  have hbase : (Cedge.adjMatrix ℤ).IsSymm :=
    SimpleGraph.isSymm_adjMatrix Cedge
  have hsymm : (Cedge.adjMatrix ℤ ^ 3).IsSymm := hbase.pow 3
  have hab : (Cedge.adjMatrix ℤ ^ 3) b a =
      (Cedge.adjMatrix ℤ ^ 3) a b :=
    congrFun (congrFun hsymm.eq a) b
  calc
    _ = (Cedge.adjMatrix ℤ ^ 3) b a := hwalk.symm
    _ = (Cedge.adjMatrix ℤ ^ 3) a b := hab
    _ = _ := by simp [pow_succ]

/-- Exact scalar bridge: the residual sector includes the diagonal, and its
square mass is `546` plus the standard row histogram excess. -/
theorem cubicResidualEdge_squareMass_eq_546_add_rowExcess
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
  classical
  let A3 := Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ
  let Q := cubicNonneighborFinset Cedge a
  have haQ : a ∉ Q := by simp [Q, cubicNonneighborFinset]
  have hentry (b : R.edgeFinset) :
      ((residualFiberCubicWalkCount R Cedge a b : ℕ) : ℤ) = A3 a b :=
    residualFiberCubicWalkCount_cast_eq_cube_apply R Cedge a b
  have hcardQ := sixRegular_fortyEight_cubicNonneighborFinset_card
    Cedge hcard hreg a
  have hmass := sixRegular_fortyEight_cubicNonneighborMass_eq
    Cedge hfree hreg a
  have hsquare := fortyOne_sum_sq_eq_baseline_add_excess
    Q (fun b ↦ A3 a b) (A3 a a) hcardQ hmass
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
    _ = 546 + cubicRowHistogramExcess Cedge a := by
      rw [hsquare]
      simp only [cubicRowHistogramExcess]
      dsimp only [A3, Q]
      ring

/-- In particular, residual square mass at least `550` forces at least four
units of row histogram excess. -/
theorem cubicRowHistogramExcess_ge_four_of_residual_squareMass_ge_550
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hcard : Fintype.card R.edgeFinset = 48)
    (hreg : ∀ b, Cedge.degree b = 6)
    (a : R.edgeFinset)
    (hlower : 550 ≤ ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) :
    4 ≤ cubicRowHistogramExcess Cedge a := by
  have heq := cubicResidualEdge_squareMass_eq_546_add_rowExcess
    R Cedge hfree hcard hreg a
  omega

end

end Erdos85

#print axioms Erdos85.cubicResidualEdge_squareMass_eq_546_add_rowExcess
#print axioms
  Erdos85.cubicRowHistogramExcess_ge_four_of_residual_squareMass_ge_550

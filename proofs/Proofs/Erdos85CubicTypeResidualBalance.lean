import Proofs.Erdos85EdgeIndexedServiceCubicTypeMass
import Proofs.Erdos85C4FreeRegularAdjacencyCube
import Proofs.Erdos85EdgeIndexedServiceShoreTypeCounts

/-! # Residual cubic mass by shore type -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def residualShoreTypeCubicWalkMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (t : ℕ) (a : R.edgeFinset) : ℕ :=
  ∑ b ∈ (shoreTypeEdgeFinset R S t).filter (fun b => ¬ Cedge.Adj a b),
    serviceCubicWalkCount Cedge b a

/-- On an edge of a six-regular C4-free service graph the cubic walk count
is `2·6-1=11`. -/
theorem serviceCubicWalkCount_eq_eleven_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    {R : SimpleGraph V} [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    {a b : R.edgeFinset} (hab : Cedge.Adj a b) :
    serviceCubicWalkCount Cedge b a = 11 := by
  unfold serviceCubicWalkCount
  have hwalk := Cedge.adjMatrix_pow_apply_eq_card_walk
    (α := ℤ) 3 b a
  have hcube := c4Free_regular_adjMatrix_cube_apply_of_adj
    Cedge hfree 6 hreg (a := b) (b := a) hab.symm
  have hentry :
      (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ) b a =
        (Fintype.card {p : Cedge.Walk b a | p.length = 3} : ℤ) := by
    simpa [pow_succ, Matrix.mul_assoc] using hwalk
  have hcube' :
      (Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ * Cedge.adjMatrix ℤ) b a = 11 := by
    norm_num at hcube ⊢
    exact hcube
  have hcast :
      (Fintype.card {p : Cedge.Walk b a | p.length = 3} : ℤ) = 11 :=
    hentry.symm.trans hcube'
  have hnat := congrArg Int.toNat hcast
  simpa using hnat

/-- Total type mass splits into residual (diagonal and nonneighbors) plus
eleven times the number of adjacent edges of that shore type. -/
theorem shoreTypeCubicWalkMass_eq_residual_add_eleven_mul_neighborCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    (S : Finset V) (t : ℕ) (a : R.edgeFinset) :
    shoreTypeCubicWalkMass R Cedge S t a =
      residualShoreTypeCubicWalkMass R Cedge S t a +
        11 * serviceNeighborShoreTypeCount R Cedge a S t := by
  classical
  let T := shoreTypeEdgeFinset R S t
  let f := fun b : R.edgeFinset => serviceCubicWalkCount Cedge b a
  have hsplit := Finset.sum_filter_add_sum_filter_not T
    (fun b => Cedge.Adj a b) f
  have hadj : (∑ b ∈ T.filter (fun b => Cedge.Adj a b), f b) =
      11 * serviceNeighborShoreTypeCount R Cedge a S t := by
    have hset : T.filter (fun b => Cedge.Adj a b) =
        (Cedge.neighborFinset a).filter
          (fun b => (b.1.toFinset ∩ S).card = t) := by
      ext b
      simp [T, shoreTypeEdgeFinset, SimpleGraph.mem_neighborFinset, and_comm]
    rw [hset]
    calc
      (∑ b ∈ (Cedge.neighborFinset a).filter
          (fun b => (b.1.toFinset ∩ S).card = t), f b) =
          ∑ _b ∈ (Cedge.neighborFinset a).filter
            (fun b => (b.1.toFinset ∩ S).card = t), 11 := by
              apply Finset.sum_congr rfl
              intro b hb
              apply serviceCubicWalkCount_eq_eleven_of_adj Cedge hfree hreg
              exact (Cedge.mem_neighborFinset a b).mp
                ((Finset.mem_filter.mp hb).1)
      _ = 11 * serviceNeighborShoreTypeCount R Cedge a S t := by
        simp [serviceNeighborShoreTypeCount, mul_comm]
  change (∑ b ∈ T, f b) =
    (∑ b ∈ T.filter (fun b => ¬ Cedge.Adj a b), f b) + _
  rw [← hadj]
  omega

/-- Arithmetic cancellation behind the h305 residual identity. -/
theorem cubicTypeResidual_two_eq_zero_add_fourteen
    (S0 S2 Q0 Q2 c0 c2 : ℕ)
    (hmass : S0 = S2 + 8)
    (hprofile : c0 = c2 + 2)
    (hsplit0 : S0 = Q0 + 11 * c0)
    (hsplit2 : S2 = Q2 + 11 * c2) :
    Q2 = Q0 + 14 := by
  omega

/-- Graph-facing form: the antipodal cubic shore balance and the universal
same-shore neighbor-profile difference force residual type-two mass to exceed
residual type-zero mass by exactly fourteen. -/
theorem residualShoreTypeCubicWalkMass_two_eq_zero_add_fourteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    (S : Finset V) (a : R.edgeFinset)
    (hmass : shoreTypeCubicWalkMass R Cedge S 0 a =
      shoreTypeCubicWalkMass R Cedge S 2 a + 8)
    (hprofile : serviceNeighborShoreTypeCount R Cedge a S 0 =
      serviceNeighborShoreTypeCount R Cedge a S 2 + 2) :
    residualShoreTypeCubicWalkMass R Cedge S 2 a =
      residualShoreTypeCubicWalkMass R Cedge S 0 a + 14 := by
  apply cubicTypeResidual_two_eq_zero_add_fourteen
    (shoreTypeCubicWalkMass R Cedge S 0 a)
    (shoreTypeCubicWalkMass R Cedge S 2 a)
    (residualShoreTypeCubicWalkMass R Cedge S 0 a)
    (residualShoreTypeCubicWalkMass R Cedge S 2 a)
    (serviceNeighborShoreTypeCount R Cedge a S 0)
    (serviceNeighborShoreTypeCount R Cedge a S 2)
    hmass hprofile
  · exact shoreTypeCubicWalkMass_eq_residual_add_eleven_mul_neighborCount
      R Cedge hfree hreg S 0 a
  · exact shoreTypeCubicWalkMass_eq_residual_add_eleven_mul_neighborCount
      R Cedge hfree hreg S 2 a

end

end Erdos85

#print axioms Erdos85.serviceCubicWalkCount_eq_eleven_of_adj
#print axioms
  Erdos85.residualShoreTypeCubicWalkMass_two_eq_zero_add_fourteen

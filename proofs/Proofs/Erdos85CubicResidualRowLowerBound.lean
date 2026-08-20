import Proofs.Erdos85CubicResidualFiberDoubleCount

/-! # Cubic residual row lower bounds from coordinate partitions -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_eq_sum_three_of_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (X Y Z : Finset V) (F : V → ℕ)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (hcover : X ∪ Y ∪ Z = Finset.univ) :
    (∑ u : V, F u) =
      (∑ u ∈ X, F u) + (∑ u ∈ Y, F u) + (∑ u ∈ Z, F u) := by
  have hXYZ : Disjoint (X ∪ Y) Z := Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩
  calc
    (∑ u : V, F u) = ∑ u ∈ X ∪ Y ∪ Z, F u := by rw [hcover]
    _ = (∑ u ∈ X ∪ Y, F u) + ∑ u ∈ Z, F u := by
      rw [Finset.sum_union hXYZ]
    _ = ((∑ u ∈ X, F u) + ∑ u ∈ Y, F u) +
        ∑ u ∈ Z, F u := by rw [Finset.sum_union hXY]

/-- A `4/4/8` coordinate partition with local lower bounds `105/52/59`
has total endpoint-fiber square mass at least `1100`. -/
theorem sum_ge_1100_of_four_four_eight_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (X25 X16 X17 : Finset V) (F : V → ℕ)
    (h25card : X25.card = 4) (h16card : X16.card = 4)
    (h17card : X17.card = 8)
    (h2516 : Disjoint X25 X16) (h2517 : Disjoint X25 X17)
    (h1617 : Disjoint X16 X17)
    (hcover : X25 ∪ X16 ∪ X17 = Finset.univ)
    (h25 : ∀ u ∈ X25, 105 ≤ F u)
    (h16 : ∀ u ∈ X16, 52 ≤ F u)
    (h17 : ∀ u ∈ X17, 59 ≤ F u) :
    1100 ≤ ∑ u : V, F u := by
  have hsum25 : 4 * 105 ≤ ∑ u ∈ X25, F u := by
    calc
      4 * 105 = ∑ _u ∈ X25, 105 := by simp [h25card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h25 u hu
  have hsum16 : 4 * 52 ≤ ∑ u ∈ X16, F u := by
    calc
      4 * 52 = ∑ _u ∈ X16, 52 := by simp [h16card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h16 u hu
  have hsum17 : 8 * 59 ≤ ∑ u ∈ X17, F u := by
    calc
      8 * 59 = ∑ _u ∈ X17, 59 := by simp [h17card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h17 u hu
  rw [sum_eq_sum_three_of_partition X25 X16 X17 F
    h2516 h2517 h1617 hcover]
  omega

/-- A `4/12` coordinate partition with local lower bounds `96/59` has
total endpoint-fiber square mass at least `1092`. -/
theorem sum_ge_1092_of_four_twelve_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (X24 X17 : Finset V) (F : V → ℕ)
    (h24card : X24.card = 4) (h17card : X17.card = 12)
    (hdisj : Disjoint X24 X17) (hcover : X24 ∪ X17 = Finset.univ)
    (h24 : ∀ u ∈ X24, 96 ≤ F u)
    (h17 : ∀ u ∈ X17, 59 ≤ F u) :
    1092 ≤ ∑ u : V, F u := by
  have hsum24 : 4 * 96 ≤ ∑ u ∈ X24, F u := by
    calc
      4 * 96 = ∑ _u ∈ X24, 96 := by simp [h24card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h24 u hu
  have hsum17 : 12 * 59 ≤ ∑ u ∈ X17, F u := by
    calc
      12 * 59 = ∑ _u ∈ X17, 59 := by simp [h17card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h17 u hu
  calc
    1092 ≤ (∑ u ∈ X24, F u) + ∑ u ∈ X17, F u := by omega
    _ = ∑ u ∈ X24 ∪ X17, F u := (Finset.sum_union hdisj).symm
    _ = ∑ u : V, F u := by rw [hcover]

/-- Cross-target row socket: once the sixteen coordinates are partitioned
into the four `25`, four `16`, and eight `17` fibers, their sharp local
bounds imply residual edge square mass at least `550`. -/
theorem cubicResidualEdge_squareMass_ge_550_of_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (X25 X16 X17 : Finset V)
    (h25card : X25.card = 4) (h16card : X16.card = 4)
    (h17card : X17.card = 8)
    (h2516 : Disjoint X25 X16) (h2517 : Disjoint X25 X17)
    (h1617 : Disjoint X16 X17)
    (hcover : X25 ∪ X16 ∪ X17 = Finset.univ)
    (h25 : ∀ u ∈ X25, 105 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2)
    (h16 : ∀ u ∈ X16, 52 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2)
    (h17 : ∀ u ∈ X17, 59 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) :
    550 ≤ ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let F := fun u : V ↦ ∑ b ∈ cubicResidualFiber R Cedge u a,
    (residualFiberCubicWalkCount R Cedge a b) ^ 2
  have htotal : 1100 ≤ ∑ u : V, F u :=
    sum_ge_1100_of_four_four_eight_partition X25 X16 X17 F
      h25card h16card h17card h2516 h2517 h1617 hcover h25 h16 h17
  have hdouble :=
    sum_residualFiberCubicWalkCount_sq_eq_two_mul_residualEdge_sq R Cedge a
  change (∑ u : V, F u) = 2 * ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
    (residualFiberCubicWalkCount R Cedge a b) ^ 2 at hdouble
  omega

/-- Antipodal-target row socket: the `4/12` local partition implies residual
edge square mass at least `546`. -/
theorem cubicResidualEdge_squareMass_ge_546_of_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (a : R.edgeFinset) (X24 X17 : Finset V)
    (h24card : X24.card = 4) (h17card : X17.card = 12)
    (hdisj : Disjoint X24 X17) (hcover : X24 ∪ X17 = Finset.univ)
    (h24 : ∀ u ∈ X24, 96 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2)
    (h17 : ∀ u ∈ X17, 59 ≤ ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) :
    546 ≤ ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let F := fun u : V ↦ ∑ b ∈ cubicResidualFiber R Cedge u a,
    (residualFiberCubicWalkCount R Cedge a b) ^ 2
  have htotal : 1092 ≤ ∑ u : V, F u :=
    sum_ge_1092_of_four_twelve_partition X24 X17 F
      h24card h17card hdisj hcover h24 h17
  have hdouble :=
    sum_residualFiberCubicWalkCount_sq_eq_two_mul_residualEdge_sq R Cedge a
  change (∑ u : V, F u) = 2 * ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
    (residualFiberCubicWalkCount R Cedge a b) ^ 2 at hdouble
  omega

end

end Erdos85

#print axioms Erdos85.sum_ge_1100_of_four_four_eight_partition
#print axioms Erdos85.sum_ge_1092_of_four_twelve_partition
#print axioms Erdos85.cubicResidualEdge_squareMass_ge_550_of_partition
#print axioms Erdos85.cubicResidualEdge_squareMass_ge_546_of_partition

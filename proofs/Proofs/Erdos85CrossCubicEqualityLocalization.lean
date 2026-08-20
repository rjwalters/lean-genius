import Proofs.Erdos85CubicResidualRowLowerBound

/-! # Equality localization for the cross cubic row bound -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem nat_eq_lowerBound_of_sum_eq_card_mul
    {V : Type*} [DecidableEq V] (S : Finset V) (F : V → ℕ) (c : ℕ)
    (hlower : ∀ x ∈ S, c ≤ F x)
    (hsum : ∑ x ∈ S, F x = S.card * c)
    {y : V} (hy : y ∈ S) : F y = c := by
  apply Nat.le_antisymm
  · by_contra hnot
    have hylt : c < F y := Nat.lt_of_not_ge hnot
    have hlt : ∑ _x ∈ S, c < ∑ x ∈ S, F x := by
      apply Finset.sum_lt_sum
      · exact hlower
      · exact ⟨y, hy, hylt⟩
    simp [hsum] at hlt
  · exact hlower y hy

/-- Equality in the `4/4/8` aggregate bound forces equality at every local
fiber; no excess can be hidden in a different coordinate class. -/
theorem four_four_eight_partition_eq_minima
    {V : Type*} [Fintype V] [DecidableEq V]
    (X25 X16 X17 : Finset V) (F : V → ℕ)
    (h25card : X25.card = 4) (h16card : X16.card = 4)
    (h17card : X17.card = 8)
    (h2516 : Disjoint X25 X16) (h2517 : Disjoint X25 X17)
    (h1617 : Disjoint X16 X17)
    (hcover : X25 ∪ X16 ∪ X17 = Finset.univ)
    (h25 : ∀ u ∈ X25, 105 ≤ F u)
    (h16 : ∀ u ∈ X16, 52 ≤ F u)
    (h17 : ∀ u ∈ X17, 59 ≤ F u)
    (htotal : ∑ u : V, F u = 1100) :
    (∀ u ∈ X25, F u = 105) ∧
      (∀ u ∈ X16, F u = 52) ∧
      (∀ u ∈ X17, F u = 59) := by
  have hXYZ : Disjoint (X25 ∪ X16) X17 :=
    Finset.disjoint_union_left.mpr ⟨h2517, h1617⟩
  have hdecomp : (∑ u : V, F u) =
      (∑ u ∈ X25, F u) + (∑ u ∈ X16, F u) +
        ∑ u ∈ X17, F u := by
    calc
      (∑ u : V, F u) = ∑ u ∈ X25 ∪ X16 ∪ X17, F u := by
        rw [hcover]
      _ = (∑ u ∈ X25 ∪ X16, F u) + ∑ u ∈ X17, F u := by
        rw [Finset.sum_union hXYZ]
      _ = ((∑ u ∈ X25, F u) + ∑ u ∈ X16, F u) +
          ∑ u ∈ X17, F u := by rw [Finset.sum_union h2516]
  have hl25 : 420 ≤ ∑ u ∈ X25, F u := by
    calc
      420 = ∑ _u ∈ X25, 105 := by simp [h25card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h25 u hu
  have hl16 : 208 ≤ ∑ u ∈ X16, F u := by
    calc
      208 = ∑ _u ∈ X16, 52 := by simp [h16card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h16 u hu
  have hl17 : 472 ≤ ∑ u ∈ X17, F u := by
    calc
      472 = ∑ _u ∈ X17, 59 := by simp [h17card]
      _ ≤ _ := Finset.sum_le_sum fun u hu ↦ h17 u hu
  have hs25 : ∑ u ∈ X25, F u = X25.card * 105 := by
    rw [h25card]
    omega
  have hs16 : ∑ u ∈ X16, F u = X16.card * 52 := by
    rw [h16card]
    omega
  have hs17 : ∑ u ∈ X17, F u = X17.card * 59 := by
    rw [h17card]
    omega
  exact ⟨fun u hu ↦ nat_eq_lowerBound_of_sum_eq_card_mul
      X25 F 105 h25 hs25 hu,
    fun u hu ↦ nat_eq_lowerBound_of_sum_eq_card_mul
      X16 F 52 h16 hs16 hu,
    fun u hu ↦ nat_eq_lowerBound_of_sum_eq_card_mul
      X17 F 59 h17 hs17 hu⟩

/-- Residual-edge square mass `550` is the equality case of every local
fiber bound in the cross `4/4/8` partition. -/
theorem cubicResidualEdge_squareMass_eq_550_localizes
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
      (residualFiberCubicWalkCount R Cedge a b) ^ 2)
    (hmass : ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 = 550) :
    (∀ u ∈ X25, ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 = 105) ∧
    (∀ u ∈ X16, ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 = 52) ∧
    (∀ u ∈ X17, ∑ b ∈ cubicResidualFiber R Cedge u a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 = 59) := by
  let F := fun u : V ↦ ∑ b ∈ cubicResidualFiber R Cedge u a,
    (residualFiberCubicWalkCount R Cedge a b) ^ 2
  have hdouble :=
    sum_residualFiberCubicWalkCount_sq_eq_two_mul_residualEdge_sq R Cedge a
  have htotal : ∑ u : V, F u = 1100 := by
    change (∑ u : V, F u) = 2 * ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 at hdouble
    omega
  exact four_four_eight_partition_eq_minima X25 X16 X17 F
    h25card h16card h17card h2516 h2517 h1617 hcover h25 h16 h17 htotal

end

end Erdos85

#print axioms Erdos85.four_four_eight_partition_eq_minima
#print axioms Erdos85.cubicResidualEdge_squareMass_eq_550_localizes

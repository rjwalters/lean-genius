import Proofs.Erdos85BranchDeficitSymmetry

/-!
# Positive-spike location balance

Double-counting the original-graph edges between the two shores converts the
two signed positive-spike profiles into the exact location equation (B15).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Subtraction-free arithmetic form of (B15). -/
theorem positiveSpike_location_balance_of_cross_incidence
    (q a b xCard yCard cross rX cX kY : ℕ)
    (hab : a + b = q - 1)
    (hxCard : xCard = q * (a + 1) - 2)
    (hyCard : yCard = q * b - 1)
    (hxLarge : 2 ≤ q * (a + 1))
    (hyLarge : 1 ≤ q * b)
    (hX : cross + rX = b * xCard + cX)
    (hY : cross + kY = (a + 1) * yCard) :
    kY + cX + a + 1 = rX + 2 * b := by
  have hqpos : 0 < q := by nlinarith
  have hq : q = a + b + 1 := by omega
  have hxAdd : xCard + 2 = q * (a + 1) := by omega
  have hyAdd : yCard + 1 = q * b := by omega
  nlinarith

private theorem sum_indicator_mem_eq_card_inter
    {V : Type*} [DecidableEq V] (S T : Finset V) :
    (∑ x ∈ S, if x ∈ T then 1 else 0) = (T ∩ S).card := by
  rw [← Finset.card_filter]
  congr 1
  ext x
  simp [and_comm]

private theorem sum_indicator_eq_eq_indicator_mem
    {V : Type*} [DecidableEq V] (S : Finset V) (c : V) :
    (∑ x ∈ S, if x = c then 1 else 0) = if c ∈ S then 1 else 0 := by
  by_cases hc : c ∈ S <;> simp [hc]

/-- Graph-facing (B15).  The two pointwise positive-spike cross-shore
profiles and the shore sizes force the exact K/R location balance. -/
theorem positiveSpike_threeSeparator_location_balance
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X Y K R : Finset V) (c : V) (q a b : ℕ)
    (hab : a + b = q - 1)
    (hxCard : X.card = q * (a + 1) - 2)
    (hyCard : Y.card = q * b - 1)
    (hxLarge : 2 ≤ q * (a + 1))
    (hyLarge : 1 ≤ q * b)
    (hXprofile : ∀ x ∈ X,
      (A.neighborFinset x ∩ Y).card + (if x ∈ R then 1 else 0) =
        b + (if x = c then 1 else 0))
    (hYprofile : ∀ y ∈ Y,
      (A.neighborFinset y ∩ X).card + (if y ∈ K then 1 else 0) =
        a + 1) :
    (K ∩ Y).card + (if c ∈ X then 1 else 0) + a + 1 =
      (R ∩ X).card + 2 * b := by
  let cross := ∑ x ∈ X, (A.neighborFinset x ∩ Y).card
  have hcomm : cross = ∑ y ∈ Y, (A.neighborFinset y ∩ X).card := by
    simpa [cross] using sum_card_neighbor_inter_comm A X Y
  have hXsum := Finset.sum_congr rfl hXprofile
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_indicator_mem_eq_card_inter X R,
    sum_indicator_eq_eq_indicator_mem X c] at hXsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hXsum
  have hYsum := Finset.sum_congr rfl hYprofile
  rw [Finset.sum_add_distrib, sum_indicator_mem_eq_card_inter Y K] at hYsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hYsum
  apply positiveSpike_location_balance_of_cross_incidence
    q a b X.card Y.card cross (R ∩ X).card
      (if c ∈ X then 1 else 0) (K ∩ Y).card
      hab hxCard hyCard hxLarge hyLarge
  · simpa [cross, mul_comm] using hXsum
  · rw [hcomm]
    simpa [mul_comm] using hYsum

end

end Erdos85

#print axioms Erdos85.positiveSpike_location_balance_of_cross_incidence
#print axioms Erdos85.positiveSpike_threeSeparator_location_balance

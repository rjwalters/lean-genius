import Proofs.Erdos85ThreeSeparatorPositiveSpikeLocationBalance

/-!
# Positive-spike K-location on the small side

Equation (B15) and the partition of the two-fold cover `K` across the two
shores give the exact small-side identity (B16).
-/

open Finset

namespace Erdos85

noncomputable section

/-- Subtraction-free arithmetic form of (B16). -/
theorem positiveSpike_smallSide_location_of_balance
    (q a b kY kSmall rX cX : ℕ)
    (hqpos : 0 < q)
    (hab : a + b = q - 1)
    (hKpartition : kY + kSmall = 2 * q)
    (hbalance : kY + cX + a + 1 = rX + 2 * b) :
    kSmall + rX = 3 * a + 3 + cX := by
  omega

/-- Finset form of (B16).  If `Y` and `X∪W` partition the ambient vertex
set and `K` has size `2q`, then (B15) determines the exact amount of `K`
on the small side `X∪W`. -/
theorem positiveSpike_threeSeparator_smallSide_location
    {V : Type*} [Fintype V] [DecidableEq V]
    (X Y W K R : Finset V) (c : V) (q a b : ℕ)
    (hqpos : 0 < q)
    (hab : a + b = q - 1)
    (hcover : Y ∪ (X ∪ W) = Finset.univ)
    (hdisj : Disjoint Y (X ∪ W))
    (hKcard : K.card = 2 * q)
    (hbalance : (K ∩ Y).card + (if c ∈ X then 1 else 0) + a + 1 =
      (R ∩ X).card + 2 * b) :
    (K ∩ (X ∪ W)).card + (R ∩ X).card =
      3 * a + 3 + (if c ∈ X then 1 else 0) := by
  have hpartsDisj : Disjoint (K ∩ Y) (K ∩ (X ∪ W)) := by
    exact hdisj.mono (Finset.inter_subset_right) (Finset.inter_subset_right)
  have hpartsUnion : (K ∩ Y) ∪ (K ∩ (X ∪ W)) = K := by
    ext v
    constructor
    · simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    · intro hvK
      have hvUniv : v ∈ Y ∪ (X ∪ W) := by
        rw [hcover]
        exact Finset.mem_univ v
      simp only [Finset.mem_union] at hvUniv
      rcases hvUniv with hy | hx | hw
      · apply Finset.mem_union.mpr
        apply Or.inl
        exact Finset.mem_inter.mpr ⟨hvK, hy⟩
      · apply Finset.mem_union.mpr
        apply Or.inr
        exact Finset.mem_inter.mpr ⟨hvK, by simp [hx]⟩
      · apply Finset.mem_union.mpr
        apply Or.inr
        exact Finset.mem_inter.mpr ⟨hvK, by simp [hw]⟩
  have hKpartition : (K ∩ Y).card + (K ∩ (X ∪ W)).card = 2 * q := by
    have hc := Finset.card_union_of_disjoint hpartsDisj
    rw [hpartsUnion, hKcard] at hc
    omega
  exact positiveSpike_smallSide_location_of_balance
    q a b (K ∩ Y).card (K ∩ (X ∪ W)).card (R ∩ X).card
      (if c ∈ X then 1 else 0) hqpos hab hKpartition hbalance

end

end Erdos85

#print axioms Erdos85.positiveSpike_smallSide_location_of_balance
#print axioms Erdos85.positiveSpike_threeSeparator_smallSide_location

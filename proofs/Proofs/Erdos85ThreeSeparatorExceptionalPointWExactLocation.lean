import Proofs.Erdos85ThreeSeparatorExceptionalPointWLocation

/-!
# Exact locations when the exceptional point lies in the separator

Endpoint B16 leaves only three units of K/R mass on `X ∪ W`.  The K-mass
on X is positive and even, while `c ∈ K ∩ W` supplies another unit.  Thus
the distribution is forced to `(k_X,k_W,r_X)=(2,1,0)`.  This is (B17W').
-/

open Finset

namespace Erdos85

/-- Arithmetic core of B17W'. -/
theorem exceptionalPoint_W_exact_location_counts
    {kX kW rX : ℕ} (hbalance : kX + kW + rX = 3)
    (hkXeven : Even kX) (hkXpos : 1 ≤ kX) (hkWpos : 1 ≤ kW) :
    kX = 2 ∧ kW = 1 ∧ rX = 0 := by
  obtain ⟨t, ht⟩ := hkXeven
  omega

/-- Finset-facing B17W': exact K/R locations on the small shore and
separator. -/
theorem exceptionalPoint_W_exact_K_R_location
    {V : Type*} [DecidableEq V]
    (X W K R : Finset V) (c : V)
    (hbalance : (K ∩ X).card + (K ∩ W).card + (R ∩ X).card = 3)
    (hkXeven : Even (K ∩ X).card) (hkXpos : 1 ≤ (K ∩ X).card)
    (hcK : c ∈ K) (hcW : c ∈ W) :
    (R ∩ X) = ∅ ∧ (K ∩ X).card = 2 ∧ (K ∩ W) = {c} := by
  have hcKW : c ∈ K ∩ W := Finset.mem_inter.mpr ⟨hcK, hcW⟩
  have hkWpos : 1 ≤ (K ∩ W).card := Finset.one_le_card.mpr ⟨c, hcKW⟩
  obtain ⟨hkX, hkW, hrX⟩ :=
    exceptionalPoint_W_exact_location_counts hbalance hkXeven hkXpos hkWpos
  have hrEmpty : R ∩ X = ∅ := Finset.card_eq_zero.mp hrX
  have hKWone : (K ∩ W).card = 1 := hkW
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hKWone
  have hcz : c = z := by
    rw [hz] at hcKW
    exact Finset.mem_singleton.mp hcKW
  subst z
  exact ⟨hrEmpty, hkX, hz⟩

#print axioms exceptionalPoint_W_exact_location_counts
#print axioms exceptionalPoint_W_exact_K_R_location

end Erdos85

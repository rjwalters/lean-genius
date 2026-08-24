import Proofs.Erdos85ThreeSeparatorUniformExceptionalMatchingCount

/-!
# Large-shore location pressure for the exceptional point

If the exceptional point lies in `Y`, its defect neighborhood contributes
almost `q` points to `K ∩ Y`.  Substitution into the location balance (B15)
forces the lower bound (B20) on `R ∩ X`.
-/

open Finset

namespace Erdos85

/-- Subtraction-safe arithmetic core of (B20). -/
theorem opposite_residue_lower_of_largeShore_K_lower
    (q a b n kY rX : ℕ)
    (hab : a + b = q - 1)
    (hq : 0 < q)
    (hn : n ≤ 1)
    (hkY : q - n ≤ kY)
    (hbalance : kY + a + 1 = rX + 2 * b) :
    3 * a + 3 - q - n ≤ rX ∧ 3 * a + 2 - q ≤ rX := by
  have hqeq : q = a + b + 1 := by omega
  have hnq : n ≤ q := by omega
  have hkY' : q ≤ kY + n := by omega
  have hraw : 3 * a + 3 ≤ rX + q + n := by omega
  constructor <;> omega

/-- Finset-facing (B20): when `c ∈ Y`, the B15 location balance and the
large-shore K-mass bound force many R-points into the opposite shore `X`. -/
theorem positiveSpike_exceptionalPoint_largeShore_forces_opposite_residue
    {V : Type*} [DecidableEq V]
    (X Y K R : Finset V) (c : V) (q a b n : ℕ)
    (hab : a + b = q - 1)
    (hq : 0 < q)
    (hXY : Disjoint X Y)
    (hcY : c ∈ Y)
    (hn : n ≤ 1)
    (hkY : q - n ≤ (K ∩ Y).card)
    (hbalance : (K ∩ Y).card + (if c ∈ X then 1 else 0) + a + 1 =
      (R ∩ X).card + 2 * b) :
    3 * a + 3 - q - n ≤ (R ∩ X).card ∧
      3 * a + 2 - q ≤ (R ∩ X).card := by
  have hcX : c ∉ X := by
    intro hcX
    exact (Finset.disjoint_left.mp hXY) hcX hcY
  have hbalance' : (K ∩ Y).card + a + 1 = (R ∩ X).card + 2 * b := by
    simpa [hcX] using hbalance
  exact opposite_residue_lower_of_largeShore_K_lower
    q a b n (K ∩ Y).card (R ∩ X).card hab hq hn hkY hbalance'

#print axioms opposite_residue_lower_of_largeShore_K_lower
#print axioms positiveSpike_exceptionalPoint_largeShore_forces_opposite_residue

end Erdos85

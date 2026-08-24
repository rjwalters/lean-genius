import Proofs.Erdos85ThreeSeparatorUniformExceptionalMatchingCount
import Proofs.Erdos85ThreeSeparatorExceptionalPointYLocation

/-! # Uniform lower bounds in the exceptional Y-location -/

open Finset SimpleGraph

namespace Erdos85

/-- B18 K-containment puts the center and all internal-Y defect neighbors
inside `K∩Y`, giving the first lower bound in B20. -/
theorem exceptionalPoint_Y_K_location_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (c : V) (Y K : Finset V) (q n : ℕ)
    (hcY : c ∈ Y) (hcK : c ∈ K)
    (hneighborK : D.neighborFinset c ⊆ K)
    (hinside : (D.neighborFinset c ∩ Y).card + n = q - 1) :
    q - n ≤ (K ∩ Y).card := by
  let T := insert c (D.neighborFinset c ∩ Y)
  have hcNot : c ∉ D.neighborFinset c ∩ Y := by
    intro hc
    exact D.loopless.irrefl c
      ((D.mem_neighborFinset c c).mp (Finset.mem_inter.mp hc).1)
  have hTcard : T.card = (D.neighborFinset c ∩ Y).card + 1 := by
    dsimp [T]
    rw [Finset.card_insert_of_notMem hcNot]
  have hTsub : T ⊆ K ∩ Y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact Finset.mem_inter.mpr ⟨hcK, hcY⟩
    · have hz' := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨hneighborK hz'.1, hz'.2⟩
  have hTle := Finset.card_le_card hTsub
  rw [hTcard] at hTle
  omega

/-- Arithmetic location transfer in B20, expressed with Nat subtraction only
in the conclusions. -/
theorem exceptionalPoint_Y_R_location_lower_of_balance
    {q a b n kY rX : ℕ}
    (hq : 1 ≤ q) (hab : a + b = q - 1)
    (hkY : q - n ≤ kY)
    (hbalance : kY + a + 1 = rX + 2 * b)
    (hn : n ≤ 1) :
    3 * a + 3 - (q + n) ≤ rX ∧ 3 * a + 2 - q ≤ rX := by
  omega

/-- Combined cardinal form of the B20 Y-location constraint. -/
theorem exceptionalPoint_Y_location_lower
    {V : Type*} [DecidableEq V]
    (K R X Y : Finset V) {q a b n : ℕ}
    (hq : 1 ≤ q) (hab : a + b = q - 1)
    (hKY : q - n ≤ (K ∩ Y).card)
    (hbalance : (K ∩ Y).card + a + 1 =
      (R ∩ X).card + 2 * b)
    (hn : n ≤ 1) :
    3 * a + 3 - (q + n) ≤ (R ∩ X).card ∧
      3 * a + 2 - q ≤ (R ∩ X).card :=
  exceptionalPoint_Y_R_location_lower_of_balance hq hab hKY hbalance hn

#print axioms exceptionalPoint_Y_K_location_lower
#print axioms exceptionalPoint_Y_R_location_lower_of_balance
#print axioms exceptionalPoint_Y_location_lower

end Erdos85

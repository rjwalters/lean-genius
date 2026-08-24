import Proofs.Erdos85FinalDyadicExceptionalSupportBridge
import Proofs.Erdos85CanonicalExceptionalMassBalance

/-!
# Final dyadic exceptional profile

At the last dyadic scale, divisibility and the degree bound force every line
occupancy to be `0`, `q/2`, or `q`.  Naming this trichotomy discharges the
normal-form hypothesis used throughout the canonical exceptional-support
chain directly from the stopping data.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Final-scale divisibility forces the canonical three-level occupancy
profile. -/
theorem finalDyadic_occupancy_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      2 * (G.neighborFinset v ∩ S).card = q ∨
      (G.neighborFinset v ∩ S).card = q := by
  intro v
  let n := (G.neighborFinset v ∩ S).card
  have hnle : n ≤ q := by
    calc
      n ≤ (G.neighborFinset v).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  obtain ⟨t, ht⟩ := hdiv v
  have ha : 0 < 2 ^ j := by positivity
  have htLe : t ≤ 2 := by
    change n = 2 ^ j * t at ht
    rw [ht, hqa] at hnle
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ j) (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnle) ha
  change n = 0 ∨ 2 * n = q ∨ n = q
  change n = 2 ^ j * t at ht
  interval_cases t <;> simp_all [Nat.mul_comm]

/-- The canonical signed exceptional vector is the exact sparse right-hand
side of the cut-sign adjacency equation at the final dyadic scale. -/
theorem finalDyadic_cutSign_adjMatrix_mulVec_eq_exceptionalOccupancySign
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    (G.adjMatrix ℤ).mulVec
        (fun w => if w ∈ S then (1 : ℤ) else -1) =
      (q : ℤ) • exceptionalOccupancySign G S q := by
  have hq : 0 < q := by rw [hqa]; positivity
  exact cutSign_adjMatrix_mulVec_eq_exceptionalOccupancySign
    G hq hreg S (finalDyadic_occupancy_trichotomy G hqa hreg S hdiv)

/-- Final-scale full-minus-empty population equals the shore displacement. -/
theorem finalDyadic_full_sub_empty_eq_cutDisplacement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    ((fullLineCenters G S q).card : ℤ) -
        (emptyLineCenters G S).card =
      2 * (S.card : ℤ) - Fintype.card V := by
  have hq : 0 < q := by rw [hqa]; positivity
  exact fullLineCenters_card_sub_emptyLineCenters_card_eq_cutDisplacement
    G hq hreg S
      (finalDyadic_occupancy_trichotomy G hqa hreg S hdiv)

end

end Erdos85

#print axioms Erdos85.finalDyadic_occupancy_trichotomy
#print axioms Erdos85.finalDyadic_cutSign_adjMatrix_mulVec_eq_exceptionalOccupancySign
#print axioms Erdos85.finalDyadic_full_sub_empty_eq_cutDisplacement

import Proofs.Erdos85DivisibleOccupancyShoreBalance
import Proofs.Erdos85CanonicalExceptionalSignedSupport

/-!
# Final dyadic support as the complement of the exceptional support

At the final scale `a=q/2`, divisibility leaves only occupancies `0,a,q`.
The odd quotient support is therefore exactly the half-occupancy family,
and its complement is exactly the canonical full/empty exceptional family.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At `a=q/2`, a line is unmarked precisely when it is full or empty. -/
theorem compl_dyadicOccupancySupport_eq_exceptionalSignedSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    (dyadicOccupancySupport G S j)ᶜ = exceptionalSignedSupport G S q := by
  ext x
  simp only [Finset.mem_compl, dyadicOccupancySupport, Finset.mem_filter,
    Finset.mem_univ, true_and, mem_exceptionalSignedSupport]
  let n := (G.neighborFinset x ∩ S).card
  have hnle : n ≤ q := by
    calc
      n ≤ (G.neighborFinset x).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = q := by rw [G.card_neighborFinset_eq_degree, hreg]
  obtain ⟨t, ht⟩ := hdiv x
  have ha : 0 < 2 ^ j := by positivity
  have htLe : t ≤ 2 := by
    change n = 2 ^ j * t at ht
    rw [ht, hqa] at hnle
    apply Nat.le_of_mul_le_mul_left (c := 2 ^ j) (by
      simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnle) ha
  have hquot : n / 2 ^ j = t := by
    change n = 2 ^ j * t at ht
    rw [ht]
    exact Nat.mul_div_cancel_left t ha
  change ¬ Odd (n / 2 ^ j) ↔ n = q ∨ n = 0
  rw [hquot]
  change n = 2 ^ j * t at ht
  interval_cases t <;> simp_all [Nat.mul_comm]

/-- Set-level bridge all the way to the named canonical full and empty
line-center families. -/
theorem compl_dyadicOccupancySupport_eq_full_union_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    (dyadicOccupancySupport G S j)ᶜ =
      fullLineCenters G S q ∪ emptyLineCenters G S := by
  rw [compl_dyadicOccupancySupport_eq_exceptionalSignedSupport
    G hqa hreg S hdiv,
    exceptionalSignedSupport_eq_full_union_empty]

/-- Cardinal form: the arithmetic small-complement parameter is exactly
the canonical exceptional support population. -/
theorem card_compl_dyadicOccupancySupport_eq_exceptionalSignedSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    ((dyadicOccupancySupport G S j)ᶜ : Finset V).card =
      (exceptionalSignedSupport G S q).card := by
  rw [compl_dyadicOccupancySupport_eq_exceptionalSignedSupport
    G hqa hreg S hdiv]

end

end Erdos85

#print axioms Erdos85.compl_dyadicOccupancySupport_eq_exceptionalSignedSupport
#print axioms Erdos85.compl_dyadicOccupancySupport_eq_full_union_empty

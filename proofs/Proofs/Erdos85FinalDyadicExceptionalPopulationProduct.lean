import Proofs.Erdos85FinalDyadicExceptionalProfile

/-!
# Product form of the final exceptional populations

The full/empty cross-edge penalty depends on a product of two population
counts.  The elementary difference-of-squares identity rewrites that product
using only total exceptional support and signed shore displacement.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Population product as a difference of the total and signed squares. -/
theorem four_mul_population_product_eq_sq_sub_difference_sq
    {full empty total : ℕ} (hsum : full + empty = total) :
    4 * ((full * empty : ℕ) : ℤ) =
      (total : ℤ) ^ 2 - ((full : ℤ) - empty) ^ 2 := by
  have hsumZ : (full : ℤ) + empty = total := by exact_mod_cast hsum
  rw [← hsumZ]
  push_cast
  ring

/-- At the final dyadic scale, four times the full×empty population product
is support-size squared minus shore-displacement squared. -/
theorem finalDyadic_exceptional_population_product_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q j : ℕ} (hqa : q = 2 * 2 ^ j)
    (hreg : ∀ v, G.degree v = q)
    (S : Finset V)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card) :
    4 * (((fullLineCenters G S q).card *
          (emptyLineCenters G S).card : ℕ) : ℤ) =
      ((exceptionalSignedSupport G S q).card : ℤ) ^ 2 -
        (2 * (S.card : ℤ) - Fintype.card V) ^ 2 := by
  have hsum : (fullLineCenters G S q).card +
      (emptyLineCenters G S).card =
        (exceptionalSignedSupport G S q).card := by
    exact (exceptionalSignedSupport_card_eq_full_add_empty
      G S (by rw [hqa]; positivity)).symm
  have hproduct := four_mul_population_product_eq_sq_sub_difference_sq hsum
  rw [finalDyadic_full_sub_empty_eq_cutDisplacement
    G hqa hreg S hdiv] at hproduct
  exact hproduct

end

end Erdos85

#print axioms Erdos85.four_mul_population_product_eq_sq_sub_difference_sq
#print axioms Erdos85.finalDyadic_exceptional_population_product_identity

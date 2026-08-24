import Proofs.Erdos85EulerianCutParity

/-!
# The positive-spike Y-shore location parity

The positive-spike internal-degree profile on the `Y` shore, combined with
the handshake lemma, forces the parity constraint recorded as (B16b).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Arithmetic form of (B16b).  An even internal-degree sum and the summed
positive-spike profile force the `R`-location count (with the exceptional
point counted once when present) to have parity `a+1`. -/
theorem positiveSpike_Y_location_parity_of_sum_profile
    (q a b yCard internal rY cY : ℕ)
    (hqEven : Even q)
    (hb : 1 ≤ b)
    (hab : a + b = q - 1)
    (hyCard : yCard = q * b - 1)
    (hinternal : Even internal)
    (hprofile : internal + rY = b * yCard + cY) :
    (rY + cY) % 2 = (a + 1) % 2 := by
  have hqmod : q % 2 = 0 := Nat.even_iff.mp hqEven
  have hqbmod : (q * b) % 2 = 0 := by
    simp [Nat.mul_mod, hqmod]
  have hqpos : 0 < q := by
    by_contra h
    have : q = 0 := by omega
    simp [this] at hab
    omega
  have hqbpos : 0 < q * b := Nat.mul_pos hqpos hb
  have hyMod : yCard % 2 = 1 := by
    rw [hyCard]
    omega
  have hbyMod : (b * yCard) % 2 = b % 2 := by
    simp [Nat.mul_mod, hyMod]
  have hiMod : internal % 2 = 0 := Nat.even_iff.mp hinternal
  have hprofileMod := congrArg (fun n : ℕ ↦ n % 2) hprofile
  have habMod := congrArg (fun n : ℕ ↦ n % 2) hab
  have hpredMod : (q - 1) % 2 = 1 := by omega
  omega

/-- Graph-facing (B16b): if the induced `A[Y]` degrees obey the
positive-spike profile, then `|R∩Y| + 1_(c∈Y)` has parity `a+1`. -/
theorem positiveSpike_threeSeparator_Y_location_parity
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (Y R : Finset V) (c : V) (q a b : ℕ)
    (hqEven : Even q)
    (hb : 1 ≤ b)
    (hab : a + b = q - 1)
    (hyCard : Y.card = q * b - 1)
    (hprofile : ∀ y ∈ Y,
      (A.neighborFinset y ∩ Y).card + (if y ∈ R then 1 else 0) =
        b + (if y = c then 1 else 0)) :
    ((R ∩ Y).card + if c ∈ Y then 1 else 0) % 2 = (a + 1) % 2 := by
  let internal := ∑ y ∈ Y, (A.neighborFinset y ∩ Y).card
  have hinternal : Even internal := by
    simpa [internal] using even_sum_internalNeighbor_card A Y
  have hRsum : (∑ y ∈ Y, if y ∈ R then 1 else 0) = (R ∩ Y).card := by
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp [and_comm]
  have hcsum : (∑ y ∈ Y, if y = c then 1 else 0) =
      if c ∈ Y then 1 else 0 := by
    by_cases hc : c ∈ Y
    · simp [hc]
    · simp [hc]
  have hsum := Finset.sum_congr rfl hprofile
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hRsum, hcsum] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  exact positiveSpike_Y_location_parity_of_sum_profile
    q a b Y.card internal (R ∩ Y).card (if c ∈ Y then 1 else 0)
      hqEven hb hab hyCard hinternal (by simpa [internal, mul_comm] using hsum)

end

end Erdos85

#print axioms Erdos85.positiveSpike_Y_location_parity_of_sum_profile
#print axioms Erdos85.positiveSpike_threeSeparator_Y_location_parity

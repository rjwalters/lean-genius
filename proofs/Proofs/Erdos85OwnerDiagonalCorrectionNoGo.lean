import Proofs.Erdos85OwnerComplementSpecialContribution

/-!
# Shared diagonal correction cannot create diagonal owner demand

The owner-cut decomposition has a shared internal cross-owner correction in
both coordinates.  Such a diagonal scalar cannot repair an ordinary owner
vector of odd aggregate parity: it preserves or swaps the one-hot charge,
but never produces `(1,1)`.
-/

namespace Erdos85

noncomputable section

/-- Adding the same `F₂` scalar in both coordinates either preserves a
one-hot owner vector or swaps it to the complementary owner. -/
theorem boolOwnerUnit_add_diagonal_eq_oneHot
    (charged : Bool) (t : ZMod 2) :
    (fun j => boolOwnerUnit charged j + t) =
      if t = 0 then boolOwnerUnit charged else boolOwnerUnit (!charged) := by
  funext j
  fin_cases t <;> cases charged <;> cases j <;> decide

/-- **Diagonal-correction no-go (`73rnz_cjibkzp-diag`).**  No shared scalar
correction can turn a two-owner vector of aggregate parity one into `(1,1)`. -/
theorem not_forall_add_diagonal_eq_one_of_sum_eq_one
    (f : Bool → ZMod 2) (hsum : (∑ i : Bool, f i) = 1)
    (t : ZMod 2) :
    ¬ ∀ i : Bool, f i + t = 1 := by
  intro hdiag
  have hf := hdiag false
  have ht := hdiag true
  have hsum' : f true + f false = 1 := by
    rw [← Fintype.sum_bool]
    exact hsum
  have hleftZero : (f false + t) + (f true + t) = 0 := by
    rw [hf, ht]
    decide
  have htt : t + t = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
  have hrearrange :
      (f false + t) + (f true + t) = f true + f false := by
    calc
      (f false + t) + (f true + t) =
          (f true + f false) + (t + t) := by abel
      _ = f true + f false := by rw [htt, add_zero]
  have hsumZero : f true + f false = 0 := by
    rw [← hrearrange]
    exact hleftZero
  rw [hsumZero] at hsum'
  exact zero_ne_one hsum'

/-- Graph-native ledger specialization: odd ordinary residual mass cannot be
upgraded to diagonal owner demand by adding one shared correction scalar. -/
theorem ordinaryResidualOwnerMass_not_diagonal_of_sharedCorrection
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c))
    (hodd : (∑ c ∈ pairs,
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
        (left c) (right c)) = 1)
    (sharedCorrection : ZMod 2) :
    let L := ordinaryResidualOwnerTransportLedger
      A hq hreg pairs left right owner hnotA
    ¬ ∀ i : Bool,
      L.ownerSourceMass i + sharedCorrection = 1 := by
  let L := ordinaryResidualOwnerTransportLedger
    A hq hreg pairs left right owner hnotA
  have hsum : (∑ i : Bool, L.ownerSourceMass i) = 1 := by
    rw [sum_ownerSourceMass_ordinaryResidualOwnerTransportLedger]
    exact hodd
  exact not_forall_add_diagonal_eq_one_of_sum_eq_one
    L.ownerSourceMass hsum sharedCorrection

end


end Erdos85

#print axioms Erdos85.boolOwnerUnit_add_diagonal_eq_oneHot
#print axioms Erdos85.not_forall_add_diagonal_eq_one_of_sum_eq_one
#print axioms Erdos85.ordinaryResidualOwnerMass_not_diagonal_of_sharedCorrection

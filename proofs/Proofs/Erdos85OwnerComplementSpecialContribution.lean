import Proofs.Erdos85OrdinaryResidualOwnerMassSplit

/-!
# The complementary special contribution forced by owner parity

An ordinary owner vector whose two coordinates sum to one is not diagonal:
it is exactly a one-hot vector.  Therefore the unique correction which turns
it into `(1,1)` is a one-hot special contribution in the complementary owner
coordinate.  This identifies precisely what the remaining special endpoint
must carry.
-/

namespace Erdos85

noncomputable section

/-- The unit vector at one Boolean owner. -/
def boolOwnerUnit (i : Bool) : Bool → ZMod 2 :=
  fun j => if j = i then 1 else 0

/-- A two-owner vector of odd aggregate parity has a unique charged owner. -/
theorem existsUnique_owner_eq_one_of_sum_eq_one
    (f : Bool → ZMod 2) (hsum : (∑ i : Bool, f i) = 1) :
    ∃! i : Bool, f i = 1 := by
  have hsum' : f true + f false = 1 := by
    rw [← Fintype.sum_bool]
    exact hsum
  generalize hfalse : f false = x
  generalize htrue : f true = y
  fin_cases x <;> fin_cases y
  · rw [htrue, hfalse] at hsum'
    change (0 : ZMod 2) + 0 = 1 at hsum'
    rw [zero_add] at hsum'
    exact (zero_ne_one hsum').elim
  · refine ⟨true, htrue, ?_⟩
    intro i hi
    cases i
    · rw [hfalse] at hi
      exact (zero_ne_one hi).elim
    · rfl
  · refine ⟨false, hfalse, ?_⟩
    intro i hi
    cases i
    · rfl
    · rw [htrue] at hi
      exact (zero_ne_one hi).elim
  · rw [htrue, hfalse] at hsum'
    change (1 : ZMod 2) + 1 = 1 at hsum'
    have htwo : (1 + 1 : ZMod 2) = 0 := by decide
    rw [htwo] at hsum'
    exact (zero_ne_one hsum').elim

/-- The unique charged owner determines the whole ordinary vector. -/
theorem eq_boolOwnerUnit_of_sum_eq_one_of_apply_eq_one
    (f : Bool → ZMod 2) (hsum : (∑ i : Bool, f i) = 1)
    (charged : Bool) (hcharged : f charged = 1) :
    f = boolOwnerUnit charged := by
  funext j
  generalize hfalse : f false = x
  generalize htrue : f true = y
  fin_cases x <;> fin_cases y <;> cases charged <;> cases j <;>
    simp_all [boolOwnerUnit]

/-- Adding the complementary owner unit to a one-hot ordinary vector gives
the diagonal owner demand `(1,1)`. -/
theorem boolOwnerUnit_add_complement_eq_one (charged : Bool) :
    ∀ j : Bool,
      boolOwnerUnit charged j + boolOwnerUnit (!charged) j = 1 := by
  intro j
  cases charged <;> cases j <;> decide

/-- The complementary unit is the *unique* special contribution which turns
the one-hot ordinary vector into the diagonal vector. -/
theorem add_eq_one_iff_eq_complementOwnerUnit
    (charged : Bool) (special : Bool → ZMod 2) :
    (∀ j, boolOwnerUnit charged j + special j = 1) ↔
      special = boolOwnerUnit (!charged) := by
  constructor
  · intro h
    funext j
    have hj := h j
    cases charged <;> cases j <;>
      simp [boolOwnerUnit] at hj ⊢ <;> exact hj
  · rintro rfl
    exact boolOwnerUnit_add_complement_eq_one charged

/-- **Forced complementary special endpoint (`73rnz_cjibkzo`).**  Odd
unlabelled ordinary residual mass determines a unique charged owner in the
graph-native ledger.  The unique owner-vector correction producing `(1,1)`
is the unit at the complementary owner. -/
theorem existsUnique_chargedOwner_and_specialCorrection
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c))
    (hodd : (∑ c ∈ pairs,
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
        (left c) (right c)) = 1) :
    let L := ordinaryResidualOwnerTransportLedger
      A hq hreg pairs left right owner hnotA
    ∃! charged : Bool,
      L.ownerSourceMass charged = 1 ∧
      (∀ special : Bool → ZMod 2,
        (∀ j, L.ownerSourceMass j + special j = 1) ↔
          special = boolOwnerUnit (!charged)) := by
  let L := ordinaryResidualOwnerTransportLedger
    A hq hreg pairs left right owner hnotA
  have hsum : (∑ i : Bool, L.ownerSourceMass i) = 1 := by
    rw [sum_ownerSourceMass_ordinaryResidualOwnerTransportLedger]
    exact hodd
  obtain ⟨charged, hcharged, hunique⟩ :=
    existsUnique_owner_eq_one_of_sum_eq_one L.ownerSourceMass hsum
  have hvector : L.ownerSourceMass = boolOwnerUnit charged :=
    eq_boolOwnerUnit_of_sum_eq_one_of_apply_eq_one
      L.ownerSourceMass hsum charged hcharged
  refine ⟨charged, ⟨hcharged, ?_⟩, ?_⟩
  · intro special
    rw [hvector]
    exact add_eq_one_iff_eq_complementOwnerUnit charged special
  · intro i hi
    exact hunique i hi.1

end


end Erdos85

#print axioms Erdos85.existsUnique_owner_eq_one_of_sum_eq_one
#print axioms Erdos85.add_eq_one_iff_eq_complementOwnerUnit
#print axioms Erdos85.existsUnique_chargedOwner_and_specialCorrection

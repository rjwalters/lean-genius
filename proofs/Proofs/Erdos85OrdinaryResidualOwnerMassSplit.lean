import Proofs.Erdos85OrdinaryResidualOwnerTransportCells

/-!
# Forgetting and recovering owner labels on ordinary residual transport

The graph-native ordinary ledger partitions its cells by the two Boolean
owners.  Forgetting that partition recovers exactly the unlabelled residual
`K`, quadratic `nu`, and cubic `mu` masses.  Consequently an odd unlabelled
residual mass selects an actual odd owner fibre.  This is deliberately weaker
than two-coordinate owner demand: aggregate conservation chooses one owner but
does not manufacture a unit in both coordinates.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_bool_filtered_eq_sum
    {C : Type*} [DecidableEq C]
    (S : Finset C) (owner : C → Bool) (f : C → ZMod 2) :
    (∑ i : Bool, ∑ c ∈ S.filter (fun c => owner c = i), f c) =
      ∑ c ∈ S, f c := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.sum_eq_single (owner c)]
  · simp
  · intro i _ hine
    simp [hine.symm]
  · simp

private theorem sum_ownerSourceMass_eq_sum_source
    {C : Type*} [DecidableEq C] (L : OwnerSourceTransportLedger C) :
    (∑ i : Bool, L.ownerSourceMass i) = ∑ c ∈ L.cells, L.source c := by
  unfold OwnerSourceTransportLedger.ownerSourceMass
    OwnerSourceTransportLedger.ownerCells
  exact sum_bool_filtered_eq_sum L.cells L.owner L.source

private theorem sum_ownerRelayMass_eq_sum_relay
    {C : Type*} [DecidableEq C] (L : OwnerSourceTransportLedger C) :
    (∑ i : Bool, L.ownerRelayMass i) = ∑ c ∈ L.cells, L.relay c := by
  unfold OwnerSourceTransportLedger.ownerRelayMass
    OwnerSourceTransportLedger.ownerCells
  exact sum_bool_filtered_eq_sum L.cells L.owner L.relay

/-- Forgetting the owner label on the graph-native ordinary ledger recovers
the literal residual-`K` source mass. -/
theorem sum_ownerSourceMass_ordinaryResidualOwnerTransportLedger
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c)) :
    (∑ i : Bool,
      (ordinaryResidualOwnerTransportLedger A hq hreg pairs left right owner hnotA).ownerSourceMass i) =
      ∑ c ∈ pairs,
        graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
          (left c) (right c) := by
  rw [sum_ownerSourceMass_eq_sum_source]
  apply Finset.sum_congr rfl
  intro c hc
  change c ∈ pairs at hc
  simp [ordinaryResidualOwnerTransportLedger,
    ownerSourceTransportLedgerOfCells, hc,
    ordinaryResidualOwnerTransportCell]

/-- Forgetting owner labels recovers the total quadratic relay mass. -/
theorem sum_ownerRelayMass_ordinaryResidualOwnerTransportLedger
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c)) :
    (∑ i : Bool,
      (ordinaryResidualOwnerTransportLedger A hq hreg pairs left right owner hnotA).ownerRelayMass i) =
      ∑ c ∈ pairs, ordinaryNu A (left c) (right c) := by
  rw [sum_ownerRelayMass_eq_sum_relay]
  apply Finset.sum_congr rfl
  intro c hc
  change c ∈ pairs at hc
  simp [ordinaryResidualOwnerTransportLedger,
    ownerSourceTransportLedgerOfCells, hc,
    ordinaryResidualOwnerTransportCell]

/-- Forgetting owner labels recovers the total cubic corrected mass. -/
theorem sum_psiHatOwner_ordinaryResidualOwnerTransportLedger
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c)) :
    (∑ i : Bool,
      (ordinaryResidualOwnerTransportLedger A hq hreg pairs left right owner hnotA).psiHatOwner i) =
      ∑ c ∈ pairs, ordinaryMu A (left c) (right c) := by
  simp only [psiHatOwner_ordinaryResidualOwnerTransportLedger_apply]
  exact sum_bool_filtered_eq_sum pairs owner fun c =>
    ordinaryMu A (left c) (right c)

/-- An odd unlabelled residual-`K` mass is carried by a concrete owner fibre.
This is the exact conclusion available from aggregate cross-witness
conservation before the separate two-coordinate owner-demand theorem. -/
theorem exists_ownerSourceMass_eq_one_of_ordinaryResidual_K_mass_eq_one
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c))
    (hodd : (∑ c ∈ pairs,
      graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
        (left c) (right c)) = 1) :
    ∃ i : Bool,
      (ordinaryResidualOwnerTransportLedger A hq hreg pairs left right owner hnotA).ownerSourceMass i = 1 := by
  let L := ordinaryResidualOwnerTransportLedger A hq hreg pairs left right owner hnotA
  have hsum : (∑ i : Bool, L.ownerSourceMass i) = 1 := by
    rw [sum_ownerSourceMass_ordinaryResidualOwnerTransportLedger]
    exact hodd
  by_contra hnone
  push Not at hnone
  have hzero : ∀ i : Bool, L.ownerSourceMass i = 0 := by
    intro i
    have hi := hnone i
    generalize hx : L.ownerSourceMass i = x at hi ⊢
    fin_cases x
    · rfl
    · exact (hi rfl).elim
  have : (0 : ZMod 2) = 1 := by simpa [hzero] using hsum
  exact zero_ne_one this

end

end Erdos85

#print axioms Erdos85.sum_ownerSourceMass_ordinaryResidualOwnerTransportLedger
#print axioms Erdos85.sum_ownerRelayMass_ordinaryResidualOwnerTransportLedger
#print axioms Erdos85.sum_psiHatOwner_ordinaryResidualOwnerTransportLedger
#print axioms Erdos85.exists_ownerSourceMass_eq_one_of_ordinaryResidual_K_mass_eq_one

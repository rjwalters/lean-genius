import Proofs.Erdos85OrdinaryResidualNuMuDecomposition
import Proofs.Erdos85OwnerSourceTransportCells

/-!
# Graph-native ordinary owner-transport cells

For a non-edge `(u,v)`, the residual-K atom is graph-theoretically
`nu(u,v) + mu(u,v)`.  Adding the quadratic relay atom `nu` therefore leaves
the cubic corrected atom `mu`.  This file packages that identity as actual
owner-labelled transport cells and ledgers, eliminating the local transport
law as an assumption on ordinary pairs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Quadratic common-neighbor parity on an ordinary pair. -/
def ordinaryNu
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (u v : V) : ZMod 2 :=
  (((A.neighborFinset u ∩ A.neighborFinset v).card : ℕ) : ZMod 2)

/-- Cubic matching/walk parity on an ordinary pair. -/
def ordinaryMu
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (u v : V) : ZMod 2 :=
  (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
    A.adjMatrix (ZMod 2)) u v

/-- A graph-derived ordinary pair is a verified owner source-transport cell:
residual K plus the `nu` relay equals corrected `mu`. -/
def ordinaryResidualOwnerTransportCell
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (owner : Bool) (u v : V) (hnotA : ¬ A.Adj u v) :
    OwnerSourceTransportCell where
  owner := owner
  source := graphEdgeIndicator (binaryTransportResidualGraph A hq hreg) u v
  relay := ordinaryNu A u v
  corrected := ordinaryMu A u v
  transport := by
    rw [graphEdgeIndicator_binaryTransportResidual_eq_nu_add_mu_of_not_adj
      A hq hreg hnotA]
    change (ordinaryNu A u v + ordinaryMu A u v) + ordinaryNu A u v =
      ordinaryMu A u v
    have hnu : ordinaryNu A u v + ordinaryNu A u v = 0 := by
      rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]
    calc
      (ordinaryNu A u v + ordinaryMu A u v) + ordinaryNu A u v =
          (ordinaryNu A u v + ordinaryNu A u v) + ordinaryMu A u v := by
        abel
      _ = ordinaryMu A u v := by rw [hnu, zero_add]

/-- Assemble any finite population of non-adjacent ordinary pairs into a
graph-native owner-resolved source-transport ledger. -/
def ordinaryResidualOwnerTransportLedger
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c)) :
    OwnerSourceTransportLedger C :=
  ownerSourceTransportLedgerOfCells pairs fun c =>
    if hc : c ∈ pairs then
      ordinaryResidualOwnerTransportCell A hq hreg (owner c)
        (left c) (right c) (hnotA c hc)
    else
      { owner := owner c
        source := 0
        relay := 0
        corrected := 0
        transport := by simp }

/-- Each corrected owner coordinate of the graph-native ordinary ledger is
literally the sum of cubic `mu` atoms in that owner fibre. -/
theorem psiHatOwner_ordinaryResidualOwnerTransportLedger_apply
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (pairs : Finset C) (left right : C → V) (owner : C → Bool)
    (hnotA : ∀ c ∈ pairs, ¬ A.Adj (left c) (right c)) (i : Bool) :
    OwnerSourceTransportLedger.psiHatOwner
        (ordinaryResidualOwnerTransportLedger A hq hreg pairs left right owner hnotA) i =
      ∑ c ∈ pairs.filter (fun c => owner c = i), ordinaryMu A (left c) (right c) := by
  unfold ordinaryResidualOwnerTransportLedger
  rw [psiHatOwner_ledgerOfCells_apply]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hcpairs
  simp [hcpairs,
    ordinaryResidualOwnerTransportCell]

end


end Erdos85

#print axioms Erdos85.ordinaryResidualOwnerTransportCell
#print axioms Erdos85.psiHatOwner_ordinaryResidualOwnerTransportLedger_apply

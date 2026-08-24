import Proofs.Erdos85OwnerLedgerTriangleCutResidual
import Proofs.Erdos85OddWitnessBlockPricedCrossRoute

/-!
# Owner-terminal failure exports a priced cross-witness route

The diagonal owner obstruction is a genuine cross-witness character.  Once
the literal residual cut is identified with the labeled relay occurrence
block, failure of the owner terminal produces an actual paired route leaving
the residual witness block, with its endpoint price and geometry retained.
-/

open SimpleGraph

namespace Erdos85

open OwnerSourceTransportLedger

noncomputable section

/-- If the corrected owner terminal fails, the odd residual cut cannot stay
inside one witness block: it yields a concrete priced paired relay segment
whose canonical witness labels lie on opposite sides of `R`. -/
theorem exists_priced_crossWitness_route_of_psiHatOwner_ne_one
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (L : OwnerSourceTransportLedger C)
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    [DecidableRel (A \ T).Adj]
    (R X U : Finset V) (t : V → ZMod 2)
    (delta : Bool → V → ZMod 2)
    (hdecomp : ∀ owner,
      L.psiHatOwner owner = 1 + ∑ g ∈ R, delta owner g)
    (hzero : ∀ g ∈ R, delta false g + delta true g = 0)
    (hdeltaActivity : ∀ g ∈ R,
      delta false g = ∑ u ∈ A.neighborFinset g ∩ X, t u)
    (heven : ∀ g ∈ R, Even (A.neighborFinset g ∩ X).card)
    (hTconst : ∀ g ∈ R, ∀ u, u ∈ A.neighborFinset g ∩ X →
      T.Adj g u → t u = t g)
    (starMate : V → V → V)
    (hfree : ¬ containsC4 V A)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (starMate w v))
    (hinvol : ∀ w v, A.Adj w v → starMate w (starMate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → starMate w v ≠ v)
    (pair : (Σ _ : {u : V // u ∈ U}, V) →
      (Σ _ : {u : V // u ∈ U}, V))
    (segment : ∀ o, o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U →
      ((witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed).induce (↑U : Set V)).Walk o.1 (pair o).1)
    (hpairClosed : ∀ o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U,
      pair o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U)
    (hpairInv : ∀ o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U, pair (pair o) = o)
    (hpairFree : ∀ o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U, pair o ≠ o)
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hprice : ∀ o (ho : o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U),
      f2WalkWeight (shoreRestrictedF2EdgePrice k (↑U : Set V))
          (segment o ho) = lam o.1.1 + lam (pair o).1.1)
    (hblock :
      Odd (labeledOccurrenceBlock
        (shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U)
        (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U) R).card ↔
      (((∑ g ∈ R,
        ((binaryVertexCutGraph (A \ T)
          (f2PotentialSupport t)).neighborFinset g ∩ X).card : ℕ) :
            ZMod 2) ≠ 0))
    (hpsi : L.psiHatOwner ≠ (fun _ : Bool => 1)) :
    ∃ (o : Σ _ : {u : V // u ∈ U}, V)
      (ho : o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U),
      pair o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U ∧
      fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U o ∈ R ∧
      fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U (pair o) ∉ R ∧
      f2WalkWeight (shoreRestrictedF2EdgePrice k (↑U : Set V))
          (segment o ho) = lam o.1.1 + lam (pair o).1.1 ∧
      (A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed U o) o.1.1 ∧
        A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed U o) o.2) ∧
      (A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed U (pair o)) (pair o).1.1 ∧
        A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed U (pair o)) (pair o).2) := by
  have hcut :
      (((∑ g ∈ R,
        ((binaryVertexCutGraph (A \ T)
          (f2PotentialSupport t)).neighborFinset g ∩ X).card : ℕ) :
            ZMod 2) ≠ 0) := by
    intro hcutZero
    apply hpsi
    exact (psiHatOwner_eq_one_iff_triangleEdgeCutResidual_eq_zero
      L A T R X t delta hdecomp hzero hdeltaActivity heven hTconst).2
      hcutZero
  exact exists_priced_crossWitness_route_of_odd_labeledOccurrenceBlock
    A hfree starMate hclosed hinvol hfixed U R pair segment hpairClosed
      hpairInv hpairFree k lam hprice (hblock.2 hcut)

end

end Erdos85

#print axioms Erdos85.exists_priced_crossWitness_route_of_psiHatOwner_ne_one

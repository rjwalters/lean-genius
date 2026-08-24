import Proofs.Erdos85OwnerLedgerOddResidualPricedRoute
import Proofs.Erdos85RelayOccurrenceBlockNeighborStarEquiv

/-!
# Canonical residual occurrence parity on the support shore

When every neighbor of a residual full center is ordinary, the canonical
full-relay occurrence block over the binary-potential shore has exactly the
literal triangle-edge residual parity.  This discharges the abstract block
identification in the owner-failure route export.
-/

open SimpleGraph

namespace Erdos85

open OwnerSourceTransportLedger

noncomputable section

/-- Labeled full-relay occurrences over the support shore are odd exactly
when the literal residual `(A \ T)` support-cut incidence is nonzero in
`ZMod 2`. -/
theorem odd_labeled_fullRelaySupportOccurrenceBlock_iff_triangleCutResidual_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    [DecidableRel (A \ T).Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (R X : Finset V) (t : V → ZMod 2)
    (hcover : ∀ g ∈ R, A.neighborFinset g ⊆ X)
    (heven : ∀ g ∈ R, Even (A.neighborFinset g ∩ X).card)
    (hTconst : ∀ g ∈ R, ∀ u, u ∈ A.neighborFinset g ∩ X →
      T.Adj g u → t u = t g) :
    Odd (labeledOccurrenceBlock
      (shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed)
          (f2PotentialSupport t))
      (fullRelayShoreOccurrenceWitness A hfree mate
        hclosed hinvol hfixed (f2PotentialSupport t)) R).card ↔
      (((∑ g ∈ R,
        ((binaryVertexCutGraph (A \ T)
          (f2PotentialSupport t)).neighborFinset g ∩ X).card : ℕ) :
            ZMod 2) ≠ 0) := by
  rw [labeled_fullRelayShoreOccurrenceBlock_card_eq_sum_neighborStarFlip
    A hfree mate hclosed hinvol hfixed (f2PotentialSupport t) R,
    odd_sum_neighborStarFlipRepresentatives_iff_odd_activityMass
      A mate hclosed hinvol hfixed R (f2PotentialSupport t)]
  have hsupportActivity :
      (((∑ g ∈ R,
        (A.neighborFinset g ∩ f2PotentialSupport t).card : ℕ) : ZMod 2)) =
        ∑ g ∈ R, ∑ u ∈ A.neighborFinset g ∩ X, t u := by
    calc
      (((∑ g ∈ R,
          (A.neighborFinset g ∩ f2PotentialSupport t).card : ℕ) : ZMod 2)) =
          ∑ g ∈ R,
            ((A.neighborFinset g ∩ f2PotentialSupport t).card : ZMod 2) := by
              simp
      _ = ∑ g ∈ R, ∑ u ∈ A.neighborFinset g, t u := by
        apply Finset.sum_congr rfl
        intro g _
        rw [f2Potential_neighborSupport_card_cast,
          SimpleGraph.adjMatrix_mulVec_apply]
      _ = ∑ g ∈ R, ∑ u ∈ A.neighborFinset g ∩ X, t u := by
        apply Finset.sum_congr rfl
        intro g hg
        congr 1
        ext u
        simp only [Finset.mem_inter]
        exact ⟨fun hu => ⟨hu, hcover g hg hu⟩, And.left⟩
  have hactivityCut :
      (∑ g ∈ R, ∑ u ∈ A.neighborFinset g ∩ X, t u) =
      (((∑ g ∈ R,
        ((binaryVertexCutGraph (A \ T)
          (f2PotentialSupport t)).neighborFinset g ∩ X).card : ℕ) :
            ZMod 2)) := by
    calc
      (∑ g ∈ R, ∑ u ∈ A.neighborFinset g ∩ X, t u) =
          ∑ g ∈ R,
            (((binaryVertexCutGraph (A \ T)
              (f2PotentialSupport t)).neighborFinset g ∩ X).card :
                ZMod 2) := by
        apply Finset.sum_congr rfl
        intro g hg
        exact sum_f2_neighbor_inter_eq_triangleEdgeCutGraph_neighbor_inter_card
          A T X t g (heven g hg) (hTconst g hg)
      _ = (((∑ g ∈ R,
          ((binaryVertexCutGraph (A \ T)
            (f2PotentialSupport t)).neighborFinset g ∩ X).card : ℕ) :
              ZMod 2)) := by simp
  rw [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even,
    hsupportActivity, hactivityCut]

/-- **Canonical owner-failure route export.**  On the binary-potential shore,
the concrete residual geometry discharges the occurrence-block parity
interface automatically.  Thus failure of the corrected owner terminal
produces an actual priced relay segment leaving the residual witness block. -/
theorem exists_canonical_priced_crossWitness_route_of_psiHatOwner_ne_one
    {C V : Type*} [DecidableEq C] [Fintype V] [DecidableEq V]
    (L : OwnerSourceTransportLedger C)
    (A T : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel T.Adj]
    [DecidableRel (A \ T).Adj]
    (R X : Finset V) (t : V → ZMod 2)
    (delta : Bool → V → ZMod 2)
    (hdecomp : ∀ owner,
      L.psiHatOwner owner = 1 + ∑ g ∈ R, delta owner g)
    (hzero : ∀ g ∈ R, delta false g + delta true g = 0)
    (hdeltaActivity : ∀ g ∈ R,
      delta false g = ∑ u ∈ A.neighborFinset g ∩ X, t u)
    (hcover : ∀ g ∈ R, A.neighborFinset g ⊆ X)
    (heven : ∀ g ∈ R, Even (A.neighborFinset g ∩ X).card)
    (hTconst : ∀ g ∈ R, ∀ u, u ∈ A.neighborFinset g ∩ X →
      T.Adj g u → t u = t g)
    (starMate : V → V → V)
    (hfree : ¬ containsC4 V A)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (starMate w v))
    (hinvol : ∀ w v, A.Adj w v → starMate w (starMate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → starMate w v ≠ v)
    (pair : (Σ _ : {u : V // u ∈ f2PotentialSupport t}, V) →
      (Σ _ : {u : V // u ∈ f2PotentialSupport t}, V))
    (segment : ∀ o, o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) (f2PotentialSupport t) →
      ((witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed).induce
          (↑(f2PotentialSupport t) : Set V)).Walk o.1 (pair o).1)
    (hpairClosed : ∀ o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) (f2PotentialSupport t),
      pair o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) (f2PotentialSupport t))
    (hpairInv : ∀ o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) (f2PotentialSupport t), pair (pair o) = o)
    (hpairFree : ∀ o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) (f2PotentialSupport t), pair o ≠ o)
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hprice : ∀ o (ho : o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) (f2PotentialSupport t)),
      f2WalkWeight (shoreRestrictedF2EdgePrice k
          (↑(f2PotentialSupport t) : Set V))
          (segment o ho) = lam o.1.1 + lam (pair o).1.1)
    (hpsi : L.psiHatOwner ≠ (fun _ : Bool => 1)) :
    ∃ (o : Σ _ : {u : V // u ∈ f2PotentialSupport t}, V)
      (ho : o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) (f2PotentialSupport t)),
      pair o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) (f2PotentialSupport t) ∧
      fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed (f2PotentialSupport t) o ∈ R ∧
      fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed (f2PotentialSupport t) (pair o) ∉ R ∧
      f2WalkWeight (shoreRestrictedF2EdgePrice k
          (↑(f2PotentialSupport t) : Set V))
          (segment o ho) = lam o.1.1 + lam (pair o).1.1 ∧
      (A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed (f2PotentialSupport t) o) o.1.1 ∧
        A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed (f2PotentialSupport t) o) o.2) ∧
      (A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed (f2PotentialSupport t) (pair o))
          (pair o).1.1 ∧
        A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
            hclosed hinvol hfixed (f2PotentialSupport t) (pair o))
          (pair o).2) := by
  apply exists_priced_crossWitness_route_of_psiHatOwner_ne_one
    L A T R X (f2PotentialSupport t) t delta hdecomp hzero hdeltaActivity
      heven hTconst starMate hfree hclosed hinvol hfixed pair segment
      hpairClosed hpairInv hpairFree k lam hprice
  · exact odd_labeled_fullRelaySupportOccurrenceBlock_iff_triangleCutResidual_ne_zero
      A T hfree starMate hclosed hinvol hfixed R X t hcover heven hTconst
  · exact hpsi

end

end Erdos85

#print axioms Erdos85.odd_labeled_fullRelaySupportOccurrenceBlock_iff_triangleCutResidual_ne_zero
#print axioms Erdos85.exists_canonical_priced_crossWitness_route_of_psiHatOwner_ne_one

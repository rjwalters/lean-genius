import Proofs.Erdos85RelayCutWitnessBoundaryParity
import Proofs.Erdos85ShoreSegmentPotentialPrice

/-!
# Priced cross-witness routing on a full-relay shore

The residual witness character is not removable by re-pairing inside one
star.  This file packages the genuinely cross-witness object: paired cut
occurrences have canonical witness labels, their label-block boundary has
the correct parity, and their internal shore segments have endpoint-
potential price in the additive branch.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Canonical full-relay witness label on the dependent occurrence type of
a vertex shore. -/
def fullRelayShoreOccurrenceWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (U : Finset V) (o : Σ _ : {u : V // u ∈ U}, V) : V :=
  fullRelayOccurrenceWitness A hfree mate hclosed hinvol hfixed
    ⟨o.1.1, o.2⟩

/-- **Priced residual witness boundary.**  On a preconnected shore of an
even full relay, one can pair every outgoing occurrence by an internal
segment so that (i) witness-block occurrence parity is exactly the parity
of cross-witness segments leaving the block, and (ii) every segment price
is the sum of its endpoint potentials. -/
theorem exists_fullRelay_shore_pairing_witnessBoundary_and_price
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (starMate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (starMate w v))
    (hinvol : ∀ w v, A.Adj w v → starMate w (starMate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → starMate w v ≠ v)
    (hdegree : ∀ v, Even ((witnessPairingRelayGraph A.Adj starMate
      hclosed hinvol hfixed).degree v))
    (U R : Finset V)
    (hconn : ((witnessPairingRelayGraph A.Adj starMate
      hclosed hinvol hfixed).induce (↑U : Set V)).Preconnected)
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hpotential : ∀ {u v},
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed).Adj u v →
      k u v = lam u + lam v) :
    ∃ (pair : (Σ _ : {u : V // u ∈ U}, V) →
        (Σ _ : {u : V // u ∈ U}, V))
      (segment : ∀ o, o ∈ shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U →
        ((witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed).induce (↑U : Set V)).Walk o.1 (pair o).1),
      (∀ o ∈ shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U,
        pair o ∈ shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U) ∧
      (∀ o ∈ shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U,
        pair (pair o) = o) ∧
      (∀ o ∈ shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U,
        pair o ≠ o) ∧
      (Odd (labeledOccurrenceBlock
        (shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U)
        (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U) R).card ↔
       Odd (labeledPairBoundaryRepresentatives pair
        (shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U)
        (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U) R).card) ∧
      ∀ o (ho : o ∈ shoreGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj starMate
            hclosed hinvol hfixed) U),
        f2WalkWeight (shoreRestrictedF2EdgePrice k (↑U : Set V))
            (segment o ho) =
          lam o.1.1 + lam (pair o).1.1 := by
  obtain ⟨pair, segment, hpairClosed, hpairInv, hpairFree⟩ :=
    exists_shoreGraphCut_pairing_with_internalSegments
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) hdegree U hconn
  refine ⟨pair, segment, hpairClosed, hpairInv, hpairFree, ?_, ?_⟩
  · exact odd_labeledOccurrenceBlock_iff_odd_boundaryRepresentatives
      pair (shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U)
      (fullRelayShoreOccurrenceWitness A hfree starMate
        hclosed hinvol hfixed U) R
      hpairClosed hpairInv hpairFree
  · exact pairedShoreSegment_price_eq_endpointPotentialSum
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U pair segment k lam hpotential

end

end Erdos85

#print axioms Erdos85.exists_fullRelay_shore_pairing_witnessBoundary_and_price

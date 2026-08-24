import Proofs.Erdos85RelayWitnessBoundaryEndpointGeometry

/-!
# Owner-resolved priced cross-witness boundary

This is the complete routing interface available before the final source
transport identity.  One pairing simultaneously retains witness-block
parity, genuine shore segments, additive endpoint prices, and the two-pole
owner alternative.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Owner-resolved cross-witness capstone.**  Two marked pole crossings in
a preconnected shore of an even full relay admit one common pairing with:

* the residual witness-block boundary parity;
* exact endpoint-potential price on every internal segment;
* either a direct cross-owner through, or two injective ordinary exits;
* the corresponding endpoint-potential formula for both owner segments.
-/
theorem exists_ownerResolved_priced_fullRelay_witnessBoundary
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
    (pole : Bool → (Σ _ : {u : V // u ∈ U}, V))
    (hpole : ∀ owner, pole owner ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U)
    (hpoles : Function.Injective pole)
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hpotential : ∀ {u v},
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed).Adj u v →
      k u v = lam u + lam v) :
    let P := witnessPairingRelayGraph A.Adj starMate
      hclosed hinvol hfixed
    ∃ (pair : (Σ _ : {u : V // u ∈ U}, V) →
        (Σ _ : {u : V // u ∈ U}, V))
      (segment : ∀ o, o ∈ shoreGraphCutOccurrences P U →
        (P.induce (↑U : Set V)).Walk o.1 (pair o).1),
      (∀ o ∈ shoreGraphCutOccurrences P U,
        pair o ∈ shoreGraphCutOccurrences P U) ∧
      (∀ o ∈ shoreGraphCutOccurrences P U, pair (pair o) = o) ∧
      (∀ o ∈ shoreGraphCutOccurrences P U, pair o ≠ o) ∧
      (Odd (labeledOccurrenceBlock (shoreGraphCutOccurrences P U)
        (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U) R).card ↔
       Odd (labeledPairBoundaryRepresentatives pair
        (shoreGraphCutOccurrences P U)
        (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U) R).card) ∧
      (∀ o (ho : o ∈ shoreGraphCutOccurrences P U),
        f2WalkWeight (shoreRestrictedF2EdgePrice k (↑U : Set V))
            (segment o ho) = lam o.1.1 + lam (pair o).1.1) ∧
      (pair (pole false) = pole true ∨
        (Function.Injective (twoPoleOwnerExit pair pole) ∧
          ∀ owner, twoPoleOwnerExit pair pole owner ∈
            twoPoleOrdinaryOccurrences (shoreGraphCutOccurrences P U)
              (pole false) (pole true))) ∧
      ∀ owner,
        f2WalkWeight (shoreRestrictedF2EdgePrice k (↑U : Set V))
            (segment (pole owner) (hpole owner)) =
          lam (pole owner).1.1 +
            lam (twoPoleOwnerExit pair pole owner).1.1 := by
  dsimp only
  obtain ⟨pair, segment, hpairClosed, hpairInv, hpairFree,
      hboundary, hprice⟩ :=
    exists_fullRelay_shore_pairing_witnessBoundary_and_price
      A hfree starMate hclosed hinvol hfixed hdegree U R hconn
      k lam hpotential
  have hroute := twoPoleOwnerExit_crossOwner_or_injective_ordinary
    pair (shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U)
    pole hpole hpoles hpairClosed hpairInv hpairFree
  refine ⟨pair, segment, hpairClosed, hpairInv, hpairFree,
    hboundary, hprice, hroute, ?_⟩
  intro owner
  exact hprice (pole owner) (hpole owner)

end

end Erdos85

#print axioms Erdos85.exists_ownerResolved_priced_fullRelay_witnessBoundary

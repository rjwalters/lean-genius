import Proofs.Erdos85OwnerResolvedPricedWitnessBoundary

/-!
# An odd witness block produces a concrete priced cross route

The witness-block handshake is upgraded from a cardinal parity assertion to
an actual paired shore segment leaving the block, with its endpoint price
and ambient witness geometry retained.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Odd parity in a witness-labeled relay cut forces one concrete segment
whose canonical witness labels lie on opposite sides of `R`. -/
theorem exists_priced_crossWitness_route_of_odd_labeledOccurrenceBlock
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (starMate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (starMate w v))
    (hinvol : ∀ w v, A.Adj w v → starMate w (starMate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → starMate w v ≠ v)
    (U R : Finset V)
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
    (hodd : Odd (labeledOccurrenceBlock
      (shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U)
      (fullRelayShoreOccurrenceWitness A hfree starMate
        hclosed hinvol hfixed U) R).card) :
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
  let S := shoreGraphCutOccurrences
    (witnessPairingRelayGraph A.Adj starMate hclosed hinvol hfixed) U
  let label := fullRelayShoreOccurrenceWitness A hfree starMate
    hclosed hinvol hfixed U
  let B := labeledPairBoundaryRepresentatives pair S label R
  have hoddB : Odd B.card :=
    (odd_labeledOccurrenceBlock_iff_odd_boundaryRepresentatives
      pair S label R hpairClosed hpairInv hpairFree).mp hodd
  have hBpos : 0 < B.card := by
    rcases hoddB with ⟨n, hn⟩
    omega
  obtain ⟨o, hoB⟩ := Finset.card_pos.mp hBpos
  have hgeom := fullRelay_witnessBoundaryRepresentative_endpointGeometry
    A hfree starMate hclosed hinvol hfixed U R pair hpairClosed hoB
  refine ⟨o, hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1,
    hprice o hgeom.1, hgeom.2.2.2.2.1, hgeom.2.2.2.2.2⟩

end

end Erdos85

#print axioms Erdos85.exists_priced_crossWitness_route_of_odd_labeledOccurrenceBlock

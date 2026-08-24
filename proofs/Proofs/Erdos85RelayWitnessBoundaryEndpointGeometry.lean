import Proofs.Erdos85RelayShoreWitnessPricedBoundary

/-!
# Endpoint geometry of cross-witness boundary segments

Every representative leaving a witness block remembers two actual relay-cut
edges.  Their canonical witnesses lie on opposite sides of the witness
block, and each is ambient-adjacent to both endpoints of its occurrence.
This is the concrete input expected by the owner-normal-form classifier.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An actual full-relay shore-cut occurrence has a canonical ambient
witness adjacent to both of its endpoints. -/
theorem fullRelayShoreOccurrenceWitness_adj_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (starMate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (starMate w v))
    (hinvol : ∀ w v, A.Adj w v → starMate w (starMate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → starMate w v ≠ v)
    (U : Finset V) (o : Σ _ : {u : V // u ∈ U}, V)
    (ho : o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U) :
    A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
      hclosed hinvol hfixed U o) o.1.1 ∧
    A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
      hclosed hinvol hfixed U o) o.2 := by
  have hoData := Finset.mem_sigma.mp ho
  have hn := (Finset.mem_sdiff.mp hoData.2).1
  have hP : (witnessPairingRelayGraph A.Adj starMate
      hclosed hinvol hfixed).Adj o.1.1 o.2 :=
    ((witnessPairingRelayGraph A.Adj starMate
      hclosed hinvol hfixed).mem_neighborFinset o.1.1 o.2).mp hn
  simpa only [fullRelayShoreOccurrenceWitness] using
    fullRelayOccurrenceWitness_adj_endpoints A hfree starMate
      hclosed hinvol hfixed ⟨o.1.1, o.2⟩ hP

/-- **Cross-witness endpoint geometry.**  A boundary representative has an
`R`-witness on its own occurrence and a non-`R` witness on the paired
occurrence, with both ambient star incidences exposed. -/
theorem fullRelay_witnessBoundaryRepresentative_endpointGeometry
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
    (hpairClosed : ∀ o ∈ shoreGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj starMate
        hclosed hinvol hfixed) U,
      pair o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U)
    {o : Σ _ : {u : V // u ∈ U}, V}
    (ho : o ∈ labeledPairBoundaryRepresentatives pair
      (shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U)
      (fullRelayShoreOccurrenceWitness A hfree starMate
        hclosed hinvol hfixed U) R) :
    o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U ∧
    pair o ∈ shoreGraphCutOccurrences
        (witnessPairingRelayGraph A.Adj starMate
          hclosed hinvol hfixed) U ∧
    fullRelayShoreOccurrenceWitness A hfree starMate
        hclosed hinvol hfixed U o ∈ R ∧
    fullRelayShoreOccurrenceWitness A hfree starMate
        hclosed hinvol hfixed U (pair o) ∉ R ∧
    (A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U o) o.1.1 ∧
      A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U o) o.2) ∧
    (A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U (pair o)) (pair o).1.1 ∧
      A.Adj (fullRelayShoreOccurrenceWitness A hfree starMate
          hclosed hinvol hfixed U (pair o)) (pair o).2) := by
  simp only [labeledPairBoundaryRepresentatives, Finset.mem_filter] at ho
  have hpairMem := hpairClosed o ho.1
  exact ⟨ho.1, hpairMem, ho.2.1, ho.2.2,
    fullRelayShoreOccurrenceWitness_adj_endpoints A hfree starMate
      hclosed hinvol hfixed U o ho.1,
    fullRelayShoreOccurrenceWitness_adj_endpoints A hfree starMate
      hclosed hinvol hfixed U (pair o) hpairMem⟩

end

end Erdos85

#print axioms Erdos85.fullRelayShoreOccurrenceWitness_adj_endpoints
#print axioms Erdos85.fullRelay_witnessBoundaryRepresentative_endpointGeometry

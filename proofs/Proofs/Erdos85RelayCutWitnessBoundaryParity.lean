import Proofs.Erdos85CanonicalBaerRelayEdgeWitness
import Proofs.Erdos85EulerianComponentCutOwnerRouting
import Proofs.Erdos85LabeledInvolutionBoundaryParity

/-!
# Witness-block boundary parity on actual relay cuts

This instantiates the abstract labeled-involution handshake on the concrete
oriented cut occurrences of a full neighbor-star relay.  It is the formal
occurrence-level version of `(73rnz_cjibkzj)--(73rnz_cjibkzk)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Canonical relay witness label of an oriented vertex pair.  The fallback
value is irrelevant off the relay edge relation, but makes the label total
on the occurrence ambient type. -/
def fullRelayOccurrenceWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (o : Σ _ : V, V) : V :=
  if hP : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).Adj o.1 o.2 then
    fullRelayEdgeWitness A hfree mate hclosed hinvol hfixed
      ⟨s(o.1, o.2), by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hP⟩
  else o.1

/-- On an actual relay edge, the occurrence label is adjacent in `A` to
both oriented endpoints. -/
theorem fullRelayOccurrenceWitness_adj_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (o : Σ _ : V, V)
    (hP : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).Adj o.1 o.2) :
    A.Adj (fullRelayOccurrenceWitness A hfree mate
      hclosed hinvol hfixed o) o.1 ∧
    A.Adj (fullRelayOccurrenceWitness A hfree mate
      hclosed hinvol hfixed o) o.2 := by
  let e : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).edgeFinset :=
    ⟨s(o.1, o.2), by
      simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hP⟩
  have hs := fullRelayEdgeWitness_spec A hfree mate
    hclosed hinvol hfixed e
  have hfirst : A.Adj
      (fullRelayEdgeWitness A hfree mate hclosed hinvol hfixed e) o.1 := by
    apply hs o.1
    simp [e, Sym2.toFinset_mk_eq]
  have hsecond : A.Adj
      (fullRelayEdgeWitness A hfree mate hclosed hinvol hfixed e) o.2 := by
    apply hs o.2
    simp [e, Sym2.toFinset_mk_eq]
  simpa only [fullRelayOccurrenceWitness, dif_pos hP] using
    And.intro hfirst hsecond

/-- **Residual witness-block handshake (73rnz_cjibkzk).**  In an even
full-relay component cut, choose a pairing of actual cut occurrences.  For
every witness block `R`, the parity of occurrences labeled in `R` equals
the parity of paired segments with exactly one witness label in `R`. -/
theorem exists_fullRelay_componentCut_pairing_witnessBoundaryParity
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A)
    (mate : V → V → V)
    (hclosed : ∀ w v, A.Adj w v → A.Adj w (mate w v))
    (hinvol : ∀ w v, A.Adj w v → mate w (mate w v) = v)
    (hfixed : ∀ w v, A.Adj w v → mate w v ≠ v)
    (hdegree : ∀ v, Even ((witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).degree v))
    (c : (witnessPairingRelayGraph A.Adj mate
      hclosed hinvol hfixed).ConnectedComponent)
    (S R : Finset V) :
    ∃ pair : (Σ _ : V, V) → (Σ _ : V, V),
      (∀ o ∈ componentGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) c S,
        pair o ∈ componentGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) c S) ∧
      (∀ o ∈ componentGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) c S,
        pair (pair o) = o) ∧
      (∀ o ∈ componentGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) c S,
        pair o ≠ o) ∧
      (Odd (labeledOccurrenceBlock
        (componentGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) c S)
        (fullRelayOccurrenceWitness A hfree mate hclosed hinvol hfixed) R).card ↔
       Odd (labeledPairBoundaryRepresentatives pair
        (componentGraphCutOccurrences
          (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) c S)
        (fullRelayOccurrenceWitness A hfree mate hclosed hinvol hfixed) R).card) := by
  obtain ⟨pair, hpairClosed, hpairInv, hpairFree⟩ :=
    exists_componentGraphCutOccurrence_pairing_of_even_degree
      (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed)
      hdegree c S
  refine ⟨pair, hpairClosed, hpairInv, hpairFree, ?_⟩
  exact odd_labeledOccurrenceBlock_iff_odd_boundaryRepresentatives
    pair (componentGraphCutOccurrences
      (witnessPairingRelayGraph A.Adj mate hclosed hinvol hfixed) c S)
    (fullRelayOccurrenceWitness A hfree mate hclosed hinvol hfixed) R
    hpairClosed hpairInv hpairFree

end

end Erdos85

#print axioms Erdos85.fullRelayOccurrenceWitness_adj_endpoints
#print axioms Erdos85.exists_fullRelay_componentCut_pairing_witnessBoundaryParity

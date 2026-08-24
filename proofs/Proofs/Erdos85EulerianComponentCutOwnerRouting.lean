import Proofs.Erdos85EulerianComponentCutParity
import Proofs.Erdos85EvenFinsetPairing

/-!
# Owner routing on concrete component-cut occurrences

The component cut mass was initially stated as a sum of neighbor counts.
Here it is realized as an actual dependent finset of oriented cut
occurrences.  Its cardinality is definitionally the cut mass, so Eulerian
component parity constructs the fixed-point-free pairing used by the
two-pole owner-routing alternative.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Oriented cut occurrences in a connected component.  The first
coordinate is the unique endpoint on `S` and in `c`; the second coordinate
is its neighbor outside `S`. -/
def componentGraphCutOccurrences
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : H.ConnectedComponent) (S : Finset V) : Finset (Σ _ : V, V) :=
  (S ∩ connectedComponentFinset c).sigma fun u => H.neighborFinset u \ S

@[simp] theorem componentGraphCutOccurrences_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : H.ConnectedComponent) (S : Finset V) :
    (componentGraphCutOccurrences H c S).card =
      componentGraphCutMass H c S := by
  simp [componentGraphCutOccurrences, componentGraphCutMass]

/-- Every component cut of a finite even-degree graph admits an occurrence
pairing.  This turns `(73rnz_cjibkp)` from a count parity statement into the
pairing object needed for owner routing. -/
theorem exists_componentGraphCutOccurrence_pairing_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, Even (H.degree v))
    (c : H.ConnectedComponent) (S : Finset V) :
    ∃ mate : (Σ _ : V, V) → (Σ _ : V, V),
      (∀ o ∈ componentGraphCutOccurrences H c S,
        mate o ∈ componentGraphCutOccurrences H c S) ∧
      (∀ o ∈ componentGraphCutOccurrences H c S, mate (mate o) = o) ∧
      (∀ o ∈ componentGraphCutOccurrences H c S, mate o ≠ o) := by
  apply exists_closed_fixedPointFree_involution_of_even_card
  rw [componentGraphCutOccurrences_card]
  exact even_componentGraphCutMass_of_even_degree H hdegree c S

/-- **Concrete component-cut owner routing.**  If two distinct pole
crossings lie in one Eulerian component cut, there is a pairing of all its
actual oriented cut occurrences for which the poles either pair directly,
or launch two distinct owner-indexed ordinary exits. -/
theorem exists_componentGraphCut_pairing_with_twoPoleOwnerRouting
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, Even (H.degree v))
    (c : H.ConnectedComponent) (S : Finset V)
    (pole : Bool → (Σ _ : V, V))
    (hpole : ∀ owner, pole owner ∈ componentGraphCutOccurrences H c S)
    (hpoles : Function.Injective pole) :
    ∃ mate : (Σ _ : V, V) → (Σ _ : V, V),
      (∀ o ∈ componentGraphCutOccurrences H c S,
        mate o ∈ componentGraphCutOccurrences H c S) ∧
      (∀ o ∈ componentGraphCutOccurrences H c S, mate (mate o) = o) ∧
      (∀ o ∈ componentGraphCutOccurrences H c S, mate o ≠ o) ∧
      (mate (pole false) = pole true ∨
        (Function.Injective (twoPoleOwnerExit mate pole) ∧
          ∀ owner, twoPoleOwnerExit mate pole owner ∈
            twoPoleOrdinaryOccurrences (componentGraphCutOccurrences H c S)
              (pole false) (pole true))) := by
  apply exists_pairing_with_twoPoleOwnerRoutingAlternative
  · rw [componentGraphCutOccurrences_card]
    exact even_componentGraphCutMass_of_even_degree H hdegree c S
  · exact hpole
  · exact hpoles

end

end Erdos85

#print axioms Erdos85.componentGraphCutOccurrences_card
#print axioms Erdos85.exists_componentGraphCutOccurrence_pairing_of_even_degree
#print axioms Erdos85.exists_componentGraphCut_pairing_with_twoPoleOwnerRouting

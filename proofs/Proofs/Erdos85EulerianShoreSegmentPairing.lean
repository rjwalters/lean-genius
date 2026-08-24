import Proofs.Erdos85EulerianComponentCutOwnerRouting

/-!
# Pairing Eulerian cut crossings by same-shore segments

For a vertex shore `U`, orient each crossing from its endpoint in `U` to
the endpoint outside `U`.  If the induced graph on `U` is preconnected,
then any pairing of these crossings can be realized by walks wholly inside
`U`.  Eulerian cut parity supplies the pairing.  This turns the abstract
owner-occurrence routing into genuine paired-star graph segments.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Outgoing oriented cut occurrences of a vertex shore.  The dependent
first coordinate remembers, by type, that the inside endpoint lies in `U`. -/
def shoreGraphCutOccurrences
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) :
    Finset (Σ _ : {u : V // u ∈ U}, V) :=
  (Finset.univ : Finset {u : V // u ∈ U}).sigma fun u =>
    H.neighborFinset u.1 \ U

@[simp] theorem shoreGraphCutOccurrences_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) :
    (shoreGraphCutOccurrences H U).card = graphCutMass H U := by
  simp only [shoreGraphCutOccurrences, Finset.card_sigma, graphCutMass]
  exact Finset.sum_attach U fun u => (H.neighborFinset u \ U).card

/-- An even-degree graph pairs all crossings of a preconnected shore, and
every pair is joined by a walk in the induced shore graph. -/
theorem exists_shoreGraphCut_pairing_with_internalSegments
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, Even (H.degree v)) (U : Finset V)
    (hconn : (H.induce (↑U : Set V)).Preconnected) :
    ∃ (mate : (Σ _ : {u : V // u ∈ U}, V) →
        (Σ _ : {u : V // u ∈ U}, V))
      (_segment : ∀ o, o ∈ shoreGraphCutOccurrences H U →
        (H.induce (↑U : Set V)).Walk o.1 (mate o).1),
      (∀ o ∈ shoreGraphCutOccurrences H U,
        mate o ∈ shoreGraphCutOccurrences H U) ∧
      (∀ o ∈ shoreGraphCutOccurrences H U, mate (mate o) = o) ∧
      (∀ o ∈ shoreGraphCutOccurrences H U, mate o ≠ o) := by
  have heven : Even (shoreGraphCutOccurrences H U).card := by
    rw [shoreGraphCutOccurrences_card]
    exact even_graphCutMass_of_even_degree H hdegree U
  obtain ⟨mate, hclosed, hinvol, hfree⟩ :=
    exists_closed_fixedPointFree_involution_of_even_card
      (shoreGraphCutOccurrences H U) heven
  let segment : ∀ o, o ∈ shoreGraphCutOccurrences H U →
      (H.induce (↑U : Set V)).Walk o.1 (mate o).1 := fun o _ =>
    Classical.choice (hconn o.1 (mate o).1)
  exact ⟨mate, segment, hclosed, hinvol, hfree⟩

/-- Two marked shore crossings can be routed with retained Boolean owner
labels along genuine same-shore segments.  They either form a cross-owner
through, or terminate at two distinct ordinary crossings. -/
theorem exists_shoreGraphCut_segments_with_twoPoleOwnerRouting
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, Even (H.degree v)) (U : Finset V)
    (hconn : (H.induce (↑U : Set V)).Preconnected)
    (pole : Bool → (Σ _ : {u : V // u ∈ U}, V))
    (hpole : ∀ owner, pole owner ∈ shoreGraphCutOccurrences H U)
    (hpoles : Function.Injective pole) :
    ∃ (mate : (Σ _ : {u : V // u ∈ U}, V) →
        (Σ _ : {u : V // u ∈ U}, V))
      (_segment : ∀ o, o ∈ shoreGraphCutOccurrences H U →
        (H.induce (↑U : Set V)).Walk o.1 (mate o).1),
      (∀ o ∈ shoreGraphCutOccurrences H U,
        mate o ∈ shoreGraphCutOccurrences H U) ∧
      (∀ o ∈ shoreGraphCutOccurrences H U, mate (mate o) = o) ∧
      (∀ o ∈ shoreGraphCutOccurrences H U, mate o ≠ o) ∧
      (mate (pole false) = pole true ∨
        (Function.Injective (twoPoleOwnerExit mate pole) ∧
          ∀ owner, twoPoleOwnerExit mate pole owner ∈
            twoPoleOrdinaryOccurrences (shoreGraphCutOccurrences H U)
              (pole false) (pole true))) := by
  obtain ⟨mate, segment, hclosed, hinvol, hfree⟩ :=
    exists_shoreGraphCut_pairing_with_internalSegments H hdegree U hconn
  refine ⟨mate, segment, hclosed, hinvol, hfree, ?_⟩
  exact twoPoleOwnerExit_crossOwner_or_injective_ordinary mate
    (shoreGraphCutOccurrences H U) pole hpole hpoles hclosed hinvol hfree

end

end Erdos85

#print axioms Erdos85.shoreGraphCutOccurrences_card
#print axioms Erdos85.exists_shoreGraphCut_pairing_with_internalSegments
#print axioms Erdos85.exists_shoreGraphCut_segments_with_twoPoleOwnerRouting

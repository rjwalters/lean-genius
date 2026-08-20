import Proofs.Erdos85EdgeIndexedServiceTypeHandshake

/-! # Saturation of a common-service exterior star -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Forget the edge-finset subtype on the common-service star. -/
def incidentServiceCommonEdgeValues
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset) : Finset (Sym2 V) :=
  (incidentServiceCommonEdgeFinset R Cedge u a).image Subtype.val

/-- If the common-service star has as many edges as the full exterior
incidence star, it is that incidence star exactly. -/
theorem incidentServiceCommonEdgeValues_eq_incidenceFinset_of_card_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (u : V) (a : R.edgeFinset)
    (hcard : (incidentServiceCommonEdgeFinset R Cedge u a).card =
      R.degree u) :
    incidentServiceCommonEdgeValues R Cedge u a = R.incidenceFinset u := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp he
    have hub := (Finset.mem_filter.mp hb).2.1
    rw [R.incidenceFinset_eq_filter]
    apply Finset.mem_filter.mpr
    exact ⟨b.2, by simpa using hub⟩
  · rw [R.card_incidenceFinset_eq_degree,
      incidentServiceCommonEdgeValues,
      Finset.card_image_of_injective _ Subtype.val_injective, hcard]

/-- Six common-star edges saturate a 6-regular exterior incidence star. -/
theorem incidentServiceCommonEdgeValues_eq_incidenceFinset_of_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hRreg : ∀ x, R.degree x = 6)
    (u : V) (a : R.edgeFinset)
    (hcard : (incidentServiceCommonEdgeFinset R Cedge u a).card = 6) :
    incidentServiceCommonEdgeValues R Cedge u a = R.incidenceFinset u := by
  apply incidentServiceCommonEdgeValues_eq_incidenceFinset_of_card_degree
  simpa [hRreg u] using hcard

end

end Erdos85

#print axioms
  Erdos85.incidentServiceCommonEdgeValues_eq_incidenceFinset_of_six

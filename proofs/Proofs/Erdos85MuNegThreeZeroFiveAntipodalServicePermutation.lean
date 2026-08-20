import Proofs.Erdos85EdgeIndexedServiceCommonStarSaturation
import Proofs.Erdos85EdgeIndexedServiceMatchingLaw
import Proofs.Erdos85MuNegThreeZeroFiveCommonStarSaturation

/-! # Permutation forced by a saturated common-service star

When every exterior edge through `u` has a common service neighbor with a
fixed edge `a`, `C₄`-freeness makes that common neighbor unique.  The service
matching law makes the resulting assignment injective.
-/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Saturation of a common-service star supplies a unique common service
neighbor for each exterior edge in the full incidence star. -/
theorem incidentServiceCommonNeighbor_existsUnique_of_saturates
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : V) (a b : R.edgeFinset)
    (hsat : incidentServiceCommonEdgeValues R Cedge u a =
      R.incidenceFinset u)
    (hua : u ∉ a.1.toFinset)
    (hub : u ∈ b.1.toFinset) :
    ∃! d : R.edgeFinset, Cedge.Adj a d ∧ Cedge.Adj b d := by
  classical
  have hbInc : b.1 ∈ R.incidenceFinset u := by
    rw [R.incidenceFinset_eq_filter]
    exact Finset.mem_filter.mpr ⟨b.2, by simpa using hub⟩
  have hbVal : b.1 ∈ incidentServiceCommonEdgeValues R Cedge u a := by
    rw [hsat]
    exact hbInc
  obtain ⟨b', hb', hb'eq⟩ := Finset.mem_image.mp hbVal
  have hbb' : b' = b := Subtype.ext hb'eq
  subst b'
  have hcommon := (Finset.mem_filter.mp hb').2.2
  obtain ⟨d, hd⟩ := hcommon
  have hd' := Finset.mem_inter.mp hd
  refine ⟨d, ⟨?_, ?_⟩, ?_⟩
  · exact (Cedge.mem_neighborFinset a d).mp hd'.2
  · exact (Cedge.mem_neighborFinset b d).mp hd'.1
  · intro e he
    have hba : b ≠ a := by
      intro hba
      exact hua (hba ▸ hub)
    exact (Finset.card_le_one.mp
      (common_le_one_of_not_containsC4 hfree b a hba) d
      (Finset.mem_inter.mpr ⟨hd'.1, hd'.2⟩) e
      (Finset.mem_inter.mpr ⟨
        (Cedge.mem_neighborFinset b e).mpr he.2,
        (Cedge.mem_neighborFinset a e).mpr he.1⟩)).symm

/-- Any choice of the common service neighbor on an incidence star is
injective.  Thus, when both stars have size six, it is a six-by-six
permutation. -/
theorem incidentServiceCommonNeighbor_assignment_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : V) (a : R.edgeFinset)
    (f : R.edgeFinset → R.edgeFinset)
    (hf : ∀ b, u ∈ b.1.toFinset →
      Cedge.Adj a (f b) ∧ Cedge.Adj b (f b)) :
    Set.InjOn f {b | u ∈ b.1.toFinset} := by
  intro b hb c hc hfc
  by_contra hbc
  have hdisj := edgeIndexedService_neighborEdges_pairwiseDisjoint
    H R Cedge hservice (f b) b c
      ((Cedge.adj_comm b (f b)).mp (hf b hb).2)
      ((Cedge.adj_comm c (f b)).mp (hfc ▸ (hf c hc).2)) hbc
  rw [Finset.disjoint_left] at hdisj
  exact hdisj hb hc

/-- Concrete antipodal h305 form: every exterior edge through either eligible
nonendpoint coordinate has a unique common service neighbor with the central
antipodal edge.  Together with
`incidentServiceCommonNeighbor_assignment_injective`, this is the induced
six-by-six permutation. -/
theorem h305_antipodal_commonServiceNeighbor_existsUnique
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a b : R.edgeFinset) (i j k : ZMod 8)
    (haoffset : j - i = 4)
    (ha : a.1.toFinset = {u i, u j})
    (hk : k ∈ h305ServiceNonendpointEligibleCoordinates i j)
    (hkb : u k ∈ b.1.toFinset) :
    ∃! d : R.edgeFinset, Cedge.Adj a d ∧ Cedge.Adj b d := by
  have hki : k ≠ i :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hua : u k ∉ a.1.toFinset := by
    rw [ha]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h ↦ hki (huinj h), fun h ↦ hkj (huinj h)⟩
  apply incidentServiceCommonNeighbor_existsUnique_of_saturates
    R Cedge hfree (u k) a b
      (h305_antipodal_commonStar_saturates H R Cedge hservice hHreg hRreg
        hCreg hfree u huinj hu a i j k haoffset ha hk) hua hkb

end

end Erdos85

#print axioms Erdos85.incidentServiceCommonNeighbor_existsUnique_of_saturates
#print axioms Erdos85.incidentServiceCommonNeighbor_assignment_injective
#print axioms Erdos85.h305_antipodal_commonServiceNeighbor_existsUnique

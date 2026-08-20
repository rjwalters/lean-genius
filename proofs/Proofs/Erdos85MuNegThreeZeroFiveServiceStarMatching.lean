import Proofs.Erdos85EdgeIndexedServiceUniqueMatching
import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry

/-! # Service-star matching in an h305 cycle shore -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def h305ServiceEligibleCoordinates (i j : ZMod 8) : Finset (ZMod 8) :=
  Finset.univ.filter fun k ↦
    i ≠ k - 1 ∧ i ≠ k + 1 ∧ j ≠ k - 1 ∧ j ≠ k + 1

set_option maxRecDepth 100000 in
theorem h305ServiceEligibleCoordinates_card_four :
    ∀ i j : ZMod 8,
      (j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 5 ∨ j - i = 7) →
      (h305ServiceEligibleCoordinates i j).card = 4 := by
  native_decide

/-- For a central exterior edge with both endpoints in one labeled h305
eight-cycle, every coordinate avoiding the four cycle-neighbor positions is
carried by a unique neighboring service edge.  This statement is independent
of which corrected shore mode (`{1,4,7}` or `{3,4,5}`) supplied the central
edge; in particular the antipodal offset causes no exceptional case. -/
theorem h305_serviceStar_uniqueEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j k : ZMod 8)
    (ha : a.1.toFinset = {u i, u j})
    (hkiPred : i ≠ k - 1) (hkiSucc : i ≠ k + 1)
    (hkjPred : j ≠ k - 1) (hkjSucc : j ≠ k + 1) :
    ∃! b : R.edgeFinset, Cedge.Adj a b ∧ u k ∈ b.1.toFinset := by
  classical
  apply edgeIndexedService_unique_incidentNeighbor H R Cedge hservice (u k) a
  rw [Finset.card_eq_zero]
  ext x
  simp only [internalEndpointNeighborFinset, Finset.mem_filter]
  constructor
  · rintro ⟨hxa, hAdj⟩
    exfalso
    rw [ha] at hxa
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxa
    rcases hxa with hxi | hxj
    · subst x
      have hmem : u i ∈ H.neighborFinset (u k) :=
        (H.mem_neighborFinset (u k) (u i)).mpr hAdj
      rw [hu k] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hpred | hsucc
      · exact hkiPred (huinj hpred)
      · exact hkiSucc (huinj hsucc)
    · subst x
      have hmem : u j ∈ H.neighborFinset (u k) :=
        (H.mem_neighborFinset (u k) (u j)).mpr hAdj
      rw [hu k] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with hpred | hsucc
      · exact hkjPred (huinj hpred)
      · exact hkjSucc (huinj hsucc)
  · intro hx
    exact (Finset.notMem_empty x hx).elim

/-- Finset-facing wrapper: each of the four eligible same-shore coordinates
for a corrected h305 exterior offset has its canonical neighboring service
edge. -/
theorem h305_serviceStar_uniqueEdge_of_mem_eligible
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j k : ZMod 8)
    (ha : a.1.toFinset = {u i, u j})
    (hk : k ∈ h305ServiceEligibleCoordinates i j) :
    ∃! b : R.edgeFinset, Cedge.Adj a b ∧ u k ∈ b.1.toFinset := by
  have hk' := (Finset.mem_filter.mp hk).2
  exact h305_serviceStar_uniqueEdge H R Cedge hservice u huinj hu a i j k ha
    hk'.1 hk'.2.1 hk'.2.2.1 hk'.2.2.2

end

end Erdos85

#print axioms Erdos85.h305_serviceStar_uniqueEdge
#print axioms Erdos85.h305ServiceEligibleCoordinates_card_four

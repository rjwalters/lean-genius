import Proofs.Erdos85OrderSixtyFourOutsideCnfSemantics
import Proofs.Erdos85SizeTwoEigenlineEightEightLowExteriorModel
import Proofs.Erdos85SizeTwoUnorderedPairServiceCount

/-!
# Transporting exterior-owner clause semantics to finite coordinates

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The checked low-`8+8` owner certificate is stated on a fixed finite owner
type, while the graph-facing routing laws naturally live on the subtype of
vertices exterior to the size-two component.  This file supplies the
equivalence transport layer.  It is deliberately independent of a DIMACS
variable numbering, so the same bridge can be consumed by a regenerated or
minimized certificate.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Clause semantics are invariant under relabeling the exterior vertices.
The transported graph is the comap along the inverse equivalence, and both
incidence and target tables are relabeled by the same inverse. -/
theorem OutsideCClauseSemantics.comap_equiv
    {U E E' : Type*} [Fintype E] [Fintype E']
    (C : SimpleGraph E)
    (incident : U → E → Prop)
    (target : U → E → Nat)
    (h : OutsideCClauseSemantics C incident target)
    (e : E ≃ E') :
    OutsideCClauseSemantics (C.comap e.symm)
      (fun u z ↦ incident u (e.symm z))
      (fun u z ↦ target u (e.symm z)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u z ht f hzf huf
    exact h.zero_service u (e.symm z) ht (e.symm f) hzf huf
  · intro u z ht
    obtain ⟨f, hzf, huf⟩ := h.one_service_exists u (e.symm z) ht
    exact ⟨e f, by simpa, by simp [huf]⟩
  · intro u z ht f g hzf huf hzg hug
    apply e.symm.injective
    exact h.one_service_unique u (e.symm z) ht
      (e.symm f) (e.symm g) hzf huf hzg hug
  · intro a b c d hab hcd hac hbc had hbd
    apply h.no_two_common (e.symm a) (e.symm b) (e.symm c) (e.symm d)
    · exact fun heq => hab (e.symm.injective heq)
    · exact fun heq => hcd (e.symm.injective heq)
    · exact hac
    · exact hbc
    · exact had
    · exact hbd

/-- Ambient C4-freeness therefore supplies the complete abstract owner-CNF
semantics after any chosen finite relabeling of the exterior subtype. -/
theorem outsideCClauseSemantics_ownerCoordinates
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (e : {x : V // x ∉ c.supp} ≃ E) :
    OutsideCClauseSemantics
      ((G.induce c.suppᶜ).comap e.symm)
      (fun u z ↦ G.Adj u.1 (e.symm z).1)
      (fun u z ↦ outsideCertificateTarget G c u (e.symm z)) := by
  exact OutsideCClauseSemantics.comap_equiv
    (G.induce c.suppᶜ)
    (fun u z ↦ G.Adj u.1 z.1)
    (outsideCertificateTarget G c)
    (outsideCClauseSemantics_of_ambient G hfree c) e

end

end Erdos85

#print axioms Erdos85.OutsideCClauseSemantics.comap_equiv
#print axioms Erdos85.outsideCClauseSemantics_ownerCoordinates

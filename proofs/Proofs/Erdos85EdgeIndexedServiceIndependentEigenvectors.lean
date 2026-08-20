import Proofs.Erdos85EdgeIndexedServiceEigenvectorTransfer

/-! # Independent endpoint-sum eigenvectors of the service graph -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Two internal `-2` eigenvectors transfer to genuinely non-proportional
service `2` eigenvectors when separate exterior edges detect them. -/
theorem edgeIndexedService_two_nonproportional_eigenvectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (f g : V → ℂ)
    (hfsum : ∑ x, f x = 0) (hgsum : ∑ x, g x = 0)
    (hf : (H.adjMatrix ℂ).mulVec f = (-2 : ℂ) • f)
    (hg : (H.adjMatrix ℂ).mulVec g = (-2 : ℂ) • g)
    (a b : R.edgeFinset)
    (hfa : edgeEndpointSumVector R f a ≠ 0)
    (hga : edgeEndpointSumVector R g a = 0)
    (hgb : edgeEndpointSumVector R g b ≠ 0) :
    (Cedge.adjMatrix ℂ).mulVec (edgeEndpointSumVector R f) =
        (2 : ℂ) • edgeEndpointSumVector R f ∧
      (Cedge.adjMatrix ℂ).mulVec (edgeEndpointSumVector R g) =
        (2 : ℂ) • edgeEndpointSumVector R g ∧
      ∀ z : ℂ, edgeEndpointSumVector R g ≠
        z • edgeEndpointSumVector R f := by
  have hfeig := edgeIndexedService_eigenvector_transfer
    H R Cedge hservice f (-2) hfsum hf
  have hgeig := edgeIndexedService_eigenvector_transfer
    H R Cedge hservice g (-2) hgsum hg
  refine ⟨by simpa using hfeig, by simpa using hgeig, ?_⟩
  intro z hprop
  have ha := congrFun hprop a
  change edgeEndpointSumVector R g a =
    z * edgeEndpointSumVector R f a at ha
  rw [hga] at ha
  have hz : z = 0 := by
    rcases mul_eq_zero.mp ha.symm with hz | hzero
    · exact hz
    · exact (hfa hzero).elim
  have hb := congrFun hprop b
  change edgeEndpointSumVector R g b =
    z * edgeEndpointSumVector R f b at hb
  rw [hz, zero_mul] at hb
  exact hgb hb

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_two_nonproportional_eigenvectors

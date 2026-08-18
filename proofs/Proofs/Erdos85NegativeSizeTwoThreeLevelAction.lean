import Proofs.Erdos85ThreeLevelEigenSupportDegreeBalance

/-!
# Three-level action for a signed size-two joint line

This exposes the linear laws for `w = A s + 2 s` which are otherwise buried
inside the extreme-fibre degree-balance argument.  On the distinguished
component `w` vanishes; hence the ambient adjacency equation may be filtered
to the exterior without changing its left-hand side.
-/

open SimpleGraph Matrix

namespace Erdos85

/-- The exact exterior action laws attached to a signed size-two joint line.

For a component vertex the exterior `w`-sum is `(3 - mu) * s x`; for an
exterior vertex it is `2 * w x`.  The same theorem also records the
three-level range and vanishing on the component, so downstream finite
arguments need not reconstruct the signed-joint algebra. -/
theorem orderSixtyFour_sizeTwo_signedJoint_threeLevelAction_of_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    let w := fun x => (G.adjMatrix ℤ).mulVec s x + 2 * s x
    (∀ x, x ∈ c.supp → w x = 0) ∧
    (∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2) ∧
    (∀ x, x ∈ c.supp →
      ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∉ c.supp), w y =
        (3 - mu) * s x) ∧
    (∀ x, x ∉ c.supp →
      ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∉ c.supp), w y =
        2 * w x) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let a : V → ℤ := A.mulVec s
  let w : V → ℤ := fun x => a x + 2 * s x
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  have hA2 : ∀ x, A.mulVec a x = (7 - mu) * s x := by
    intro x
    change A.mulVec (A.mulVec s) x = _
    rw [Matrix.mulVec_mulVec s A A]
    change (((G.adjMatrix ℤ) * (G.adjMatrix ℤ)).mulVec s) x = _
    rw [binarySquare_regular_adjMatrix_sq_mulVec_apply G hfree hreg s x,
      P.sum_eq_zero, P.defectAction x]
    ring
  have hw_in : ∀ x, x ∈ c.supp → w x = 0 := by
    intro x hx
    simp only [w, a]
    rw [P.ambientAction_in x hx]
    ring
  have hw_out : ∀ x, x ∉ c.supp → w x = a x := by
    intro x hx
    simp only [w]
    rw [hs_out x hx]
    ring
  have hlevels : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2 := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact Or.inr (Or.inl (hw_in x hx))
    · rw [hw_out x hx]
      exact P.ambientAction_out x hx
  have hAw : ∀ x, ∑ y ∈ G.neighborFinset x, w y =
      (3 - mu) * s x + 2 * w x := by
    intro x
    simp only [w]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have ha : A.mulVec a x = ∑ y ∈ G.neighborFinset x, a y := by
      simp only [A]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have hs : A.mulVec s x = ∑ y ∈ G.neighborFinset x, s y := by
      simp only [A]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    rw [← ha, ← hs, hA2 x]
    simp only [a]
    ring
  have hout_eq_full : ∀ x,
      ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∉ c.supp), w y =
        ∑ y ∈ G.neighborFinset x, w y := by
    intro x
    rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset x)
      (fun y => y ∉ c.supp)]
    simp only [not_not]
    have hzero : ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ c.supp), w y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      exact hw_in y (Finset.mem_filter.mp hy).2
    rw [hzero, add_zero]
  refine ⟨hw_in, hlevels, ?_, ?_⟩
  · intro x hx
    rw [hout_eq_full x, hAw x, hw_in x hx]
    ring
  · intro x hx
    rw [hout_eq_full x, hAw x, hs_out x hx, hw_out x hx]
    ring

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_threeLevelAction_of_local

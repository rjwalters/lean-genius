import Proofs.Erdos85RestrictedOwnerCommutesInducedDefect
import Proofs.Erdos85SevenRegularNearTwinCommutingPropagation

/-! # Collision propagation to a named private pair -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem sum_signed_singletons_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℤ) (p q : V) :
    (∑ w : V, ((if w = p then 1 else 0) - (if w = q then 1 else 0)) * f w) =
      f p - f q := by
  classical
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- Named form of collision propagation.  The singleton equations identify
the exact private pair, removing the existential ambiguity from the basic
near-twin theorem. -/
theorem commutingGraph_rowCollision_propagates_to_named_privatePair
    {V : Type*} [Fintype V] [DecidableEq V]
    (D R : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel R.Adj]
    {x y p q : V}
    (hp : D.neighborFinset x \ D.neighborFinset y = {p})
    (hq : D.neighborFinset y \ D.neighborFinset x = {q})
    (hcomm : D.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * D.adjMatrix ℤ)
    (hxyRows : ∀ w : V, R.adjMatrix ℤ x w = R.adjMatrix ℤ y w) :
    ∀ z : V, R.adjMatrix ℤ p z = R.adjMatrix ℤ q z := by
  have hDrow : ∀ w : V,
      D.adjMatrix ℤ x w - D.adjMatrix ℤ y w =
        (if w = p then 1 else 0) - (if w = q then 1 else 0) := by
    intro w
    have hpiff : (w ∈ D.neighborFinset x ∧ w ∉ D.neighborFinset y) ↔ w = p := by
      rw [← Finset.mem_sdiff, hp]
      simp
    have hqiff : (w ∈ D.neighborFinset y ∧ w ∉ D.neighborFinset x) ↔ w = q := by
      rw [← Finset.mem_sdiff, hq]
      simp
    rw [SimpleGraph.adjMatrix_apply, SimpleGraph.adjMatrix_apply]
    by_cases hx : D.Adj x w <;> by_cases hy : D.Adj y w <;>
      simp_all [SimpleGraph.mem_neighborFinset]
  intro z
  have h := sparseRowDifference_of_matrix_comm
    (D.adjMatrix ℤ) (R.adjMatrix ℤ) x y p q hcomm hDrow z
  rw [sum_signed_singletons_apply
    (fun w => R.adjMatrix ℤ w z) p q] at h
  have hzero :
      (∑ w : V,
        (R.adjMatrix ℤ x w - R.adjMatrix ℤ y w) * D.adjMatrix ℤ w z) = 0 := by
    apply Finset.sum_eq_zero
    intro w _hw
    rw [hxyRows w, sub_self, zero_mul]
  rw [hzero] at h
  omega

/-- Actual order-64 restricted-owner specialization targeting a supplied
private pair in one induced defect component. -/
theorem orderSixtyFour_restrictedOwner_rowCollision_propagates_to_named_privatePair
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = 16)
    {x y p q : source.supp}
    (hp : (((secondOrderDefectGraph G).induce source.supp).neighborFinset x) \
      (((secondOrderDefectGraph G).induce source.supp).neighborFinset y) = {p})
    (hq : (((secondOrderDefectGraph G).induce source.supp).neighborFinset y) \
      (((secondOrderDefectGraph G).induce source.supp).neighborFinset x) = {q})
    (hxyRows : ∀ w : source.supp,
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ x w =
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ y w) :
    ∀ z : source.supp,
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ p z =
      (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ q z := by
  let D := (secondOrderDefectGraph G).induce source.supp
  let O := restrictedComponentOwnerGraph G source owner
  have hcommOD : O.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * O.adjMatrix ℤ :=
    orderSixtyFour_restrictedOwner_adjMatrix_comm_inducedDefect
      G hfree hreg source owner howner
  exact commutingGraph_rowCollision_propagates_to_named_privatePair
    D O hp hq hcommOD.symm hxyRows

end

end Erdos85

import Proofs.Erdos85TwoPoleKFiberAtomization
import Proofs.Erdos85OrdinaryResidualNuMuMass

/-!
# Aggregate atomization of the minimum two-pole K-fiber

This sums `(73rnz_bw)` over the support away from the unique adjacent
endpoint and proves `(73rnz_bx)`.
-/

open SimpleGraph

namespace Erdos85

/-- **Aggregate K-fiber atomization (`73rnz_bx`).** -/
theorem binaryTransportResidual_poleAction_eq_ordinaryMass_add_cubeSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    [DecidableRel (antipodalGraph A).Adj]
    [DecidableRel (triangleFreeEdgeGraph A).Adj]
    (hfree : ¬ containsC4 V A)
    {q : ℕ} (hq : Even q) (hreg : ∀ v, A.degree v = q)
    (x : V → ZMod 2) (ordinary : Finset V) (pole p : V)
    (hpX : p ∈ f2PotentialSupport x) (hpoleX : pole ∉ f2PotentialSupport x)
    (hpA : A.Adj pole p)
    (hXline : f2PotentialSupport x ∩ A.neighborFinset pole = {p})
    (htype : ∀ z ∈ (f2PotentialSupport x).erase p,
      z ∈ ordinary ↔
        z ∉ (secondOrderDefectGraph A).neighborFinset pole) :
    ((binaryTransportResidualGraph A hq hreg).adjMatrix (ZMod 2)).mulVec x pole =
      (((ordinary ∩ (f2PotentialSupport x).erase p).card : ℕ) : ZMod 2) +
        ∑ z ∈ (f2PotentialSupport x).erase p,
          (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
            A.adjMatrix (ZMod 2)) pole z := by
  classical
  let K := binaryTransportResidualGraph A hq hreg
  let X := f2PotentialSupport x
  let S := X.erase p
  have hKnotA : ¬ K.Adj pole p := by
    intro hK
    have hKA : (K ⊓ A).Adj pole p := ⟨hK, hpA⟩
    have hinf := binaryTransportResidualGraph_inf_eq_bot A hfree hq hreg
    rw [hinf] at hKA
    exact hKA
  have hKp : graphEdgeIndicator K pole p = 0 := by
    simp [graphEdgeIndicator, hKnotA]
  have hall : (∑ z ∈ X, graphEdgeIndicator K pole z) =
      (K.adjMatrix (ZMod 2)).mulVec x pole := by
    rw [sum_graphEdgeIndicator_eq_neighbor_inter_card_cast,
      f2Potential_neighborSupport_card_cast]
  have herase : (∑ z ∈ S, graphEdgeIndicator K pole z) =
      (K.adjMatrix (ZMod 2)).mulVec x pole := by
    calc
      (∑ z ∈ S, graphEdgeIndicator K pole z) =
          (∑ z ∈ S, graphEdgeIndicator K pole z) +
            graphEdgeIndicator K pole p := by rw [hKp, add_zero]
      _ = ∑ z ∈ X, graphEdgeIndicator K pole z := by
        exact Finset.sum_erase_add X (graphEdgeIndicator K pole) hpX
      _ = (K.adjMatrix (ZMod 2)).mulVec x pole := hall
  change (K.adjMatrix (ZMod 2)).mulVec x pole = _
  rw [← herase]
  calc
    (∑ z ∈ S, graphEdgeIndicator K pole z) =
        ∑ z ∈ S, ((if z ∈ ordinary then 1 else 0) +
          (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
            A.adjMatrix (ZMod 2)) pole z) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzp : z ≠ p := Finset.ne_of_mem_erase hz
      have hzX : z ∈ X := Finset.mem_of_mem_erase hz
      have hpolez : pole ≠ z := fun h => hpoleX (h ▸ hzX)
      have hnotA : ¬ A.Adj pole z := by
        intro hAz
        have : z ∈ X ∩ A.neighborFinset pole :=
          Finset.mem_inter.mpr
            ⟨hzX, (A.mem_neighborFinset pole z).mpr hAz⟩
        rw [hXline] at this
        exact hzp (Finset.mem_singleton.mp this)
      exact graphEdgeIndicator_residual_eq_ordinaryIndicator_add_cube
        A hfree hq hreg ordinary pole z hpolez hnotA (htype z hz)
    _ = (∑ z ∈ S, (if z ∈ ordinary then 1 else 0)) +
        ∑ z ∈ S, (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
          A.adjMatrix (ZMod 2)) pole z := by
      rw [Finset.sum_add_distrib]
    _ = (((ordinary ∩ S).card : ℕ) : ZMod 2) +
        ∑ z ∈ S, (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) *
          A.adjMatrix (ZMod 2)) pole z := by
      congr 1
      rw [Finset.sum_boole]
      congr 2
      ext z
      simp [and_comm]

end Erdos85

#print axioms Erdos85.binaryTransportResidual_poleAction_eq_ordinaryMass_add_cubeSum

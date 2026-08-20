import Proofs.Erdos85EightCycleCubeEntries
import Proofs.Erdos85EdgeIndexedServiceCubicCensus

/-! # Cubic endpoint budgets at antipodal exterior edges -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem eightCycle_lengthThreeWalk_card_eq_value
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (i j : ZMod 8) :
    Fintype.card {p : H.Walk (u i) (u j) | p.length = 3} =
      eightCycleCubeValue i j := by
  have hm := H.adjMatrix_pow_apply_eq_card_walk (α := ℤ) 3 (u i) (u j)
  have hpow : H.adjMatrix ℤ ^ 3 =
      H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ := by
    noncomm_ring
  rw [hpow, eightCycle_adjMatrix_cube_apply H u huinj hu] at hm
  rw [eightCycleCubeValue_eq i j]
  exact_mod_cast hm.symm

theorem eightCycleCubeValue_antipodal_sum (i j : ZMod 8) :
    eightCycleCubeValue j i + eightCycleCubeValue j (i + 4) =
      if j = i + 1 ∨ j = i + 3 ∨ j = i + 5 ∨ j = i + 7 then 4 else 0 := by
  revert i j
  native_decide

/-- An antipodal exterior edge receives four internal length-three walks
from odd-offset shore coordinates and none from even-offset coordinates. -/
theorem internalEndpointCubicWalkMass_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)}) :
    internalEndpointCubicWalkMass H R (u j) a =
      if j = i + 1 ∨ j = i + 3 ∨ j = i + 5 ∨ j = i + 7 then 4 else 0 := by
  classical
  unfold internalEndpointCubicWalkMass
  rw [ha]
  have hne : u i ≠ u (i + 4) := by
    apply huinj.ne
    intro h
    have h' : (0 : ZMod 8) = 4 := by
      apply add_left_cancel (a := i)
      simpa using h
    exact (by native_decide : (0 : ZMod 8) ≠ 4) h'
  rw [← Finset.sum_filter]
  have hfilter : (Finset.univ.filter fun x : V =>
      x ∈ ({u i, u (i + 4)} : Finset V)) = {u i, u (i + 4)} := by
    ext x
    simp
  change (∑ x ∈ Finset.univ.filter (fun x : V =>
      x ∈ ({u i, u (i + 4)} : Finset V)),
        Fintype.card {p : H.Walk (u j) x | p.length = 3}) = _
  rw [hfilter, Finset.sum_pair hne,
    eightCycle_lengthThreeWalk_card_eq_value H u huinj hu,
    eightCycle_lengthThreeWalk_card_eq_value H u huinj hu,
    eightCycleCubeValue_antipodal_sum]

/-- The cubic service census therefore gives the exact complementary
incident-service budgets `24` and `28`. -/
theorem incidentServiceCubicWalkMass_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)}) :
    incidentServiceCubicWalkMass R Cedge (u j) a =
      if j = i + 1 ∨ j = i + 3 ∨ j = i + 5 ∨ j = i + 7 then 24 else 28 := by
  have hcensus := edgeIndexedService_cubicWalkCensus
    H R Cedge hservice hHreg hCreg (u j) a
  rw [internalEndpointCubicWalkMass_antipodal H R u huinj hu a i j ha] at hcensus
  split_ifs at hcensus ⊢ <;> omega

end

end Erdos85

#print axioms Erdos85.internalEndpointCubicWalkMass_antipodal
#print axioms Erdos85.incidentServiceCubicWalkMass_antipodal

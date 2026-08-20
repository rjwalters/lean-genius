import Proofs.Erdos85EdgeIndexedServiceCubicCensus
import Proofs.Erdos85EightCycleCubeEntries

/-! # Cubic service budgets on an eight-cycle shore -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

theorem eightCycle_lengthThreeWalk_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (i j : ZMod 8) :
    Fintype.card {p : H.Walk (u i) (u j) | p.length = 3} =
      if j = i - 1 ∨ j = i + 1 then 3
      else if j = i - 3 ∨ j = i + 3 then 1 else 0 := by
  have hwalk := H.adjMatrix_pow_apply_eq_card_walk (α := ℤ) 3 (u i) (u j)
  have hcube := eightCycle_adjMatrix_cube_apply H u huinj hu i j
  have hpow :
      (H.adjMatrix ℤ * H.adjMatrix ℤ * H.adjMatrix ℤ) (u i) (u j) =
        (Fintype.card {p : H.Walk (u i) (u j) | p.length = 3} : ℤ) := by
    simpa [pow_succ, Matrix.mul_assoc] using hwalk
  rw [hpow] at hcube
  exact_mod_cast hcube

/-- If the endpoints of an exterior edge have coordinates `j,k` on one
eight-cycle shore, its internal cubic contribution at coordinate `i` is the
sum of the two explicit C8 cube values. -/
theorem internalEndpointCubicWalkMass_eq_eightCycle_values
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (i j k : ZMod 8) (hjk : j ≠ k) (a : R.edgeFinset)
    (hends : a.1.toFinset = {u j, u k}) :
    internalEndpointCubicWalkMass H R (u i) a =
      (if j = i - 1 ∨ j = i + 1 then 3
        else if j = i - 3 ∨ j = i + 3 then 1 else 0) +
      (if k = i - 1 ∨ k = i + 1 then 3
        else if k = i - 3 ∨ k = i + 3 then 1 else 0) := by
  classical
  unfold internalEndpointCubicWalkMass
  rw [hends]
  have hjk' : u j ≠ u k := huinj.ne hjk
  simp only [Finset.mem_insert, Finset.mem_singleton]
  have hsplit (x : V) :
      (if x = u j ∨ x = u k then
          Fintype.card {p : H.Walk (u i) x | p.length = 3} else 0) =
        (if x = u j then
          Fintype.card {p : H.Walk (u i) x | p.length = 3} else 0) +
        (if x = u k then
          Fintype.card {p : H.Walk (u i) x | p.length = 3} else 0) := by
    by_cases hxj : x = u j
    · subst x
      simp [hjk']
    · by_cases hxk : x = u k
      · subst x
        simp [hjk'.symm]
      · simp [hxj, hxk]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp only [Fintype.sum_ite_eq']
  rw [eightCycle_lengthThreeWalk_card H u huinj hu i j,
    eightCycle_lengthThreeWalk_card H u huinj hu i k]

/-- The corresponding exterior cubic mass is `28` minus those two explicit
cycle values. -/
theorem incidentServiceCubicWalkMass_add_eightCycle_values_eq_twentyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (i j k : ZMod 8) (hjk : j ≠ k) (a : R.edgeFinset)
    (hends : a.1.toFinset = {u j, u k}) :
    incidentServiceCubicWalkMass R Cedge (u i) a +
      ((if j = i - 1 ∨ j = i + 1 then 3
        else if j = i - 3 ∨ j = i + 3 then 1 else 0) +
      (if k = i - 1 ∨ k = i + 1 then 3
        else if k = i - 3 ∨ k = i + 3 then 1 else 0)) = 28 := by
  rw [← internalEndpointCubicWalkMass_eq_eightCycle_values
    H R u huinj hu i j k hjk a hends]
  exact edgeIndexedService_cubicWalkCensus H R Cedge hservice hHreg hCreg
    (u i) a

end

end Erdos85

#print axioms Erdos85.incidentServiceCubicWalkMass_add_eightCycle_values_eq_twentyEight

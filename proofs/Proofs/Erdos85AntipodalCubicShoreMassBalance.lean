import Proofs.Erdos85AntipodalCubicEndpointBudget
import Proofs.Erdos85EdgeIndexedServiceCubicTypeMass

/-! # Antipodal h305 cubic shore-mass balance -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
theorem h305_antipodal_cubicCoordinateBudget_sum :
    ∀ i : ZMod 8, (∑ j : ZMod 8,
      if j = i + 1 ∨ j = i + 3 ∨ j = i + 5 ∨ j = i + 7 then 24 else 28) =
      208 := by
  native_decide

/-- Across the eight vertices of the shore containing an antipodal target
edge, the incident service cubic mass is exactly `4·24 + 4·28 = 208`. -/
theorem h305_antipodal_incidentServiceCubicWalkMass_shore_sum_eq_208
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)}) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    (∑ x ∈ U, incidentServiceCubicWalkMass R Cedge x a) = 208 := by
  classical
  dsimp only
  rw [Finset.sum_image]
  · simp_rw [incidentServiceCubicWalkMass_antipodal H R Cedge hservice
      hHreg hCreg u huinj hu a i _ ha]
    exact h305_antipodal_cubicCoordinateBudget_sum i
  · intro x _ y _ hxy
    exact huinj hxy

/-- On a disjoint eight-vertex shore, vanishing internal cubic contribution
turns the pointwise cubic census into the complementary total `8·28 = 224`. -/
theorem h305_incidentServiceCubicWalkMass_other_shore_sum_eq_224
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (v : ZMod 8 → V) (hvinj : Function.Injective v)
    (a : R.edgeFinset)
    (hzero : ∀ j, internalEndpointCubicWalkMass H R (v j) a = 0) :
    let W := (Finset.univ : Finset (ZMod 8)).image v
    (∑ x ∈ W, incidentServiceCubicWalkMass R Cedge x a) = 224 := by
  classical
  dsimp only
  rw [Finset.sum_image]
  · have hpoint (j : ZMod 8) :
        incidentServiceCubicWalkMass R Cedge (v j) a = 28 := by
      have hcensus := edgeIndexedService_cubicWalkCensus
        H R Cedge hservice hHreg hCreg (v j) a
      rw [hzero j] at hcensus
      omega
    simp_rw [hpoint]
    norm_num
  · intro x _ y _ hxy
    exact hvinj hxy

/-- A length-three internal walk cannot cross two distinct connected
components.  Consequently a target edge contained in one component has zero
internal endpoint cubic mass at every coordinate of the other component. -/
theorem internalEndpointCubicWalkMass_eq_zero_of_distinct_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (e : R.edgeFinset) (i : ZMod 8)
    (he : e.1.toFinset = {u i, u (i + 4)}) (j : ZMod 8) :
    internalEndpointCubicWalkMass H R (v j) e = 0 := by
  classical
  unfold internalEndpointCubicWalkMass
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hy
  · apply (Fintype.card_eq_zero_iff.mpr ⟨?_⟩)
    rintro ⟨p, _⟩
    have hvB : v j ∈ B.supp := by
      rw [← hvrange]
      exact ⟨j, rfl⟩
    have hyA : y ∈ A.supp := by
      rw [← hurange]
      rw [he] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ⟨i, rfl⟩
      · exact ⟨i + 4, rfl⟩
    have hvcomp : H.connectedComponentMk (v j) = B :=
      (ConnectedComponent.mem_supp_iff B (v j)).mp hvB
    have hycomp : H.connectedComponentMk y = A :=
      (ConnectedComponent.mem_supp_iff A y).mp hyA
    have hreach : H.connectedComponentMk (v j) = H.connectedComponentMk y :=
      ConnectedComponent.sound p.reachable
    exact hAB (hycomp.symm.trans (hreach.symm.trans hvcomp))
  · rfl

/-- If the complementary C8 shore contributes its forced `224` cubic mass,
then an antipodal target has type-zero cubic mass exactly eight larger than
its type-two cubic mass.  This is the graph-facing specialization of the
abstract shore/complement cancellation identity. -/
theorem h305_antipodal_shoreTypeCubicWalkMass_zero_eq_two_add_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)})
    (hcomplement :
      let U := (Finset.univ : Finset (ZMod 8)).image u
      (∑ x ∈ Uᶜ, incidentServiceCubicWalkMass R Cedge x a) = 224) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    shoreTypeCubicWalkMass R Cedge U 0 a =
      shoreTypeCubicWalkMass R Cedge U 2 a + 8 := by
  classical
  dsimp only at hcomplement ⊢
  let U := (Finset.univ : Finset (ZMod 8)).image u
  change (∑ x ∈ Uᶜ, incidentServiceCubicWalkMass R Cedge x a) = 224 at hcomplement
  change shoreTypeCubicWalkMass R Cedge U 0 a =
    shoreTypeCubicWalkMass R Cedge U 2 a + 8
  have hshore :
      (∑ x ∈ U, incidentServiceCubicWalkMass R Cedge x a) = 208 :=
    h305_antipodal_incidentServiceCubicWalkMass_shore_sum_eq_208
      H R Cedge hservice hHreg hCreg u huinj hu a i ha
  have hbalance := shoreTypeCubicWalkMass_balance_of_complement_sums
    R Cedge U a 208 224 hshore hcomplement
  omega

/-- Two C8 shore images that partition the vertex set discharge the `224`
complement premise as soon as internal length-three walks do not cross the
shores. -/
theorem h305_antipodal_twoShore_shoreTypeCubicWalkMass_zero_eq_two_add_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)})
    (hpartition :
      ((Finset.univ : Finset (ZMod 8)).image u)ᶜ =
        (Finset.univ : Finset (ZMod 8)).image v)
    (hzero : ∀ j, internalEndpointCubicWalkMass H R (v j) a = 0) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    shoreTypeCubicWalkMass R Cedge U 0 a =
      shoreTypeCubicWalkMass R Cedge U 2 a + 8 := by
  apply h305_antipodal_shoreTypeCubicWalkMass_zero_eq_two_add_eight
    H R Cedge hservice hHreg hCreg u huinj hu a i ha
  dsimp only
  rw [hpartition]
  exact h305_incidentServiceCubicWalkMass_other_shore_sum_eq_224
    H R Cedge hservice hHreg hCreg v hvinj a hzero

/-- Fully component-facing version: distinct C8 components themselves imply
the cross-shore vanishing needed by the cubic type-mass balance. -/
theorem h305_antipodal_componentShoreTypeCubicWalkMass_zero_eq_two_add_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ a, Cedge.degree a = 6)
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (e : R.edgeFinset) (i : ZMod 8)
    (he : e.1.toFinset = {u i, u (i + 4)})
    (hpartition :
      ((Finset.univ : Finset (ZMod 8)).image u)ᶜ =
        (Finset.univ : Finset (ZMod 8)).image v) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    shoreTypeCubicWalkMass R Cedge U 0 e =
      shoreTypeCubicWalkMass R Cedge U 2 e + 8 := by
  apply h305_antipodal_twoShore_shoreTypeCubicWalkMass_zero_eq_two_add_eight
    H R Cedge hservice hHreg hCreg u v huinj hvinj hu e i he hpartition
  exact internalEndpointCubicWalkMass_eq_zero_of_distinct_components
    H R A B hAB u v hurange hvrange e i he

end

end Erdos85

#print axioms Erdos85.h305_antipodal_cubicCoordinateBudget_sum
#print axioms
  Erdos85.h305_antipodal_incidentServiceCubicWalkMass_shore_sum_eq_208
#print axioms
  Erdos85.h305_antipodal_shoreTypeCubicWalkMass_zero_eq_two_add_eight
#print axioms
  Erdos85.h305_antipodal_twoShore_shoreTypeCubicWalkMass_zero_eq_two_add_eight
#print axioms
  Erdos85.h305_antipodal_componentShoreTypeCubicWalkMass_zero_eq_two_add_eight

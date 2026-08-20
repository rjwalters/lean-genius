import Proofs.Erdos85AntipodalCubicShoreMassBalance
import Proofs.Erdos85CubicTypeResidualBalance
import Proofs.Erdos85MuNegThreeZeroFiveServiceShoreTypeProfiles
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # Fully wired antipodal cubic residual type balance -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every one of the three same-shore h305 service-neighbor profiles has two
more type-zero than type-two neighbors. -/
theorem h305_serviceNeighbor_typeZero_eq_typeTwo_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, u j})
    (hoffset : j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
      j - i = 5 ∨ j - i = 7) :
    let U := Finset.univ.image u
    serviceNeighborShoreTypeCount R Cedge a U 0 =
      serviceNeighborShoreTypeCount R Cedge a U 2 + 2 := by
  have hp := h305_serviceNeighbor_shoreType_profiles
    H R Cedge hservice hCreg u v huinj hvinj hu hdisj hcover
      a i j ha hoffset
  dsimp only at hp ⊢
  rcases hp with hp | hp | hp <;> omega

/-- In the actual two-component h305 geometry, an antipodal target satisfies
the residual cubic identity `Q₂ = Q₀ + 14` with no remaining arithmetic,
partition, or cross-walk hypotheses. -/
theorem h305_antipodal_component_residualTypeCubicWalkMass_two_eq_zero_add_fourteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i : ZMod 8)
    (ha : a.1.toFinset = {u i, u (i + 4)}) :
    let U := Finset.univ.image u
    residualShoreTypeCubicWalkMass R Cedge U 2 a =
      residualShoreTypeCubicWalkMass R Cedge U 0 a + 14 := by
  classical
  dsimp only
  let U : Finset V := Finset.univ.image u
  have hpartition : Uᶜ = Finset.univ.image v := by
    exact h305_shoreImages_compl_eq u v hdisj hcover
  have hmass : shoreTypeCubicWalkMass R Cedge U 0 a =
      shoreTypeCubicWalkMass R Cedge U 2 a + 8 :=
    h305_antipodal_componentShoreTypeCubicWalkMass_zero_eq_two_add_eight
      H R Cedge hservice hHreg hCreg A B hAB u v huinj hvinj
        hurange hvrange hu a i ha hpartition
  have hoffset : (i + 4) - i = (4 : ZMod 8) := by ring
  have hprofile : serviceNeighborShoreTypeCount R Cedge a U 0 =
      serviceNeighborShoreTypeCount R Cedge a U 2 + 2 := by
    apply h305_serviceNeighbor_typeZero_eq_typeTwo_add_two
      H R Cedge hservice hCreg u v huinj hvinj hu hdisj hcover
        a i (i + 4) ha
    exact Or.inr (Or.inr (Or.inl hoffset))
  exact residualShoreTypeCubicWalkMass_two_eq_zero_add_fourteen
    R Cedge hfree hCreg U a hmass hprofile

end

end Erdos85

#print axioms Erdos85.h305_serviceNeighbor_typeZero_eq_typeTwo_add_two
#print axioms
  Erdos85.h305_antipodal_component_residualTypeCubicWalkMass_two_eq_zero_add_fourteen

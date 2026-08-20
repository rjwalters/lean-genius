import Proofs.Erdos85CrossCubicMassEqualityOrientation

/-! # A sharp upper bound orients the cross-row marked matching

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the actual two-C8 service model, the universal lower bound turns a
matching upper bound `mass ≤ 550` into equality, hence into one of the two
explicit orientations of the value-five matching. -/
theorem h305_cross_mass_le_550_valueFiveEdge_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (hzeroUV : ∀ k l,
      Fintype.card {p : H.Walk (u k) (v l) | p.length = 3} = 0)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (a : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset = {u i, v j})
    (hupper : (∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 550) :
    let M := cubicValueFiveEdgeFinset R Cedge a
    (∃ b₀ b₁, M = {b₀, b₁} ∧
      b₀.1.toFinset = {u (i - 1), v (j - 1)} ∧
      b₁.1.toFinset = {u (i + 1), v (j + 1)}) ∨
    (∃ b₀ b₁, M = {b₀, b₁} ∧
      b₀.1.toFinset = {u (i - 1), v (j + 1)} ∧
      b₁.1.toFinset = {u (i + 1), v (j - 1)}) := by
  have hlower := h305_cross_cubicResidualEdge_squareMass_ge_550
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover hzeroUV hzeroVU a i j ha
  have hmass : ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 = 550 :=
    Nat.le_antisymm hupper hlower
  exact h305_cross_mass_eq_550_valueFiveEdge_orientation
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover hmodeu hmodev hzeroUV hzeroVU a i j ha hmass

end

end Erdos85

#print axioms Erdos85.h305_cross_mass_le_550_valueFiveEdge_orientation

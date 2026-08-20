import Proofs.Erdos85CrossCubicMassUpperOrientation
import Proofs.Erdos85CrossCubicValueFiveGlobalGraph
import Proofs.Erdos85CrossEdgeCoordinateIndex
import Proofs.Erdos85CubicMarkedCoordinateBipartite

/-! # Uniformly sharp cross rows give an even-cycle marked graph -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the uniform cross-row upper bound, every marked adjacency changes
the canonical first-shore coordinate by `±1`. -/
theorem h305_cross_mass_le_550_valueFiveGraph_firstCoordinate_step
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
    (hupper : let U := (Finset.univ : Finset (ZMod 8)).image u
      let S := shoreTypeEdgeFinset R U 1
      ∀ a ∈ S, (∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 550)
    ⦃a b : shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1⦄
    (hab : (h305CrossCubicValueFiveGraph R Cedge
      ((Finset.univ : Finset (ZMod 8)).image u)).Adj a b) :
    shoreTypeOneEdgeFirstCoordinate R u v hcover b =
        shoreTypeOneEdgeFirstCoordinate R u v hcover a - 1 ∨
      shoreTypeOneEdgeFirstCoordinate R u v hcover b =
        shoreTypeOneEdgeFirstCoordinate R u v hcover a + 1 := by
  classical
  dsimp only at hupper
  let i := shoreTypeOneEdgeFirstCoordinate R u v hcover a
  obtain ⟨j, ha⟩ :=
    shoreTypeOneEdgeFirstCoordinate_support R u v hcover a
  have hbM : b.1 ∈ cubicValueFiveEdgeFinset R Cedge a.1 := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hab.2⟩
  have horient := h305_cross_mass_le_550_valueFiveEdge_orientation
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover hmodeu hmodev hzeroUV hzeroVU a.1 i j ha
        (hupper a.1 a.2)
  rcases horient with ⟨b₀, b₁, hM, hb₀, hb₁⟩ |
      ⟨b₀, b₁, hM, hb₀, hb₁⟩
  all_goals
    rw [hM] at hbM
    rcases Finset.mem_insert.mp hbM with hb | hb
    · left
      apply shoreTypeOneEdgeFirstCoordinate_eq_of_support
        R u v huinj hdisj hcover b (i - 1)
      simpa [hb] using hb₀
    · right
      have hb' : b.1 = b₁ := Finset.mem_singleton.mp hb
      apply shoreTypeOneEdgeFirstCoordinate_eq_of_support
        R u v huinj hdisj hcover b (i + 1)
      simpa [hb'] using hb₁

/-- The actual 24-target value-five graph is bipartite under the uniform
sharp upper bound; together with `IsCycles`, all its components are even
cycles. -/
theorem h305_cross_mass_le_550_valueFiveGraph_isBipartite
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
    (hupper : let U := (Finset.univ : Finset (ZMod 8)).image u
      let S := shoreTypeEdgeFinset R U 1
      ∀ a ∈ S, (∑ b ∈ cubicResidualEdgeFinset R Cedge a,
        (residualFiberCubicWalkCount R Cedge a b) ^ 2) ≤ 550) :
    (h305CrossCubicValueFiveGraph R Cedge
      ((Finset.univ : Finset (ZMod 8)).image u)).IsBipartite := by
  apply isBipartite_of_zmodEight_unitStep _
    (shoreTypeOneEdgeFirstCoordinate R u v hcover)
  intro a b hab
  exact h305_cross_mass_le_550_valueFiveGraph_firstCoordinate_step
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover hmodeu hmodev hzeroUV hzeroVU hupper hab

end

end Erdos85

#print axioms
  Erdos85.h305_cross_mass_le_550_valueFiveGraph_firstCoordinate_step
#print axioms Erdos85.h305_cross_mass_le_550_valueFiveGraph_isBipartite

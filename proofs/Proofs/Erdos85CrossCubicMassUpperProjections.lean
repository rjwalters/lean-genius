import Proofs.Erdos85CrossCubicMassUpperOrientation
import Proofs.Erdos85MuNegThreeZeroFiveGraphProfileLedger

/-! # Sharp cross-row projections for the global marked graph -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- An edge displayed with one endpoint on each labeled shore has shore type
one relative to the first shore. -/
theorem crossEndpointEdge_mem_shoreTypeEdgeFinset_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u v : ZMod 8 → V) (hdisj : ∀ i j, u i ≠ v j)
    (b : R.edgeFinset) (i j : ZMod 8)
    (hb : b.1.toFinset = {u i, v j}) :
    b ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1 := by
  classical
  simp only [shoreTypeEdgeFinset, Finset.mem_filter, Finset.mem_univ,
    true_and]
  rw [hb]
  have hui : u i ∈ (Finset.univ : Finset (ZMod 8)).image u :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hvj : v j ∉ (Finset.univ : Finset (ZMod 8)).image u := by
    intro h
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    exact hdisj k j hk
  simp [hui, hvj]

/-- The upper-bound orientation package exposes exactly the two local facts
needed by the global marked-cycle bridge: two value-five edges, both in the
canonical cross-shore population. -/
theorem h305_cross_mass_le_550_valueFiveEdge_card_two_and_subset
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
    let U := (Finset.univ : Finset (ZMod 8)).image u
    let M := cubicValueFiveEdgeFinset R Cedge a
    M.card = 2 ∧ M ⊆ shoreTypeEdgeFinset R U 1 := by
  classical
  dsimp only
  have horient := h305_cross_mass_le_550_valueFiveEdge_orientation
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover hmodeu hmodev hzeroUV hzeroVU a i j ha hupper
  have hpm : ∀ k : ZMod 8, k - 1 ≠ k + 1 := by native_decide
  rcases horient with ⟨b₀, b₁, hM, hb₀, hb₁⟩ |
      ⟨b₀, b₁, hM, hb₀, hb₁⟩
  · have hbne : b₀ ≠ b₁ := by
      intro h
      have heq : u (i - 1) = u (i + 1) := by
        have : ({u (i - 1), v (j - 1)} : Finset V) =
            {u (i + 1), v (j + 1)} := hb₀.symm.trans (h ▸ hb₁)
        have hu0 : u (i - 1) ∈ ({u (i + 1), v (j + 1)} : Finset V) := by
          rw [← this]
          simp
        simpa [hdisj (i - 1) (j + 1)] using hu0
      exact hpm i (huinj heq)
    constructor
    · rw [hM]
      simp [hbne]
    · rw [hM]
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact crossEndpointEdge_mem_shoreTypeEdgeFinset_one
          R u v hdisj _ (i - 1) (j - 1) hb₀
      · exact crossEndpointEdge_mem_shoreTypeEdgeFinset_one
          R u v hdisj _ (i + 1) (j + 1) hb₁
  · have hbne : b₀ ≠ b₁ := by
      intro h
      have heq : u (i - 1) = u (i + 1) := by
        have : ({u (i - 1), v (j + 1)} : Finset V) =
            {u (i + 1), v (j - 1)} := hb₀.symm.trans (h ▸ hb₁)
        have hu0 : u (i - 1) ∈ ({u (i + 1), v (j - 1)} : Finset V) := by
          rw [← this]
          simp
        simpa [hdisj (i - 1) (j - 1)] using hu0
      exact hpm i (huinj heq)
    constructor
    · rw [hM]
      simp [hbne]
    · rw [hM]
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · exact crossEndpointEdge_mem_shoreTypeEdgeFinset_one
          R u v hdisj _ (i - 1) (j + 1) hb₀
      · exact crossEndpointEdge_mem_shoreTypeEdgeFinset_one
          R u v hdisj _ (i + 1) (j - 1) hb₁

end


end Erdos85

#print axioms Erdos85.crossEndpointEdge_mem_shoreTypeEdgeFinset_one
#print axioms Erdos85.h305_cross_mass_le_550_valueFiveEdge_card_two_and_subset

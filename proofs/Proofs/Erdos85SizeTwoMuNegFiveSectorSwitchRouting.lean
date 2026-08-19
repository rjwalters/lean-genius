import Proofs.Erdos85SizeTwoMuNegFiveEightEightParameterBounds
import Proofs.Erdos85SizeTwoMuSwitchTable

/-!
# Exact sector switch routing in the `mu=-5` lane

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The sharp signed-capacity window was previously available only as
inequalities.  At order 64 it has exactly six integral cells.  Their shore
switches land in `{-3,-1,1,3}` and no cell is self-switching.
-/

namespace Erdos85

noncomputable section

/-- The six exact integral cells in the `mu=-5` C8+C8 capacity window. -/
def MuNegFiveSectorCells (k r : ℕ) : Prop :=
  (k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 4) ∨ (k = 0 ∧ r = 5) ∨
  (k = 1 ∧ r = 2) ∨ (k = 1 ∧ r = 3) ∨ (k = 1 ∧ r = 4)

theorem muNegFive_sector_cells_of_bounds
    (k r : ℕ) (hk : k ≤ 1) (hr2 : 2 ≤ r) (hr7 : r ≤ 7)
    (hlower : 3 ≤ r + k) (hupper : r + k ≤ 5)
    (hkzero : k = 0 → 3 ≤ r) (hkone : k = 1 → r ≤ 4) :
    MuNegFiveSectorCells k r := by
  interval_cases k <;> interval_cases r <;>
    simp [MuNegFiveSectorCells] <;> omega

/-- Exact arithmetic switch targets of the six cells. -/
theorem muNegFive_sector_switch_target
    (k r : ℕ) (hcell : MuNegFiveSectorCells k r) :
    sizeTwoMuSwitchTarget (-5) k r = -3 ∨
      sizeTwoMuSwitchTarget (-5) k r = -1 ∨
      sizeTwoMuSwitchTarget (-5) k r = 1 ∨
      sizeTwoMuSwitchTarget (-5) k r = 3 := by
  rcases hcell with h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;> norm_num [sizeTwoMuSwitchTarget]

/-- No exact `mu=-5` sector cell is fixed by the shore switch. -/
theorem muNegFive_sector_switch_target_ne_self
    (k r : ℕ) (hcell : MuNegFiveSectorCells k r) :
    sizeTwoMuSwitchTarget (-5) k r ≠ -5 := by
  rcases muNegFive_sector_switch_target k r hcell with h | h | h | h <;>
    omega

/-- Graph-facing extraction of the six exact cells and their four possible
cross-lane targets. -/
theorem orderSixtyFour_sizeTwo_muNegFive_eightEight_sector_cells
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    [DecidableRel (MuNegFiveNeutralProjection G c s)]
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hA_in : ∀ x ∈ c.supp, ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-5 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    ∃ k r : ℕ, MuNegFiveSectorCells k r ∧
      (sizeTwoMuSwitchTarget (-5) k r = -3 ∨
       sizeTwoMuSwitchTarget (-5) k r = -1 ∨
       sizeTwoMuSwitchTarget (-5) k r = 1 ∨
       sizeTwoMuSwitchTarget (-5) k r = 3) := by
  obtain ⟨k, r, hk, hr2, hr7, hlower, hupper, hkzero, hkone⟩ :=
    orderSixtyFour_sizeTwo_muNegFive_eightEight_parameter_bounds
      G hfree hreg hcard c hc s hs_out hs_in hA_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  have hcell := muNegFive_sector_cells_of_bounds k r hk hr2 hr7
    hlower hupper hkzero hkone
  exact ⟨k, r, hcell, muNegFive_sector_switch_target k r hcell⟩

end

end Erdos85

#print axioms Erdos85.muNegFive_sector_switch_target
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_eightEight_sector_cells

import Proofs.Erdos85SizeTwoMuNegThreeEightEightSectorParameterGrid
import Proofs.Erdos85SizeTwoMuSwitchTable
import Proofs.Erdos85SizeTwoMuNegFiveEightEightShoreSwitch

/-! # Discrete sector cells and switch targets in the `mu=-3` lane -/

open Matrix

namespace Erdos85

noncomputable section

/-- The four cells compatible with two all-triangle shores. -/
def MuNegThreeBothTriangleCell (k r : ℕ) : Prop :=
  (k = 0 ∧ r = 5) ∨ (k = 0 ∧ r = 6) ∨
    (k = 1 ∧ r = 4) ∨ (k = 1 ∧ r = 5)

/-- A mixed pair of shores has exactly two possible cells. -/
def MuNegThreeMixedCell (k r : ℕ) : Prop :=
  (k = 0 ∧ r = 5) ∨ (k = 1 ∧ r = 4)

/-- The six cells compatible with two all-triangle-free shores. -/
def MuNegThreeBothTriangleFreeCell (k r : ℕ) : Prop :=
  (k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 4) ∨ (k = 0 ∧ r = 5) ∨
    (k = 1 ∧ r = 2) ∨ (k = 1 ∧ r = 3) ∨ (k = 1 ∧ r = 4)

/-- Arithmetic refinement of the shared two-shore grid after the normal-form
collapse `k≤1` and the global capacity window `3≤r+k≤6`. -/
theorem muNegThree_sector_grid_discrete
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hk : k ≤ 1) (hr2 : 2 ≤ r) (hr7 : r ≤ 7)
    (hlower : 3 ≤ r + k) (hupper : r + k ≤ 6)
    (hgrid :
      (C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧ 5 ≤ r + k) ∨
      ((((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧ r + k = 5) ∨
        (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧ r + k ≤ 5))) :
    (C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧
        MuNegThreeBothTriangleCell k r) ∨
      (((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧
        MuNegThreeMixedCell k r) ∨
      (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧
        MuNegThreeBothTriangleFreeCell k r) := by
  rcases hgrid with hzero | hmixed | hone
  · left
    refine ⟨hzero.1, hzero.2.1, ?_⟩
    dsimp [MuNegThreeBothTriangleCell]
    omega
  · right; left
    refine ⟨hmixed.1, ?_⟩
    dsimp [MuNegThreeMixedCell]
    omega
  · right; right
    refine ⟨hone.1, hone.2.1, ?_⟩
    dsimp [MuNegThreeBothTriangleFreeCell]
    omega

/-- Every post-grid `mu=-3` cell switches to the checked target recorded in
the master table; the only targets are `-5,-3,-1,1,3`. -/
theorem muNegThree_sector_cell_switch_target
    (k r : ℕ)
    (hcell : MuNegThreeBothTriangleCell k r ∨
      MuNegThreeMixedCell k r ∨ MuNegThreeBothTriangleFreeCell k r) :
    sizeTwoMuSwitchTarget (-3) k r = -5 ∨
      sizeTwoMuSwitchTarget (-3) k r = -3 ∨
      sizeTwoMuSwitchTarget (-3) k r = -1 ∨
      sizeTwoMuSwitchTarget (-3) k r = 1 ∨
      sizeTwoMuSwitchTarget (-3) k r = 3 := by
  rcases hcell with h | h | h
  · dsimp [MuNegThreeBothTriangleCell] at h
    rcases h with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]
  · dsimp [MuNegThreeMixedCell] at h
    rcases h with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]
  · dsimp [MuNegThreeBothTriangleFreeCell] at h
    rcases h with h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]

/-- The cells already routed to the closed positive targets `1` or `3` are
exactly `(0,6)`, `(1,4)`, and `(1,5)`. -/
theorem muNegThree_switch_target_positive_iff
    (k r : ℕ)
    (hcell : MuNegThreeBothTriangleCell k r ∨
      MuNegThreeMixedCell k r ∨ MuNegThreeBothTriangleFreeCell k r) :
    (sizeTwoMuSwitchTarget (-3) k r = 1 ∨
      sizeTwoMuSwitchTarget (-3) k r = 3) ↔
    ((k = 0 ∧ r = 6) ∨ (k = 1 ∧ r = 4) ∨ (k = 1 ∧ r = 5)) := by
  rcases hcell with h | h | h
  · dsimp [MuNegThreeBothTriangleCell] at h
    rcases h with h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]
  · dsimp [MuNegThreeMixedCell] at h
    rcases h with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]
  · dsimp [MuNegThreeBothTriangleFreeCell] at h
    rcases h with h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]

set_option maxHeartbeats 1200000 in
/-- Graph-facing composition of the normalized sector grid with the discrete
`mu=-3` cell enumeration. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_sector_cells
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ, k ≤ 1 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      ((C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧
          MuNegThreeBothTriangleCell k r) ∨
        ((((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
            (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧
              MuNegThreeMixedCell k r) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧
            MuNegThreeBothTriangleFreeCell k r))) := by
  classical
  dsimp only
  obtain ⟨k, r, hk, hr2, hr7, hlower, hupper, hgrid⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_sector_parameter_grid
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  refine ⟨k, r, hk, hr2, hr7, ?_⟩
  exact muNegThree_sector_grid_discrete _ _ k r hk hr2 hr7
    hlower hupper hgrid

/-- The two self-switching `mu=-3` cells are forced into the both-all-TF
sector of the grid. -/
theorem muNegThree_self_cells_bothTriangleFree
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hdisc :
      (C8CycleEntriesZero N₁ ∧ C8CycleEntriesZero N₂ ∧
          MuNegThreeBothTriangleCell k r) ∨
      ((((C8CycleEntriesZero N₁ ∧ C8CycleEntriesOne N₂) ∨
          (C8CycleEntriesOne N₁ ∧ C8CycleEntriesZero N₂)) ∧
            MuNegThreeMixedCell k r) ∨
        (C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ ∧
          MuNegThreeBothTriangleFreeCell k r)))
    (hself : (k = 0 ∧ r = 4) ∨ (k = 1 ∧ r = 2)) :
    C8CycleEntriesOne N₁ ∧ C8CycleEntriesOne N₂ := by
  rcases hdisc with hzero | hmixed | hone
  · exfalso
    dsimp [MuNegThreeBothTriangleCell] at hzero
    omega
  · exfalso
    dsimp [MuNegThreeMixedCell] at hmixed
    omega
  · exact ⟨hone.1, hone.2.1⟩

end


end Erdos85

#print axioms Erdos85.muNegThree_sector_grid_discrete
#print axioms Erdos85.muNegThree_sector_cell_switch_target
#print axioms Erdos85.muNegThree_switch_target_positive_iff
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_sector_cells
#print axioms Erdos85.muNegThree_self_cells_bothTriangleFree

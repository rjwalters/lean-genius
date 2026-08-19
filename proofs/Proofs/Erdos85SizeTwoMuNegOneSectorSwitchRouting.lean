import Proofs.Erdos85SizeTwoMuSwitchTable
import Proofs.Erdos85SizeTwoMuNegOneEightEightSectorParameterGrid

/-!
# Discrete sector routing in the `mu=-1` size-two branch

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3.

The normalized `mu=-1` branch has `k ≤ 1`, `2 ≤ r ≤ 7`, and the basic
capacity bound `3 ≤ r+k`.  Combining those bounds with the two-shore sector
grid turns its three qualitative cells into finite parameter lists.  This
file also records the switch targets of those lists.
-/

namespace Erdos85

/-- Abstract arithmetic form of the `mu=-1` sector grid.  `allZero` denotes
two all-triangle shores, `mixed` one shore of each kind, and `allOne` two
all-triangle-free shores. -/
theorem sizeTwoMuNegOne_sector_parameter_cases
    (k r : ℕ) (allZero mixed allOne : Prop)
    (hk : k ≤ 1) (hr2 : 2 ≤ r) (hr7 : r ≤ 7)
    (hbase : 3 ≤ r + k) (hupper : r + k ≤ 7)
    (hgrid : (allZero ∧ 5 ≤ r + k) ∨
      (mixed ∧ r + k = 5) ∨ (allOne ∧ r + k ≤ 5)) :
    (allZero ∧
      ((k = 0 ∧ r = 5) ∨ (k = 0 ∧ r = 6) ∨ (k = 0 ∧ r = 7) ∨
       (k = 1 ∧ r = 4) ∨ (k = 1 ∧ r = 5) ∨ (k = 1 ∧ r = 6))) ∨
    (mixed ∧ ((k = 0 ∧ r = 5) ∨ (k = 1 ∧ r = 4))) ∨
    (allOne ∧
      ((k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 4) ∨ (k = 0 ∧ r = 5) ∨
       (k = 1 ∧ r = 2) ∨ (k = 1 ∧ r = 3) ∨ (k = 1 ∧ r = 4))) := by
  rcases hgrid with hzero | hmixed | hone
  · left
    rcases hzero with ⟨hzero, hlo⟩
    refine ⟨hzero, ?_⟩
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · have hrcases : r = 5 ∨ r = 6 ∨ r = 7 := by omega
      rcases hrcases with rfl | rfl | rfl <;> simp
    · have hrcases : r = 4 ∨ r = 5 ∨ r = 6 := by omega
      rcases hrcases with rfl | rfl | rfl <;> simp
  · right; left
    rcases hmixed with ⟨hmixed, heq⟩
    refine ⟨hmixed, ?_⟩
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · left; omega
    · right; omega
  · right; right
    rcases hone with ⟨hone, hhi⟩
    refine ⟨hone, ?_⟩
    have hkcases : k = 0 ∨ k = 1 := by omega
    rcases hkcases with rfl | rfl
    · have hrcases : r = 3 ∨ r = 4 ∨ r = 5 := by omega
      rcases hrcases with rfl | rfl | rfl <;> simp
    · have hrcases : r = 2 ∨ r = 3 ∨ r = 4 := by omega
      rcases hrcases with rfl | rfl | rfl <;> simp

/-- Switching an all-triangle `mu=-1` cell reaches only the already central
lanes `-3,-1,+1,+3`. -/
theorem sizeTwoMuNegOne_allZero_switch_targets
    (k r : ℕ)
    (h : (k = 0 ∧ r = 5) ∨ (k = 0 ∧ r = 6) ∨ (k = 0 ∧ r = 7) ∨
      (k = 1 ∧ r = 4) ∨ (k = 1 ∧ r = 5) ∨ (k = 1 ∧ r = 6)) :
    sizeTwoMuSwitchTarget (-1) k r = -3 ∨
    sizeTwoMuSwitchTarget (-1) k r = -1 ∨
    sizeTwoMuSwitchTarget (-1) k r = 1 ∨
    sizeTwoMuSwitchTarget (-1) k r = 3 := by
  rcases h with h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
    norm_num [sizeTwoMuSwitchTarget]

/-- A mixed `mu=-1` sector switches either to `mu=-3` or is a self cell. -/
theorem sizeTwoMuNegOne_mixed_switch_targets
    (k r : ℕ) (h : (k = 0 ∧ r = 5) ∨ (k = 1 ∧ r = 4)) :
    sizeTwoMuSwitchTarget (-1) k r = -3 ∨
      sizeTwoMuSwitchTarget (-1) k r = -1 := by
  rcases h with h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
    norm_num [sizeTwoMuSwitchTarget]

/-- Switching an all-triangle-free `mu=-1` cell reaches only the lower
negative lanes (including the already excluded `mu=-7` lane). -/
theorem sizeTwoMuNegOne_allOne_switch_targets
    (k r : ℕ)
    (h : (k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 4) ∨ (k = 0 ∧ r = 5) ∨
      (k = 1 ∧ r = 2) ∨ (k = 1 ∧ r = 3) ∨ (k = 1 ∧ r = 4)) :
    sizeTwoMuSwitchTarget (-1) k r = -7 ∨
    sizeTwoMuSwitchTarget (-1) k r = -5 ∨
    sizeTwoMuSwitchTarget (-1) k r = -3 ∨
    sizeTwoMuSwitchTarget (-1) k r = -1 := by
  rcases h with h | h | h | h | h | h <;> rcases h with ⟨rfl, rfl⟩ <;>
    norm_num [sizeTwoMuSwitchTarget]

set_option maxHeartbeats 1200000 in
/-- Graph-facing exact sector cells for the normalized `mu=-1` C8+C8
branch.  This is the direct composition socket for shore switching and the
four residual self-cell terminals. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_sector_cells
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
        s y = (-1 : ℤ) * s z)
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
    ∃ k r : ℕ,
      ((MuNegOneC8CycleEntriesZero N₁ ∧ MuNegOneC8CycleEntriesZero N₂) ∧
        ((k = 0 ∧ r = 5) ∨ (k = 0 ∧ r = 6) ∨ (k = 0 ∧ r = 7) ∨
         (k = 1 ∧ r = 4) ∨ (k = 1 ∧ r = 5) ∨ (k = 1 ∧ r = 6))) ∨
      ((((MuNegOneC8CycleEntriesZero N₁ ∧ MuNegOneC8CycleEntriesOne N₂) ∨
          (MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesZero N₂))) ∧
        ((k = 0 ∧ r = 5) ∨ (k = 1 ∧ r = 4))) ∨
      ((MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesOne N₂) ∧
        ((k = 0 ∧ r = 3) ∨ (k = 0 ∧ r = 4) ∨ (k = 0 ∧ r = 5) ∨
         (k = 1 ∧ r = 2) ∨ (k = 1 ∧ r = 3) ∨ (k = 1 ∧ r = 4))) := by
  dsimp only
  obtain ⟨k, r, hk, hr2, hr7, hbase, hupper, hgrid⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_sector_parameter_grid
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
        u v huinj hvinj hurange hvrange hu hv
  let K := (secondOrderDefectGraph G).induce c.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  let allZero := MuNegOneC8CycleEntriesZero N₁ ∧
    MuNegOneC8CycleEntriesZero N₂
  let mixed := (MuNegOneC8CycleEntriesZero N₁ ∧
      MuNegOneC8CycleEntriesOne N₂) ∨
    (MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesZero N₂)
  let allOne := MuNegOneC8CycleEntriesOne N₁ ∧
    MuNegOneC8CycleEntriesOne N₂
  have hgrid' : (allZero ∧ 5 ≤ r + k) ∨
      (mixed ∧ r + k = 5) ∨ (allOne ∧ r + k ≤ 5) := by
    simpa [allZero, mixed, allOne, N₁, N₂, K, and_assoc] using hgrid
  refine ⟨k, r, ?_⟩
  simpa [allZero, mixed, allOne, N₁, N₂, K] using
    (sizeTwoMuNegOne_sector_parameter_cases k r allZero mixed allOne
      hk hr2 hr7 hbase hupper hgrid')

end Erdos85

#print axioms Erdos85.sizeTwoMuNegOne_sector_parameter_cases
#print axioms Erdos85.sizeTwoMuNegOne_allZero_switch_targets
#print axioms Erdos85.sizeTwoMuNegOne_mixed_switch_targets
#print axioms Erdos85.sizeTwoMuNegOne_allOne_switch_targets
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_sector_cells

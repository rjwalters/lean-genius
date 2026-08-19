import Proofs.Erdos85SizeTwoMuSwitchTable

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
    (hk : k ≤ 1) (hr2 : 2 ≤ r) (hr7 : r ≤ 7) (hbase : 3 ≤ r + k)
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
    interval_cases k <;> interval_cases r <;> omega
  · right; left
    rcases hmixed with ⟨hmixed, heq⟩
    refine ⟨hmixed, ?_⟩
    interval_cases k <;> interval_cases r <;> omega
  · right; right
    rcases hone with ⟨hone, hhi⟩
    refine ⟨hone, ?_⟩
    interval_cases k <;> interval_cases r <;> omega

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

end Erdos85

#print axioms Erdos85.sizeTwoMuNegOne_sector_parameter_cases
#print axioms Erdos85.sizeTwoMuNegOne_allZero_switch_targets
#print axioms Erdos85.sizeTwoMuNegOne_mixed_switch_targets
#print axioms Erdos85.sizeTwoMuNegOne_allOne_switch_targets

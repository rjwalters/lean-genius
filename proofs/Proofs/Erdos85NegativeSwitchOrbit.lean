import Proofs.Erdos85SizeTwoMuNegOneRefinedSectorRouting
import Proofs.Erdos85SizeTwoMuNegThreeRefinedSectorRouting
import Proofs.Erdos85SizeTwoMuNegFiveSectorSwitchRouting

/-!
# Canonical negative switch orbits

The shore switch is an involution, so routing whole signed-eigenvalue lanes
through one another creates a cycle.  These finite classifications retain the
common parameters `k,r` and expose the actual two-endpoint orbit instead.  A
graph-facing assembly can consequently choose one certificate endpoint of
each displayed orbit and use the opposite endpoint only for transport.

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

namespace Erdos85

/-- The four post-`mu=1` cells in the `mu=-5` lane, with their exact switched
endpoint.  The three negative targets are the canonical (smaller-eigenvalue)
side of their orbits; `(1,4)` is the positive `mu=3` exit. -/
theorem muNegFive_postMuOne_exact_switch_orbits
    (k r : ℕ) (hcell : MuNegFivePostMuOneSectorCells k r) :
    (k = 0 ∧ r = 3 ∧ sizeTwoMuSwitchTarget (-5) k r = -3) ∨
    (k = 0 ∧ r = 4 ∧ sizeTwoMuSwitchTarget (-5) k r = -1) ∨
    (k = 1 ∧ r = 2 ∧ sizeTwoMuSwitchTarget (-5) k r = -1) ∨
    (k = 1 ∧ r = 4 ∧ sizeTwoMuSwitchTarget (-5) k r = 3) := by
  rcases hcell with h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    norm_num [sizeTwoMuSwitchTarget]

/-- The post-`mu=1` `mu=-3` table modulo repeated geometry modes.  The
`(0,3)` cell transports to the canonical `mu=-5` endpoint; `(1,2)` is the
self cell; `(0,5)` and `(1,3)` are the canonical endpoints of their
`mu=-1` orbits; `(1,5)` exits to `mu=3`. -/
theorem muNegThree_postMuOne_exact_switch_orbits
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hcell : MuNegThreePostMuOneSectorCells N₁ N₂ k r) :
    (k = 0 ∧ r = 3 ∧ sizeTwoMuSwitchTarget (-3) k r = -5) ∨
    (k = 0 ∧ r = 5 ∧ sizeTwoMuSwitchTarget (-3) k r = -1) ∨
    (k = 1 ∧ r = 2 ∧ sizeTwoMuSwitchTarget (-3) k r = -3) ∨
    (k = 1 ∧ r = 3 ∧ sizeTwoMuSwitchTarget (-3) k r = -1) ∨
    (k = 1 ∧ r = 5 ∧ sizeTwoMuSwitchTarget (-3) k r = 3) := by
  rcases hcell with hzero | hmixed | hone
  · rcases hzero.2.2 with h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]
  · rcases hmixed.2 with ⟨rfl, rfl⟩
    norm_num [sizeTwoMuSwitchTarget]
  · rcases hone.2.2 with h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]

/-- The endpoint-reduced `mu=-1` table modulo repeated geometry modes.  Its
negative cross-lane cells all transport to the canonical smaller endpoint;
`(1,4)` is the self cell and `(1,6)` exits to `mu=3`. -/
theorem muNegOne_postEndpoint_exact_switch_orbits
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (k r : ℕ)
    (hcell : MuNegOnePostEndpointSectorCells N₁ N₂ k r) :
    (k = 0 ∧ r = 4 ∧ sizeTwoMuSwitchTarget (-1) k r = -5) ∨
    (k = 0 ∧ r = 5 ∧ sizeTwoMuSwitchTarget (-1) k r = -3) ∨
    (k = 1 ∧ r = 2 ∧ sizeTwoMuSwitchTarget (-1) k r = -5) ∨
    (k = 1 ∧ r = 3 ∧ sizeTwoMuSwitchTarget (-1) k r = -3) ∨
    (k = 1 ∧ r = 4 ∧ sizeTwoMuSwitchTarget (-1) k r = -1) ∨
    (k = 1 ∧ r = 6 ∧ sizeTwoMuSwitchTarget (-1) k r = 3) := by
  rcases hcell with hzero | hmixed | hone
  · rcases hzero.2 with h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]
  · rcases hmixed.2 with h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]
  · rcases hone.2 with h | h | h | h | h <;>
      rcases h with ⟨rfl, rfl⟩ <;>
      norm_num [sizeTwoMuSwitchTarget]

end Erdos85

#print axioms Erdos85.muNegFive_postMuOne_exact_switch_orbits
#print axioms Erdos85.muNegThree_postMuOne_exact_switch_orbits
#print axioms Erdos85.muNegOne_postEndpoint_exact_switch_orbits

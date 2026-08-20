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

/-- A non-recursive elimination principle for the complete negative switch
table.  `P μ k r` is the graph-facing bad configuration at one endpoint and
`htransport` is the shore switch.  Only the smaller negative endpoint of
each two-cycle needs a certificate; the two negative self cells and the
positive exits are supplied separately.

This is deliberately independent of the concrete graph representation.  In
particular, a downstream consumer can instantiate `P` with a record that
retains its aligned quotient and sector geometry instead of erasing those
data into an ambient eigenvector. -/
theorem negativeSwitchOrbits_false_of_canonical_endpoints
    (P : ℤ → ℕ → ℕ → Prop)
    (N₁ N₂ : Matrix (ZMod 8) (ZMod 8) ℤ) (mu : ℤ) (k r : ℕ)
    (hP : P mu k r)
    (hcell :
      (mu = -5 ∧ MuNegFivePostMuOneSectorCells k r) ∨
      (mu = -3 ∧ MuNegThreePostMuOneSectorCells N₁ N₂ k r) ∨
      (mu = -1 ∧ MuNegOnePostEndpointSectorCells N₁ N₂ k r))
    (htransport : ∀ theta i j, P theta i j →
      P (sizeTwoMuSwitchTarget theta i j) i j)
    (h503 : P (-5) 0 3 → False)
    (h504 : P (-5) 0 4 → False)
    (h512 : P (-5) 1 2 → False)
    (h305 : P (-3) 0 5 → False)
    (h313 : P (-3) 1 3 → False)
    (h312 : P (-3) 1 2 → False)
    (h114 : P (-1) 1 4 → False)
    (hpos : ∀ i j, P 3 i j → False) : False := by
  rcases hcell with ⟨rfl, h5⟩ | ⟨rfl, h3⟩ | ⟨rfl, h1⟩
  · rcases muNegFive_postMuOne_exact_switch_orbits k r h5 with
      h | h | h | h
    · rcases h with ⟨rfl, rfl, _⟩
      exact h503 hP
    · rcases h with ⟨rfl, rfl, _⟩
      exact h504 hP
    · rcases h with ⟨rfl, rfl, _⟩
      exact h512 hP
    · rcases h with ⟨rfl, rfl, ht⟩
      exact hpos 1 4 (ht ▸ htransport (-5) 1 4 hP)
  · rcases muNegThree_postMuOne_exact_switch_orbits N₁ N₂ k r h3 with
      h | h | h | h | h
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h503 (ht ▸ htransport (-3) 0 3 hP)
    · rcases h with ⟨rfl, rfl, _⟩
      exact h305 hP
    · rcases h with ⟨rfl, rfl, _⟩
      exact h312 hP
    · rcases h with ⟨rfl, rfl, _⟩
      exact h313 hP
    · rcases h with ⟨rfl, rfl, ht⟩
      exact hpos 1 5 (ht ▸ htransport (-3) 1 5 hP)
  · rcases muNegOne_postEndpoint_exact_switch_orbits N₁ N₂ k r h1 with
      h | h | h | h | h | h
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h504 (ht ▸ htransport (-1) 0 4 hP)
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h305 (ht ▸ htransport (-1) 0 5 hP)
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h512 (ht ▸ htransport (-1) 1 2 hP)
    · rcases h with ⟨rfl, rfl, ht⟩
      exact h313 (ht ▸ htransport (-1) 1 3 hP)
    · rcases h with ⟨rfl, rfl, _⟩
      exact h114 hP
    · rcases h with ⟨rfl, rfl, ht⟩
      exact hpos 1 6 (ht ▸ htransport (-1) 1 6 hP)
end Erdos85

#print axioms Erdos85.muNegFive_postMuOne_exact_switch_orbits
#print axioms Erdos85.muNegThree_postMuOne_exact_switch_orbits
#print axioms Erdos85.muNegOne_postEndpoint_exact_switch_orbits
#print axioms Erdos85.negativeSwitchOrbits_false_of_canonical_endpoints

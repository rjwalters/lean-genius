import Proofs.Erdos85BinarySquareRegularCapstone

/-! # The connected nonbipartite binary-square interface

This module pins the remaining `A-REG-NONBIP-q2k` branch as an exact Lean
proposition.  It deliberately supplies no mechanism for proving the
proposition: that mathematical step remains open.  The theorem below records
only the safe direction from the stronger existing `A-REG` interface.
-/

open SimpleGraph

namespace Erdos85

/-- **A-REG-NONBIP-q2k** as a proposition: at binary square order, no regular
C4-free candidate has a connected, nonbipartite second-order defect graph.

This is a named socket for the sole open structural branch, not a Lean axiom.
-/
def BinarySquareConnectedNonbipartiteExclusion : Prop :=
  ∀ k : Nat, 3 ≤ k →
    ∀ (G : SimpleGraph (Fin (2 ^ k * 2 ^ k)))
      (_ : DecidableRel G.Adj),
      ¬ containsC4 (Fin (2 ^ k * 2 ^ k)) G →
      (∀ x, G.degree x = 2 ^ k) →
      (secondOrderDefectGraph G).Connected →
      ¬ (secondOrderDefectGraph G).IsBipartite →
      False

/-- The full regular exclusion implies its connected nonbipartite subcase.
No converse is asserted here: closing Branch A also needs the already-developed
reductions that route every regular candidate into this subcase. -/
theorem binarySquareConnectedNonbipartiteExclusion_of_regularExclusion
    (h : BinarySquareRegularExclusion) :
    BinarySquareConnectedNonbipartiteExclusion := by
  intro k hk G hdec hfree hreg _hconn _hnotbip
  exact h k hk ⟨G, hdec, hfree, hreg⟩

end Erdos85

#print axioms Erdos85.binarySquareConnectedNonbipartiteExclusion_of_regularExclusion

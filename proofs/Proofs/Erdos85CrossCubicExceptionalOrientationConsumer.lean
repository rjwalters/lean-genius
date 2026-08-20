import Proofs.Erdos85CrossCubicExceptionalMatchingOrientation

/-! # Graph-facing exceptional matching orientation consumer -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Sharp cubic equality at the four cross exceptional coordinates forces
the two value-five edges to be either the straight or crossed local matching.
This is the graph-facing Boolean transition interface for the global marked
relation. -/
theorem h305_crossCubicSharp_valueFiveEdge_orientation
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hdisj : ∀ k l, u k ≠ v l)
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R v ∨
      MuNegThreeZeroFiveTfShoreMode R v)
    (i j : ZMod 8) (a : R.edgeFinset)
    (hsharp : ∀ x ∈ h305CrossCubicExceptionalCoordinates u v i j,
      let c := cubicResidualFiberHistogram R Cedge x a
      (∑ t ∈ Finset.range 7, c t) = 6 ∧
        (∑ t ∈ Finset.range 7, t * c t) = 25 ∧
        (∑ t ∈ Finset.range 7, t ^ 2 * c t) ≤ 105)
    (houtside : ∀ x ∉ h305CrossCubicExceptionalCoordinates u v i j,
      cubicResidualFiberHistogram R Cedge x a 5 = 0) :
    let M := cubicValueFiveEdgeFinset R Cedge a
    (∃ b₀ b₁, M = {b₀, b₁} ∧
      b₀.1.toFinset = {u (i - 1), v (j - 1)} ∧
      b₁.1.toFinset = {u (i + 1), v (j + 1)}) ∨
    (∃ b₀ b₁, M = {b₀, b₁} ∧
      b₀.1.toFinset = {u (i - 1), v (j + 1)} ∧
      b₁.1.toFinset = {u (i + 1), v (j - 1)}) := by
  classical
  dsimp only
  let X := h305CrossCubicExceptionalCoordinates u v i j
  let M := cubicValueFiveEdgeFinset R Cedge a
  have hX : X.card = 4 :=
    h305CrossCubicExceptionalCoordinates_card_four
      u v huinj hvinj hdisj i j
  have hbase := cubicResidual_sharp_fourFibers_valueFiveEdge_matching
    R Cedge hfree hreg a X hX (by simpa [X] using hsharp)
      (by simpa [X] using houtside)
  have hcross := h305_crossCubicExceptional_valueFiveEdge_crossMatching
    R Cedge hfree hreg u v huinj hvinj hdisj hmodeu hmodev i j a
      hsharp houtside
  exact h305_crossCubicExceptional_matching_orientation
    R u v huinj hvinj hdisj i j M hcross.1 hbase.2.1 hcross.2.1
      hcross.2.2

end

end Erdos85

#print axioms Erdos85.h305_crossCubicSharp_valueFiveEdge_orientation

import Proofs.Erdos85CubicEqualityMarkedEdgeMatching
import Proofs.Erdos85CrossCubicExceptionalCoordinates

/-! # Exceptional value-five edges form a cross-shore matching -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Graph-facing cross-shore form of the sharp cubic equality package.  The
two value-five edges pair the four exceptional coordinates, and each such
edge has exactly one endpoint on either C8 shore. -/
theorem h305_crossCubicExceptional_valueFiveEdge_crossMatching
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
    let X := h305CrossCubicExceptionalCoordinates u v i j
    let M := cubicValueFiveEdgeFinset R Cedge a
    M.card = 2 ∧
      (∀ b ∈ M,
        (b.1.toFinset ∩ {u (i - 1), u (i + 1)}).card = 1 ∧
        (b.1.toFinset ∩ {v (j - 1), v (j + 1)}).card = 1) ∧
      ∀ x ∈ X, ∃! b : R.edgeFinset, b ∈ M ∧ x ∈ b.1.toFinset := by
  classical
  dsimp only
  let X := h305CrossCubicExceptionalCoordinates u v i j
  let M := cubicValueFiveEdgeFinset R Cedge a
  have hX : X.card = 4 :=
    h305CrossCubicExceptionalCoordinates_card_four
      u v huinj hvinj hdisj i j
  have hpkg := cubicResidual_sharp_fourFibers_valueFiveEdge_matching
    R Cedge hfree hreg a X hX (by simpa [X] using hsharp)
      (by simpa [X] using houtside)
  refine ⟨hpkg.1, ?_, hpkg.2.2⟩
  intro b hb
  exact h305_crossExceptional_edge_one_endpoint_each_shore
    R u v huinj hvinj hdisj hmodeu hmodev i j b (hpkg.2.1 b hb)

end

end Erdos85

#print axioms
  Erdos85.h305_crossCubicExceptional_valueFiveEdge_crossMatching

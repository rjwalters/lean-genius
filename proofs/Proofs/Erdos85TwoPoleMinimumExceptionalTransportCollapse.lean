import Proofs.Erdos85TwoPoleMinimumDefectSignature
import Proofs.Erdos85TwoPoleExceptionalLineCorrection

/-!
# Collapse of the minimum exceptional transports

At minimum support, the ordinary defect equation and the exceptional
residual transport contain the same pole-line term.  Over `ZMod 2` it
cancels, leaving a pole-free comparison of the three transport graphs.
-/

open SimpleGraph

namespace Erdos85

/-- A minimum two-pole potential satisfying the exceptional residual
transport obeys the pole-free identity `Kx + Dx = Tx + x`. -/
theorem minimumTwoPole_exceptionalTransport_collapse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} (hqEven : Even q) (hreg : ∀ u, G.degree u = q)
    (x : V → ZMod 2) (pole₁ pole₂ : V)
    (hAx : (G.adjMatrix (ZMod 2)).mulVec x =
      Pi.single pole₁ 1 + Pi.single pole₂ 1)
    (hcard : (f2PotentialSupport x).card = q)
    (htransport :
      ((binaryTransportResidualGraph G hqEven hreg).adjMatrix
          (ZMod 2)).mulVec x =
        ((triangleFreeEdgeGraph G).adjMatrix (ZMod 2)).mulVec x +
          (G.adjMatrix (ZMod 2)).mulVec
            (Pi.single pole₁ 1 + Pi.single pole₂ 1)) :
    ((binaryTransportResidualGraph G hqEven hreg).adjMatrix
          (ZMod 2)).mulVec x +
        ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec x =
      ((triangleFreeEdgeGraph G).adjMatrix (ZMod 2)).mulVec x + x := by
  have hdefect := secondOrderDefect_mulVec_minimum_twoPolePotential
    G hfree hqEven hreg x pole₁ pole₂ hAx hcard
  rw [htransport, hdefect]
  funext v
  simp only [Pi.add_apply]
  calc
    _ = ((triangleFreeEdgeGraph G).adjMatrix (ZMod 2)).mulVec x v +
          ((G.adjMatrix (ZMod 2)).mulVec
              (Pi.single pole₁ 1 + Pi.single pole₂ 1) v +
            (G.adjMatrix (ZMod 2)).mulVec
              (Pi.single pole₁ 1 + Pi.single pole₂ 1) v) + x v := by
            ac_rfl
    _ = _ := by rw [zmodTwo_add_self, add_zero]

end Erdos85

#print axioms Erdos85.minimumTwoPole_exceptionalTransport_collapse

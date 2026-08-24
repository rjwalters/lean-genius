import Proofs.Erdos85TwoPoleKernelImageDichotomy
import Proofs.Erdos85BinaryCutGraphTwoPoleRoute

/-!
# Two-pole weighted transport or a physical cut route

The finite-dimensional kernel/image dichotomy leaves an adjacency-potential
equation in its second horn.  In an even-regular graph that equation already
has a graph-native consumer: its support cut contains a pole-to-pole walk.
Thus both horns now end in concrete transport geometry.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Weighted transport / physical route dichotomy (`73rnz_ay-bl`).**
For two distinct poles in an even-regular graph, either a kernel separator
distinguishes them and transports weighted residual mass to triangle mass,
or a binary potential support cut contains an actual pole-to-pole walk with
the exact F₂ endpoint boundary. -/
theorem exists_starDistinguishing_residualTransport_or_twoPoleCutRoute
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    {q : ℕ} (hq : Even q) (hreg : ∀ x, A.degree x = q)
    (E₁ E₂ : V) (hpoles : E₁ ≠ E₂) :
    (∃ v : V → ZMod 2,
      v E₁ + v E₂ = 1 ∧
      ∀ center,
        (∑ z, graphEdgeIndicator (binaryTransportResidualGraph A hq hreg)
          center z * v z) =
        ∑ z, graphEdgeIndicator (triangleFreeEdgeGraph A) center z * v z) ∨
      ∃ x : V → ZMod 2,
        ∃ p : (binaryVertexCutGraph A (f2PotentialSupport x)).Walk E₁ E₂,
          f2WalkEdgeBoundary p = f2EndpointSwitch E₁ E₂ := by
  rcases exists_starDistinguishing_residualTransport_or_exists_adjPotential
    A hq hreg E₁ E₂ with hweighted | ⟨x, hx⟩
  · exact Or.inl hweighted
  · right
    have heven : ∀ u, Even (A.degree u) := by
      intro u
      rw [hreg]
      exact hq
    have hpotential :
        (A.adjMatrix (ZMod 2)).mulVec x = f2EndpointSwitch E₁ E₂ := by
      simpa [f2EndpointSwitch] using hx
    obtain ⟨p, hp⟩ :=
      exists_binaryVertexCutGraph_twoPole_walk_of_adjMatrix_mulVec
        A x E₁ E₂ hpoles heven hpotential
    exact ⟨x, p, hp⟩

end


end Erdos85

#print axioms Erdos85.exists_starDistinguishing_residualTransport_or_twoPoleCutRoute

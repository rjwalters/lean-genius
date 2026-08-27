import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveSixthOrbitTransport

/-! # Semantic realization transport for adaptive sixth cells -/

namespace Erdos85

open SimpleGraph

/-- A graph contains every positive edge forced by one adaptive sixth cell. -/
def OrderFortyNineRealizesAdaptiveSixthCell
    (G : SimpleGraph (Fin 49))
    (li ri ai bi ci di ei : Fin 8) : Prop :=
  ∀ i j,
    orderFortyNineThreeHighB1AdaptiveSixthAvailableEdge
        li ri ai bi ci di ei i j = true →
      G.Adj i j

theorem orderFortyNineAdaptiveSixthOrbitVertexPerm_symm_apply
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator) (v : Fin 49) :
    (orderFortyNineAdaptiveSixthOrbitVertexPerm g).symm v =
      orderFortyNineAdaptiveSixthOrbitVertexPerm g v := by
  rfl

theorem orderFortyNineAdaptiveSixthOrbitVertexPerm_involutive
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator) (v : Fin 49) :
    orderFortyNineAdaptiveSixthOrbitVertexPerm g
        (orderFortyNineAdaptiveSixthOrbitVertexPerm g v) = v := by
  exact orderFortyNineAdaptiveSixthOrbitVertexMap_involutive g v

/-- Relabeling by an explicit sixth-orbit generator carries a realization of
the source forced-edge cell to a realization of the transformed target cell. -/
theorem orderFortyNineAdaptiveSixthOrbit_realizes_target
    (G : SimpleGraph (Fin 49))
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (li ri ai bi ci di ei : Fin 8)
    (hreal : OrderFortyNineRealizesAdaptiveSixthCell
      G li ri ai bi ci di ei) :
    let t := orderFortyNineAdaptiveSixthOrbitTransform
      g li ri ai bi ci di ei
    OrderFortyNineRealizesAdaptiveSixthCell
      (orderFortyNineRelabeledGraph G
        (orderFortyNineAdaptiveSixthOrbitVertexPerm g))
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
        t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
  dsimp only
  intro i j hij
  rw [orderFortyNineRelabeledGraph_adj]
  simp only [orderFortyNineAdaptiveSixthOrbitVertexPerm_symm_apply]
  apply hreal
  rw [← orderFortyNineAdaptiveSixthOrbitAvailableEdge_covariant
    g li ri ai bi ci di ei
      (orderFortyNineAdaptiveSixthOrbitVertexPerm g i)
      (orderFortyNineAdaptiveSixthOrbitVertexPerm g j)]
  simpa only [orderFortyNineAdaptiveSixthOrbitVertexPerm_involutive] using hij

/-- The graph-theoretic admissibility package transports together with the
positive cell realization.  No DIMACS auxiliary-variable automorphism is
assumed. -/
theorem orderFortyNineAdaptiveSixthOrbit_semantic_transport
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (li ri ai bi ci di ei : Fin 8) (d : Nat)
    (hfree : ¬ containsC4 (Fin 49) G)
    (hdegree : ∀ v, d ≤ G.degree v)
    (hreal : OrderFortyNineRealizesAdaptiveSixthCell
      G li ri ai bi ci di ei) :
    let t := orderFortyNineAdaptiveSixthOrbitTransform
      g li ri ai bi ci di ei
    let H := orderFortyNineRelabeledGraph G
      (orderFortyNineAdaptiveSixthOrbitVertexPerm g)
    ¬ containsC4 (Fin 49) H ∧
      (∀ v, d ≤ H.degree v) ∧
      OrderFortyNineRealizesAdaptiveSixthCell H
        t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
          t.2.2.2.2.2.1 t.2.2.2.2.2.2 := by
  dsimp only
  exact ⟨orderFortyNineRelabeledGraph_not_containsC4 G _ hfree,
    orderFortyNineRelabeledGraph_minDegree G _ d hdegree,
    orderFortyNineAdaptiveSixthOrbit_realizes_target
      G g li ri ai bi ci di ei hreal⟩

end Erdos85

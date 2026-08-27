import Proofs.Erdos85OrderFortyNineAlignedBooleanBridge

/-!
# Transport of signed partial order-49 graph states

The adaptive frontier orbit audit compares partial graph states containing
both forced edges and forced nonedges.  This module gives the graph-semantic
transport theorem needed to use an explicit vertex isomorphism without
assuming that auxiliary DIMACS variables transform in the same way.
-/

namespace Erdos85

open SimpleGraph

/-- A partial signed graph state.  `some true` prescribes an edge,
`some false` a nonedge, and `none` leaves the pair unspecified. -/
abbrev OrderFortyNineSignedEdgeState :=
  Fin 49 → Fin 49 → Option Bool

/-- Relabel a signed state by the same convention as
`orderFortyNineRelabeledGraph`. -/
def orderFortyNineRelabeledSignedEdgeState
    (S : OrderFortyNineSignedEdgeState)
    (E : Equiv.Perm (Fin 49)) : OrderFortyNineSignedEdgeState :=
  fun i j => S (E.symm i) (E.symm j)

/-- `G` agrees with every edge and nonedge prescribed by `S`. -/
def OrderFortyNineRealizesSignedEdgeState
    (G : SimpleGraph (Fin 49))
    (S : OrderFortyNineSignedEdgeState) : Prop :=
  ∀ i j b, S i j = some b → (G.Adj i j ↔ b = true)

/-- Realization of a signed partial state is invariant under simultaneous
vertex relabeling of the graph and state. -/
theorem orderFortyNineRealizesRelabeledSignedEdgeState
    (G : SimpleGraph (Fin 49))
    (S : OrderFortyNineSignedEdgeState)
    (E : Equiv.Perm (Fin 49))
    (hreal : OrderFortyNineRealizesSignedEdgeState G S) :
    OrderFortyNineRealizesSignedEdgeState
      (orderFortyNineRelabeledGraph G E)
      (orderFortyNineRelabeledSignedEdgeState S E) := by
  intro i j b hs
  rw [orderFortyNineRelabeledGraph_adj]
  exact hreal (E.symm i) (E.symm j) b hs

/-- A vertex permutation transports any uniform lower degree bound. -/
theorem orderFortyNineRelabeledGraph_minDegree
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (E : Equiv.Perm (Fin 49)) (d : Nat)
    (hdegree : ∀ v, d ≤ G.degree v) :
    ∀ i, d ≤ (orderFortyNineRelabeledGraph G E).degree i := by
  intro i
  rw [orderFortyNineRelabeledGraph_degree]
  exact hdegree (E.symm i)

/-- The full semantic package used by an order-49 nonexistence argument
transports from a signed state to its relabeling. -/
theorem orderFortyNineSignedState_semantic_transport
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S : OrderFortyNineSignedEdgeState)
    (E : Equiv.Perm (Fin 49)) (d : Nat)
    (hfree : ¬ containsC4 (Fin 49) G)
    (hdegree : ∀ v, d ≤ G.degree v)
    (hreal : OrderFortyNineRealizesSignedEdgeState G S) :
    ¬ containsC4 (Fin 49) (orderFortyNineRelabeledGraph G E) ∧
      (∀ i, d ≤ (orderFortyNineRelabeledGraph G E).degree i) ∧
      OrderFortyNineRealizesSignedEdgeState
        (orderFortyNineRelabeledGraph G E)
        (orderFortyNineRelabeledSignedEdgeState S E) := by
  exact ⟨orderFortyNineRelabeledGraph_not_containsC4 G E hfree,
    orderFortyNineRelabeledGraph_minDegree G E d hdegree,
    orderFortyNineRealizesRelabeledSignedEdgeState G S E hreal⟩

/-- Convenient orbit-consumer form: an explicit equality from the relabeled
source state to a target state transports an admissible realization directly
to that target. -/
theorem orderFortyNineSignedState_semantic_transport_to
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (S T : OrderFortyNineSignedEdgeState)
    (E : Equiv.Perm (Fin 49)) (d : Nat)
    (hstate : orderFortyNineRelabeledSignedEdgeState S E = T)
    (hfree : ¬ containsC4 (Fin 49) G)
    (hdegree : ∀ v, d ≤ G.degree v)
    (hreal : OrderFortyNineRealizesSignedEdgeState G S) :
    ¬ containsC4 (Fin 49) (orderFortyNineRelabeledGraph G E) ∧
      (∀ i, d ≤ (orderFortyNineRelabeledGraph G E).degree i) ∧
      OrderFortyNineRealizesSignedEdgeState
        (orderFortyNineRelabeledGraph G E) T := by
  simpa [hstate] using orderFortyNineSignedState_semantic_transport
    G S E d hfree hdegree hreal

end Erdos85

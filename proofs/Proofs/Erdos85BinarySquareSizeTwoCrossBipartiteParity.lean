import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteCycles
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! # Parity of size-two cross-block cycles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The canonical two-coloring of a component cross block: left vertices
have color zero and right vertices color one. -/
def componentCrossBipartiteColoring
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentCrossBipartiteGraph G c d).Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk
    (fun v => match v with
      | Sum.inl _ => 0
      | Sum.inr _ => 1)
    (by
      intro u v huv
      cases u <;> cases v <;>
        simp [componentCrossBipartiteGraph] at huv ⊢)

/-- Every component cross block is bipartite. -/
theorem componentCrossBipartiteGraph_isBipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentCrossBipartiteGraph G c d).IsBipartite :=
  ⟨componentCrossBipartiteColoring G c d⟩

/-- Every connected cycle in a size-two cross block has even order. -/
theorem binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    Even e.supp.ncard := by
  let H := componentCrossBipartiteGraph G c d
  have hdeg : ∀ v, H.degree v = 2 :=
    binarySquare_regular_twoSizeTwoParts_crossBipartiteGraph_degree_two
      G hfree hq hreg hcard c d hc hd
  obtain ⟨x, p, hp, hpverts, _hgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph H hdeg e
  have hloopEven : Even p.length :=
    (SimpleGraph.two_colorable_iff_forall_loop_even.mp
      (componentCrossBipartiteGraph_isBipartite G c d)) x p
  have hlen : p.length = e.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = e.supp.ncard := congrArg Set.ncard hpverts
  rwa [hlen] at hloopEven

end

end Erdos85

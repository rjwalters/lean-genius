import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteCycles

/-! # Ambient C4-freeness of cross-component bipartite graphs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Forget the side tag on a vertex of a component cross graph. -/
def componentCrossBipartiteVal
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    c.supp ⊕ d.supp → V
  | Sum.inl x => x.1
  | Sum.inr y => y.1

/-- Distinct defect components have disjoint supports, so forgetting the side
tag in their cross graph remains injective. -/
theorem componentCrossBipartiteVal_injective_of_ne
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d) :
    Function.Injective (componentCrossBipartiteVal G c d) := by
  intro u v huv
  cases u with
  | inl x =>
      cases v with
      | inl y =>
          congr 1
          exact Subtype.ext huv
      | inr y =>
          exfalso
          apply hcd
          change x.1 = y.1 at huv
          have hxc :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff c x.1).mp x.2
          have hyd :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff d y.1).mp y.2
          rw [huv] at hxc
          exact hxc.symm.trans hyd
  | inr x =>
      cases v with
      | inl y =>
          exfalso
          apply hcd
          change x.1 = y.1 at huv
          have hxd :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff d x.1).mp x.2
          have hyc :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff c y.1).mp y.2
          rw [huv] at hxd
          exact hyc.symm.trans hxd
      | inr y =>
          congr 1
          exact Subtype.ext huv

/-- Every cross-graph edge is an ambient edge after forgetting its side tag. -/
theorem componentCrossBipartiteVal_map_adj
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) {u v : c.supp ⊕ d.supp}
    (huv : (componentCrossBipartiteGraph G c d).Adj u v) :
    G.Adj (componentCrossBipartiteVal G c d u)
      (componentCrossBipartiteVal G c d v) := by
  cases u with
  | inl x =>
      cases v with
      | inl y => simp [componentCrossBipartiteGraph] at huv
      | inr y => exact huv
  | inr y =>
      cases v with
      | inl x =>
          have hxy : G.Adj x.1 y.1 := huv
          exact hxy.symm
      | inr z => simp [componentCrossBipartiteGraph] at huv

/-- A cross graph between two distinct defect components of a C4-free graph
is itself C4-free.  No regularity or component-size assumptions are needed. -/
theorem componentCrossBipartiteGraph_not_containsC4_of_ne
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d) :
    ¬ containsC4 (c.supp ⊕ d.supp) (componentCrossBipartiteGraph G c d) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  refine ⟨componentCrossBipartiteVal G c d ∘ f, ?_, ?_⟩
  · exact (componentCrossBipartiteVal_injective_of_ne G c d hcd).comp hf
  · intro i j hij
    exact componentCrossBipartiteVal_map_adj G c d (hadj i j hij)

end

end Erdos85

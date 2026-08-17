import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity

/-! # Routing colors as regular bipartite factors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The bipartite graph whose cross edges have a fixed intermediate-component
color `d`. -/
def routingColorBipartiteGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph (c.supp ⊕ e.supp) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr z => d = crossIntermediateComponent G hfree hce x z
    | Sum.inr z, Sum.inl x => d = crossIntermediateComponent G hfree hce x z
    | _, _ => False
  symm := by
    constructor
    intro u v
    cases u <;> cases v <;> simp_all
  loopless := by
    constructor
    intro u
    cases u <;> simp

noncomputable instance routingColorBipartiteGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (routingColorBipartiteGraph G hfree c e hce d).Adj :=
  Classical.decRel _

@[simp] theorem routingColorBipartiteGraph_adj_inl_inr
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (z : e.supp) :
    (routingColorBipartiteGraph G hfree c e hce d).Adj
      (Sum.inl x) (Sum.inr z) ↔
        d = crossIntermediateComponent G hfree hce x z := by
  rfl

/-- The degree on the left is the corresponding routing-row color count. -/
theorem routingColorBipartiteGraph_degree_inl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) (x : c.supp) :
    (routingColorBipartiteGraph G hfree c e hce d).degree (Sum.inl x) =
      ((Finset.univ : Finset e.supp).filter fun z =>
        d = crossIntermediateComponent G hfree hce x z).card := by
  rw [← card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun z _ => Sum.inr z)
  · intro z hz
    exact ((routingColorBipartiteGraph G hfree c e hce d).mem_neighborFinset
      (Sum.inl x) (Sum.inr z)).mpr (Finset.mem_filter.mp hz).2
  · intro z₁ h₁ z₂ h₂ heq
    exact Sum.inr.inj heq
  · intro u hu
    have huAdj := ((routingColorBipartiteGraph G hfree c e hce d).mem_neighborFinset
      (Sum.inl x) u).mp hu
    cases u with
    | inl y => simp [routingColorBipartiteGraph] at huAdj
    | inr z =>
      exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huAdj⟩, rfl⟩

/-- The degree on the right is the corresponding routing-column color count. -/
theorem routingColorBipartiteGraph_degree_inr
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (d : (secondOrderDefectGraph G).ConnectedComponent) (z : e.supp) :
    (routingColorBipartiteGraph G hfree c e hce d).degree (Sum.inr z) =
      ((Finset.univ : Finset c.supp).filter fun x =>
        d = crossIntermediateComponent G hfree hce x z).card := by
  rw [← card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun x _ => Sum.inl x)
  · intro x hx
    exact ((routingColorBipartiteGraph G hfree c e hce d).mem_neighborFinset
      (Sum.inr z) (Sum.inl x)).mpr (Finset.mem_filter.mp hx).2
  · intro x₁ h₁ x₂ h₂ heq
    exact Sum.inl.inj heq
  · intro u hu
    have huAdj := ((routingColorBipartiteGraph G hfree c e hce d).mem_neighborFinset
      (Sum.inr z) u).mp hu
    cases u with
    | inl x =>
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huAdj⟩, rfl⟩
    | inr y => simp [routingColorBipartiteGraph] at huAdj

/-- Every routing-color factor between normalized size-two endpoint
components is 4-regular. -/
theorem binarySquare_regular_threeSizeTwoParts_routingColorBipartiteGraph_degree_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (he : e.supp.ncard = q * 2) :
    ∀ u, (routingColorBipartiteGraph G hfree c e hce d).degree u = 4 := by
  intro u
  cases u with
  | inl x =>
      rw [routingColorBipartiteGraph_degree_inl]
      exact binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
        G hfree hq hreg hcard c d e hce hc hd he x
  | inr z =>
      rw [routingColorBipartiteGraph_degree_inr]
      exact binarySquare_regular_threeSizeTwoParts_routing_column_card_eq_four
        G hfree hq hreg hcard c d e hce hc hd he z

/-- Every cross edge of the complete endpoint bipartite graph has exactly one
intermediate-component routing color. -/
theorem existsUnique_routingColorBipartiteGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (x : c.supp) (z : e.supp) :
    ∃! d : (secondOrderDefectGraph G).ConnectedComponent,
      (routingColorBipartiteGraph G hfree c e hce d).Adj
        (Sum.inl x) (Sum.inr z) := by
  let d := crossIntermediateComponent G hfree hce x z
  refine ⟨d, rfl, ?_⟩
  intro d' hd'
  exact hd'

end

end Erdos85

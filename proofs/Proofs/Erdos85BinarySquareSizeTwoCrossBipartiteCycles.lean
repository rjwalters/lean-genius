import Proofs.Erdos85BinarySquareSizeTwoCrossFactorPathBalance

/-! # Cross blocks as canonical bipartite cycle systems -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The bipartite graph represented by the ambient adjacency block between
two defect components. -/
def componentCrossBipartiteGraph
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph (c.supp ⊕ d.supp) where
  Adj u v := match u, v with
    | Sum.inl x, Sum.inr y => G.Adj x.1 y.1
    | Sum.inr y, Sum.inl x => G.Adj x.1 y.1
    | _, _ => False
  symm := by
    constructor
    intro u v
    cases u <;> cases v <;> simp [adj_comm]
  loopless := by
    constructor
    intro u
    cases u <;> simp

noncomputable instance componentCrossBipartiteGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (componentCrossBipartiteGraph G c d).Adj :=
  Classical.decRel _

@[simp] theorem componentCrossBipartiteGraph_adj_inl_inr
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (y : d.supp) :
    (componentCrossBipartiteGraph G c d).Adj (Sum.inl x) (Sum.inr y) ↔
      G.Adj x.1 y.1 := by
  rfl

@[simp] theorem componentCrossBipartiteGraph_adj_inr_inl
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (x : c.supp) (y : d.supp) :
    (componentCrossBipartiteGraph G c d).Adj (Sum.inr y) (Sum.inl x) ↔
      G.Adj x.1 y.1 := by
  rfl

/-- The left degree in the cross bipartite graph is the corresponding cross
row cardinality. -/
theorem componentCrossBipartiteGraph_degree_inl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (x : c.supp) :
    (componentCrossBipartiteGraph G c d).degree (Sum.inl x) =
      (componentCrossNeighborFinset G d x).card := by
  rw [← card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun y _ => Sum.inr y)
  · intro y hy
    rw [(componentCrossBipartiteGraph G c d).mem_neighborFinset]
    exact (Finset.mem_filter.mp hy).2
  · intro y₁ h₁ y₂ h₂ hy
    exact Sum.inr.inj hy
  · intro v hv
    rw [(componentCrossBipartiteGraph G c d).mem_neighborFinset] at hv
    cases v with
    | inl y => simp [componentCrossBipartiteGraph] at hv
    | inr y =>
      refine ⟨y, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩

/-- The right degree in the cross bipartite graph is the reverse cross-row
cardinality. -/
theorem componentCrossBipartiteGraph_degree_inr
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (y : d.supp) :
    (componentCrossBipartiteGraph G c d).degree (Sum.inr y) =
      (componentCrossNeighborFinset G c y).card := by
  rw [← card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun x _ => Sum.inl x)
  · intro x hx
    rw [(componentCrossBipartiteGraph G c d).mem_neighborFinset]
    exact (Finset.mem_filter.mp hx).2.symm
  · intro x₁ h₁ x₂ h₂ hx
    exact Sum.inl.inj hx
  · intro v hv
    rw [(componentCrossBipartiteGraph G c d).mem_neighborFinset] at hv
    cases v with
    | inl x =>
      refine ⟨x, ?_, rfl⟩
      have hv' : G.Adj x.1 y.1 := hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'.symm⟩
    | inr x => simp [componentCrossBipartiteGraph] at hv

/-- Between two normalized size-two defect components the canonical cross
bipartite graph is 2-regular. -/
theorem binarySquare_regular_twoSizeTwoParts_crossBipartiteGraph_degree_two
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
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    ∀ v, (componentCrossBipartiteGraph G c d).degree v = 2 := by
  obtain ⟨_htranspose, hleft, hright⟩ :=
    binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
      G hfree hq hreg hcard c d hc hd
  intro v
  cases v with
  | inl x => rw [componentCrossBipartiteGraph_degree_inl]; exact hleft x
  | inr y => rw [componentCrossBipartiteGraph_degree_inr]; exact hright y

/-- Consequently every connected component of a size-two cross block is a
cycle, in Mathlib's `IsCycles` interface. -/
theorem binarySquare_regular_twoSizeTwoParts_crossBipartiteGraph_isCycles
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
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    (componentCrossBipartiteGraph G c d).IsCycles := by
  intro v _hv
  rw [← Set.fintypeCard_eq_ncard,
    (componentCrossBipartiteGraph G c d).card_neighborSet_eq_degree,
    binarySquare_regular_twoSizeTwoParts_crossBipartiteGraph_degree_two
      G hfree hq hreg hcard c d hc hd v]

end

end Erdos85

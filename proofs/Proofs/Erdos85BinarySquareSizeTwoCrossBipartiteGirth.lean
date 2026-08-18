import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteParity

/-! # Girth of off-diagonal size-two cross blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Forget which side of a component cross block a vertex occupies. -/
def componentCrossVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) :
    c.supp ⊕ d.supp → V
  | Sum.inl x => x.1
  | Sum.inr y => y.1

/-- Distinct defect components make the forgetful cross-vertex map
injective. -/
theorem componentCrossVertex_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d) :
    Function.Injective (componentCrossVertex G c d) := by
  intro u v huv
  cases u with
  | inl x =>
    cases v with
    | inl y => exact congrArg Sum.inl (Subtype.ext huv)
    | inr y =>
      exfalso
      apply hcd
      have hx := (ConnectedComponent.mem_supp_iff c x.1).mp x.2
      have hy := (ConnectedComponent.mem_supp_iff d y.1).mp y.2
      rw [← hx, ← hy]
      exact congrArg (secondOrderDefectGraph G).connectedComponentMk huv
  | inr x =>
    cases v with
    | inl y =>
      exfalso
      apply hcd
      have hx := (ConnectedComponent.mem_supp_iff d x.1).mp x.2
      have hy := (ConnectedComponent.mem_supp_iff c y.1).mp y.2
      rw [← hx, ← hy]
      exact (congrArg (secondOrderDefectGraph G).connectedComponentMk huv).symm
    | inr y => exact congrArg Sum.inr (Subtype.ext huv)

/-- Every edge of the cross-block graph is an ambient edge. -/
theorem componentCrossVertex_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent) {u v : c.supp ⊕ d.supp}
    (huv : (componentCrossBipartiteGraph G c d).Adj u v) :
    G.Adj (componentCrossVertex G c d u) (componentCrossVertex G c d v) := by
  cases u with
  | inl x =>
    cases v with
    | inl y => simp [componentCrossBipartiteGraph] at huv
    | inr y => exact huv
  | inr x =>
    cases v with
    | inl y =>
      have huv' : G.Adj y.1 x.1 := huv
      exact huv'.symm
    | inr y => simp [componentCrossBipartiteGraph] at huv

/-- An off-diagonal cross-block graph inherits ambient four-cycle freeness. -/
theorem componentCrossBipartiteGraph_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d) :
    ¬ containsC4 (c.supp ⊕ d.supp) (componentCrossBipartiteGraph G c d) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  refine ⟨fun i => componentCrossVertex G c d (f i),
    (componentCrossVertex_injective G c d hcd).comp hf, ?_⟩
  intro i j hij
  exact componentCrossVertex_adj G c d (hadj i j hij)

/-- No connected component of an off-diagonal size-two cross block has order
four. -/
theorem binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_ne_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    e.supp.ncard ≠ 4 := by
  intro he
  apply componentCrossBipartiteGraph_not_containsC4 G hfree c d hcd
  exact twoRegular_containsC4_of_component_order_four
    (componentCrossBipartiteGraph G c d)
    (binarySquare_regular_twoSizeTwoParts_crossBipartiteGraph_degree_two
      G hfree hq hreg hcard c d hc hd) e he

/-- Every connected component of an off-diagonal size-two cross block is an
even cycle of order at least six. -/
theorem binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_six_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (e : (componentCrossBipartiteGraph G c d).ConnectedComponent) :
    6 ≤ e.supp.ncard := by
  let H := componentCrossBipartiteGraph G c d
  have hdeg : ∀ v, H.degree v = 2 :=
    binarySquare_regular_twoSizeTwoParts_crossBipartiteGraph_degree_two
      G hfree hq hreg hcard c d hc hd
  obtain ⟨x, p, hp, hpverts, _hgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph H hdeg e
  have hlen : p.length = e.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = e.supp.ncard := congrArg Set.ncard hpverts
  have hthree : 3 ≤ e.supp.ncard := by
    rw [← hlen]
    exact hp.three_le_length
  have heven :=
    binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_even
      G hfree hq hreg hcard c d hc hd e
  have hne :=
    binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_ne_four
      G hfree hq hreg hcard c d hcd hc hd e
  obtain ⟨k, hk⟩ := heven
  omega

end

end Erdos85

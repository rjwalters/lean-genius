import Proofs.Erdos85BinarySquareRoutingRowStarDecomposition

/-! # Canonical center pairs across defect-adjacent roots -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A target vertex records its canonical common-neighbor center with each of
two roots. -/
def crossRootCenterPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (w : e.supp) : V × V :=
  (crossCommonNeighbor G hfree hde x w,
    crossCommonNeighbor G hfree hde y w)

/-- If the two roots are adjacent in the second-order defect graph, their
center-pair encoding of a remote component is injective.  Equality of both
centers for two different target vertices would give a four-cycle; equality
of the two centers with each other would give the defect-adjacent roots a
common neighbor. -/
theorem crossRootCenterPair_injective_of_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp)
    (hxyD : (secondOrderDefectGraph G).Adj x.1 y.1) :
    Function.Injective (crossRootCenterPair G hfree hde x y) := by
  intro w₁ w₂ hpairs
  let u := crossCommonNeighbor G hfree hde x w₁
  let v := crossCommonNeighbor G hfree hde y w₁
  have hxy : x.1 ≠ y.1 := (secondOrderDefectGraph G).ne_of_adj hxyD
  have huSpec := crossCommonNeighbor_spec G hfree hde x w₁
  have hvSpec := crossCommonNeighbor_spec G hfree hde y w₁
  have huv : u ≠ v := by
    intro huv
    have hyu : G.Adj y.1 u := by
      rw [huv]
      exact hvSpec.1
    apply not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy
      huSpec.1 hyu
    exact hxyD
  have huEq :
      crossCommonNeighbor G hfree hde x w₁ =
        crossCommonNeighbor G hfree hde x w₂ :=
    congrArg Prod.fst hpairs
  have hvEq :
      crossCommonNeighbor G hfree hde y w₁ =
        crossCommonNeighbor G hfree hde y w₂ :=
    congrArg Prod.snd hpairs
  have huSpec₂ := crossCommonNeighbor_spec G hfree hde x w₂
  have hvSpec₂ := crossCommonNeighbor_spec G hfree hde y w₂
  rw [← huEq] at huSpec₂
  rw [← hvEq] at hvSpec₂
  apply Subtype.ext
  by_contra hw
  apply hfree
  exact containsC4_of_two_common huv hw
    huSpec.2 hvSpec.2 huSpec₂.2 hvSpec₂.2

/-- The fiber of the first-center coordinate is exactly that center's target
selector.  Together with injectivity, this identifies the cross-root encoding
as the edge set of a simple bipartite transition graph. -/
theorem crossRootCenterPair_fst_fiber_eq_componentCrossNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (u : c.supp)
    (hxu : G.Adj x.1 u.1) :
    ((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).1 = u.1) =
        componentCrossNeighborFinset G e u := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    crossRootCenterPair, componentCrossNeighborFinset]
  constructor
  · intro hcenter
    have hspec := (crossCommonNeighbor_spec G hfree hde x w).2
    rw [hcenter] at hspec
    exact hspec.symm
  · intro huw
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hde x w
      ⟨hxu, huw.symm⟩

/-- Symmetric second-coordinate fiber description. -/
theorem crossRootCenterPair_snd_fiber_eq_componentCrossNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (u : c.supp)
    (hyu : G.Adj y.1 u.1) :
    ((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).2 = u.1) =
        componentCrossNeighborFinset G e u := by
  classical
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    crossRootCenterPair, componentCrossNeighborFinset]
  constructor
  · intro hcenter
    have hspec := (crossCommonNeighbor_spec G hfree hde y w).2
    rw [hcenter] at hspec
    exact hspec.symm
  · intro huw
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hde y w
      ⟨hyu, huw.symm⟩

/-- In the normalized size-two regime every first-coordinate transition
fiber has degree two. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPair_fst_fiber_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp) (u : c.supp) (hxu : G.Adj x.1 u.1) :
    (((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).1 = u.1).card) = 2 := by
  rw [crossRootCenterPair_fst_fiber_eq_componentCrossNeighborFinset
    G hfree hde x y u hxu]
  rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
  exact binarySquare_regular_sizeTwoPart_selector_card
    G hfree hq hreg hcard e he u.1

/-- In the normalized size-two regime every second-coordinate transition
fiber has degree two. -/
theorem binarySquare_regular_sizeTwo_crossRootCenterPair_snd_fiber_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ z, G.degree z = q) (hcard : Fintype.card V = q * q)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (he : e.supp.ncard = q * 2)
    (x y : d.supp) (u : c.supp) (hyu : G.Adj y.1 u.1) :
    (((Finset.univ : Finset e.supp).filter fun w =>
      (crossRootCenterPair G hfree hde x y w).2 = u.1).card) = 2 := by
  rw [crossRootCenterPair_snd_fiber_eq_componentCrossNeighborFinset
    G hfree hde x y u hyu]
  rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
  exact binarySquare_regular_sizeTwoPart_selector_card
    G hfree hq hreg hcard e he u.1

end

end Erdos85

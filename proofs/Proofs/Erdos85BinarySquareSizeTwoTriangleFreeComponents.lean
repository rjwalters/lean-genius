import Proofs.Erdos85BinarySquareRegularParity

/-! # Triangle-free coloring of size-two internal components

For a normalized size-two second-order defect component at even square order,
triangle-free degree two propagates along the internal ambient graph.  Thus the
status is constant on every internal connected component.  This packages the
exact dichotomy used by the `[6,2]` synchronized-model analysis.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a normalized size-two defect component, triangle-free degree two is
constant along every walk in the induced ambient graph. -/
theorem binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x y : c.supp)
    (hxy : (G.induce c.supp).Reachable x y) :
    (triangleFreeEdgeGraph G).degree x.1 = 2 ↔
      (triangleFreeEdgeGraph G).degree y.1 = 2 := by
  have hwalk : Relation.ReflTransGen (G.induce c.supp).Adj x y :=
    ((G.induce c.supp).reachable_iff_reflTransGen x y).mp hxy
  have hprop : ∀ {a b : c.supp},
      Relation.ReflTransGen (G.induce c.supp).Adj a b →
      (triangleFreeEdgeGraph G).degree a.1 = 2 →
      (triangleFreeEdgeGraph G).degree b.1 = 2 := by
    intro a b hab ha
    induction hab with
    | refl => exact ha
    | tail _ hbc ih =>
        exact
          (binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_adj
            G hfree hq hqEven hreg hcard c hc _ _ hbc).mp ih
  constructor
  · exact hprop hwalk
  · exact hprop
      (((G.induce c.supp).reachable_iff_reflTransGen y x).mp hxy.symm)

/-- Consequently, the triangle-free degree itself is constant on every
connected component of the internal ambient graph. -/
theorem binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_of_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x y : c.supp)
    (hxy : (G.induce c.supp).Reachable x y) :
    (triangleFreeEdgeGraph G).degree x.1 =
      (triangleFreeEdgeGraph G).degree y.1 := by
  have hiff :=
    binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
      G hfree hq hqEven hreg hcard c hc x y hxy
  rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree hq hqEven hreg hcard c hc x with hx | hx <;>
    rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree hq hqEven hreg hcard c hc y with hy | hy
  · omega
  · have hxTwo := hiff.mpr hy
    omega
  · have hyTwo := hiff.mp hx
    omega
  · omega

/-- If both triangle-free colors occur in a normalized size-two defect
component, then its internal ambient graph is disconnected.  Thus after the
two uniform branches are excluded, the residual is genuinely a multi-cycle
problem rather than another connected-factor case. -/
theorem binarySquare_regular_sizeTwoPart_internal_not_connected_of_mixed_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x y : c.supp)
    (hx : (triangleFreeEdgeGraph G).degree x.1 = 0)
    (hy : (triangleFreeEdgeGraph G).degree y.1 = 2) :
    ¬ (G.induce c.supp).Connected := by
  intro hconn
  have hdeg :=
    binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_of_reachable
      G hfree hq hqEven hreg hcard c hc x y (hconn.preconnected x y)
  omega

#print axioms
  Erdos85.binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_reachable
#print axioms
  Erdos85.binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_of_reachable
#print axioms
  Erdos85.binarySquare_regular_sizeTwoPart_internal_not_connected_of_mixed_triangleFree

end

end Erdos85

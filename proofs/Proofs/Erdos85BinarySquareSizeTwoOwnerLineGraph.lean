import Proofs.Erdos85BinarySquareSizeTwoSelectorGraph

/-! # Size-two owner colors are selector line graphs

For a normalized size-two defect component, ambient vertices are already
known to be in bijection with the non-defect pairs in that component.  This
file records the graph-specific content retained by that bijection: the owner
graph is precisely the intersection graph of those pairs.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The intersection graph on the non-defect two-element selectors belonging
to one defect component.  This is the concrete finset model of the line graph
of the selector-complement graph. -/
def sizeTwoSelectorIntersectionGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    SimpleGraph {s : Finset V // ∃ u v : c.supp,
      u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1 ∧ s = {u.1, v.1}} where
  Adj s t := s ≠ t ∧ (s.1 ∩ t.1).Nonempty
  symm := ⟨by
    intro s t h
    exact ⟨h.1.symm, by simpa [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by intro s h; exact h.1 rfl⟩

noncomputable instance sizeTwoSelectorIntersectionGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    DecidableRel (sizeTwoSelectorIntersectionGraph G c).Adj :=
  Classical.decRel _

/-- **Owner-line-graph identification.**  Under the canonical selector
bijection, owner adjacency is exactly intersection of the corresponding
non-defect pairs. -/
theorem binarySquare_regular_sizeTwoPart_exists_ownerGraph_iso_selectorIntersectionGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    ∃ e : componentOwnerGraph G (secondOrderDefectGraph G) c ≃g
        sizeTwoSelectorIntersectionGraph G c,
      ∀ x, (e x).1 =
        componentNeighborFinset G (secondOrderDefectGraph G) c x := by
  obtain ⟨E, hE⟩ :=
    binarySquare_regular_sizeTwoPart_selector_equiv_nondefectPairs
      G hfree hq hreg hcard c hc
  let e : componentOwnerGraph G (secondOrderDefectGraph G) c ≃g
      sizeTwoSelectorIntersectionGraph G c :=
    { toEquiv := E
      map_rel_iff' := by
        intro x y
        simp only [componentOwnerGraph, sizeTwoSelectorIntersectionGraph]
        rw [hE x, hE y]
        exact and_congr E.injective.eq_iff.not Iff.rfl }
  exact ⟨e, hE⟩

/-- Pointwise form of the line-graph identification: two ambient vertices
have owner color `c` iff their canonical selector pairs in `c` intersect. -/
theorem binarySquare_regular_sizeTwoPart_ownerAdj_iff_selector_intersects
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : V) :
    (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y ↔
      x ≠ y ∧
        (componentNeighborFinset G (secondOrderDefectGraph G) c x ∩
          componentNeighborFinset G (secondOrderDefectGraph G) c y).Nonempty := by
  rfl

/-- The graph-specific cross-coordinate law: an edge in owner color `c`
becomes a pair of disjoint selectors in every distinct color `d`.  Under the
two line-graph identifications, intersecting edges in one selector graph are
therefore sent to disjoint edges in the other. -/
theorem componentOwnerGraph_adj_implies_other_selector_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c d : (secondOrderDefectGraph G).ConnectedComponent} (hcd : c ≠ d)
    {x y : V}
    (hxy : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y) :
    Disjoint
      (componentNeighborFinset G (secondOrderDefectGraph G) d x)
      (componentNeighborFinset G (secondOrderDefectGraph G) d y) := by
  let D := secondOrderDefectGraph G
  have hxyData :=
    (componentOwnerGraph_adj G D c x y).mp hxy
  obtain ⟨z, hz⟩ := hxyData.2
  have hzData := Finset.mem_inter.mp hz
  have hzx : G.Adj x z :=
    (G.mem_neighborFinset x z).mp (Finset.mem_filter.mp hzData.1).1
  have hzy : G.Adj y z :=
    (G.mem_neighborFinset y z).mp (Finset.mem_filter.mp hzData.2).1
  have hnotD : ¬ D.Adj x y :=
    not_secondOrderDefect_adj_of_commonNeighbor G hfree hxyData.1 hzx hzy
  obtain ⟨e, he, heUnique⟩ :=
    (not_secondOrderDefect_adj_iff_existsUnique_component_selector_inter_nonempty
      G hfree hxyData.1).mp hnotD
  have hc : c = e := heUnique c hxyData.2
  rw [Finset.disjoint_left]
  intro w hwx hwy
  have hd : d = e := heUnique d ⟨w, Finset.mem_inter.mpr ⟨hwx, hwy⟩⟩
  exact hcd (hc.trans hd.symm)

/-- Two normalized size-two coordinates give orthogonal edge labelings:
intersection adjacency in the first selector graph forces disjointness in the
second.  This is the graph-isomorphism form used by orthogonal-double-cover
and perfect-matching arguments. -/
theorem binarySquare_regular_twoSizeTwoParts_exists_orthogonal_ownerLineGraph_isos
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
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    ∃ ec : componentOwnerGraph G (secondOrderDefectGraph G) c ≃g
        sizeTwoSelectorIntersectionGraph G c,
      ∃ ed : componentOwnerGraph G (secondOrderDefectGraph G) d ≃g
        sizeTwoSelectorIntersectionGraph G d,
        (∀ x, (ec x).1 =
          componentNeighborFinset G (secondOrderDefectGraph G) c x) ∧
        (∀ x, (ed x).1 =
          componentNeighborFinset G (secondOrderDefectGraph G) d x) ∧
        ∀ ⦃x y : V⦄,
          (sizeTwoSelectorIntersectionGraph G c).Adj (ec x) (ec y) →
            Disjoint (ed x).1 (ed y).1 := by
  obtain ⟨ec, hec⟩ :=
    binarySquare_regular_sizeTwoPart_exists_ownerGraph_iso_selectorIntersectionGraph
      G hfree hq hreg hcard c hc
  obtain ⟨ed, hed⟩ :=
    binarySquare_regular_sizeTwoPart_exists_ownerGraph_iso_selectorIntersectionGraph
      G hfree hq hreg hcard d hd
  refine ⟨ec, ed, hec, hed, ?_⟩
  intro x y hxy
  have howner :
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y :=
    ec.map_rel_iff.mp hxy
  have hdis := componentOwnerGraph_adj_implies_other_selector_disjoint
    G hfree hcd howner
  simpa only [hed x, hed y] using hdis

end

end Erdos85

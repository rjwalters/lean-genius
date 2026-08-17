import Proofs.Erdos85BinarySquareRegularParity

/-!
# Selector graph of a normalized size-two defect component

For a defect component of order `2q`, each ambient vertex selects a pair of
points in the component.  The resulting graph on the component is exactly the
loopless complement of the induced defect graph.  This packages the pairwise
theorems as the graph object needed by blockwise spectra and fourth moments.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two component points are adjacent when they form the selector of an
ambient vertex. -/
def sizeTwoSelectorGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) : SimpleGraph c.supp where
  Adj u v := u ≠ v ∧ ∃ x : V,
    componentNeighborFinset G D c x = {u.1, v.1}
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨x, hx⟩ := h.2
    refine ⟨x, ?_⟩
    simpa [Finset.pair_comm] using hx⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

noncomputable instance sizeTwoSelectorGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent] (c : D.ConnectedComponent) :
    DecidableRel (sizeTwoSelectorGraph G D c).Adj := Classical.decRel _

/-- The loopless complement of the defect graph induced on one component. -/
def componentDefectComplementGraph
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent) :
    SimpleGraph c.supp where
  Adj u v := u ≠ v ∧ ¬D.Adj u.1 v.1
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, fun hvu => h.2 hvu.symm⟩⟩
  loopless := ⟨by
    intro u h
    exact h.1 rfl⟩

@[simp] theorem componentDefectComplementGraph_eq_compl_induce
    {V : Type*} (D : SimpleGraph V) (c : D.ConnectedComponent) :
    componentDefectComplementGraph D c = (D.induce c.supp)ᶜ := by
  ext u v
  rfl

/-- **Size-two selector-complement identity.**  The graph of ambient selector
pairs is exactly the complement of the defect graph inside the component. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_eq_componentDefectComplementGraph
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
    sizeTwoSelectorGraph G (secondOrderDefectGraph G) c =
      componentDefectComplementGraph (secondOrderDefectGraph G) c := by
  ext u v
  change
    (u ≠ v ∧ ∃ x : V,
      componentNeighborFinset G (secondOrderDefectGraph G) c x = {u.1, v.1}) ↔
    (u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1)
  constructor
  · rintro ⟨huv, hpair⟩
    exact ⟨huv,
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u v huv).mp hpair⟩
  · rintro ⟨huv, hnotD⟩
    exact ⟨huv,
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u v huv).mpr hnotD⟩

/-- The size-two selector graph is `q`-regular on `2q` component points. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_degree
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
    (hc : c.supp.ncard = q * 2) (u : c.supp) :
    (sizeTwoSelectorGraph G (secondOrderDefectGraph G) c).degree u = q := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have hsubset : D.neighborSet u.1 ⊆ c.supp := by
    intro v hv
    have huv : D.Adj u.1 v := hv
    have hcomp : D.connectedComponentMk u.1 = D.connectedComponentMk v :=
      SimpleGraph.ConnectedComponent.sound huv.reachable
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr
      (hcomp.symm.trans
        ((SimpleGraph.ConnectedComponent.mem_supp_iff c u.1).mp u.2))
  have hindDegree : (D.induce c.supp).degree u = q - 1 := by
    rw [SimpleGraph.degree_induce_of_neighborSet_subset hsubset, hDreg]
  letI : DecidableRel ((D.induce c.supp)ᶜ).Adj := Classical.decRel _
  have hneighbors :
      (sizeTwoSelectorGraph G D c).neighborFinset u =
        ((D.induce c.supp)ᶜ).neighborFinset u := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset]
    change
      (u ≠ v ∧ ∃ x : V, componentNeighborFinset G D c x = {u.1, v.1}) ↔
        (u ≠ v ∧ ¬D.Adj u.1 v.1)
    constructor
    · rintro ⟨huv, hpair⟩
      exact ⟨huv,
        (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
          G hfree hq hreg hcard c hc u v huv).mp hpair⟩
    · rintro ⟨huv, hnotD⟩
      exact ⟨huv,
        (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
          G hfree hq hreg hcard c hc u v huv).mpr hnotD⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    hneighbors, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.degree_compl, hindDegree]
  have hcardSupp : Fintype.card c.supp = q * 2 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = q * 2 := hc
  rw [hcardSupp]
  omega

end

end Erdos85

import Proofs.Erdos85BinarySquareTwoOwnerOrientedRectangles

/-! # Same-orientation residue at a defect edge

At a defect edge, remove the defect neighborhoods of its two roots.  Every
remaining vertex is eligible to carry owner colors on both legs.  The two
mixed orientations occupy an exactly known disjoint subset, leaving a large
local residue for the same-owner orientations.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Vertices whose two legs from `x` and `y` are both nonedges of `D`. -/
def twoLegDefectEligible
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (x y : V) : Finset V :=
  Finset.univ \ (D.neighborFinset x ∪ D.neighborFinset y)

/-- Two degree-`r` defect neighborhoods exclude at most `2r` vertices. -/
theorem card_sub_two_mul_degree_le_twoLegDefectEligible
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (r : ℕ) (hreg : ∀ z, D.degree z = r) (x y : V) :
    Fintype.card V - 2 * r ≤ (twoLegDefectEligible D x y).card := by
  have hunion : (D.neighborFinset x ∪ D.neighborFinset y).card ≤ 2 * r := by
    calc
      (D.neighborFinset x ∪ D.neighborFinset y).card ≤
          (D.neighborFinset x).card + (D.neighborFinset y).card :=
        Finset.card_union_le _ _
      _ = 2 * r := by
        rw [D.card_neighborFinset_eq_degree, D.card_neighborFinset_eq_degree,
          hreg x, hreg y]
        omega
  rw [twoLegDefectEligible, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ]
  omega

/-- Every mixed-owner middle is eligible on both defect legs. -/
theorem coloredTwoStepMiddles_subset_twoLegDefectEligible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (x y : V) :
    coloredTwoStepMiddles
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) x y ⊆
      twoLegDefectEligible (secondOrderDefectGraph G) x y := by
  intro z hz
  have hz' := (Finset.mem_filter.mp hz).2
  have hnotxz := componentOwnerGraph_adj_not_secondOrderDefect_adj
    G hfree a hz'.1
  have hnotzy := componentOwnerGraph_adj_not_secondOrderDefect_adj
    G hfree b hz'.2
  simp only [twoLegDefectEligible, Finset.mem_sdiff, Finset.mem_univ,
    Finset.mem_union, SimpleGraph.mem_neighborFinset, true_and]
  exact not_or_intro hnotxz (fun hyz => hnotzy hyz.symm)

/-- After removing both mixed orientations at a defect edge, at least
`q² - 2(q-1) - 2m_a m_b` eligible vertices remain.  In a genuine
two-component stratum, owner exhaustion identifies this as same-owner
pressure. -/
theorem binarySquare_regular_defectEdge_twoOwnerMixedResidue_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (q * q - 2 * (q - 1)) - 2 * m_a * m_b ≤
      (twoLegDefectEligible (secondOrderDefectGraph G) x y \ (
        coloredTwoStepMiddles
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) b) x y ∪
        coloredTwoStepMiddles
          (componentOwnerGraph G (secondOrderDefectGraph G) b)
          (componentOwnerGraph G (secondOrderDefectGraph G) a) x y)).card := by
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let M := coloredTwoStepMiddles A B x y ∪ coloredTwoStepMiddles B A x y
  have hDreg : ∀ z, D.degree z = q - 1 := by
    have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
      rw [hcard]
      calc
        q * q = q * ((q - 1) + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
        _ = q * (q - 1) + q := by ring
        _ = q * (q - 1) + 3 + (q - 3) := by omega
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change D.degree z = (q - 3) + 2 at h
    omega
  have helig : q * q - 2 * (q - 1) ≤
      (twoLegDefectEligible D x y).card := by
    rw [← hcard]
    exact card_sub_two_mul_degree_le_twoLegDefectEligible
      D (q - 1) hDreg x y
  have hxy : x ≠ y := hxyD.ne
  have hnotA : ¬ A.Adj x y := by
    intro h
    exact (componentOwnerGraph_adj_not_secondOrderDefect_adj G hfree a h) hxyD
  have hnotB : ¬ B.Adj x y := by
    intro h
    exact (componentOwnerGraph_adj_not_secondOrderDefect_adj G hfree b h) hxyD
  have hMcard : M.card = 2 * m_a * m_b := by
    exact binarySquare_regular_two_orientedOwnerRectangles_union_card
      G hfree hq hreg hcard a b hab ha hb hxy hnotA hnotB
  have hMsub : M ⊆ twoLegDefectEligible D x y := by
    apply Finset.union_subset
    · exact coloredTwoStepMiddles_subset_twoLegDefectEligible
        G hfree a b x y
    · exact coloredTwoStepMiddles_subset_twoLegDefectEligible
        G hfree b a x y
  change _ ≤ (twoLegDefectEligible D x y \ M).card
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hMsub, hMcard]
  omega

end

end Erdos85

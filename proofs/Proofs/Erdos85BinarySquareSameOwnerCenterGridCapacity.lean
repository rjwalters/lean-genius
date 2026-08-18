import Proofs.Erdos85BinarySquareTwoOwnerDefectEdgeResidue
import Proofs.Erdos85BinarySquareMixedOwnerRectangleRouting
import Proofs.Erdos85RoutingOwnerRainbowHexagon

/-! # Same-owner middles inject into the center grid -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A canonical owner-component common neighbor, with an irrelevant fallback
off owner edges. -/
def componentOwnerCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) (x z : V) : V :=
  if h : (componentOwnerGraph G D owner).Adj x z then
    (Classical.choose
      (componentOwnerGraph_adj_exists_owner_commonNeighbor G D owner h)).1
  else x

theorem componentOwnerCenter_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {x z : V}
    (h : (componentOwnerGraph G D owner).Adj x z) :
    componentOwnerCenter G D owner x z ∈ owner.supp ∧
      G.Adj x (componentOwnerCenter G D owner x z) ∧
      G.Adj z (componentOwnerCenter G D owner x z) := by
  rw [componentOwnerCenter, dif_pos h]
  let u := Classical.choose
    (componentOwnerGraph_adj_exists_owner_commonNeighbor G D owner h)
  have hu := Classical.choose_spec
    (componentOwnerGraph_adj_exists_owner_commonNeighbor G D owner h)
  exact ⟨u.2, hu.1, hu.2⟩

/-- At a defect edge, same-owner middles inject into the product of the two
owner selectors. -/
theorem sameOwner_coloredTwoStepMiddles_card_le_centerGrid
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) x y).card ≤
      (componentNeighborFinset G (secondOrderDefectGraph G) owner x).card *
        (componentNeighborFinset G (secondOrderDefectGraph G) owner y).card := by
  classical
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D owner
  let S := coloredTwoStepMiddles O O x y
  let X := componentNeighborFinset G D owner x
  let Y := componentNeighborFinset G D owner y
  let f : {z // z ∈ S} → V × V := fun z =>
    (componentOwnerCenter G D owner x z.1,
      componentOwnerCenter G D owner y z.1)
  have hfmem : ∀ z : {z // z ∈ S}, f z ∈ X ×ˢ Y := by
    intro z
    have hz := (Finset.mem_filter.mp z.2).2
    have hu := componentOwnerCenter_spec G D owner hz.1
    have hv := componentOwnerCenter_spec G D owner hz.2.symm
    rw [Finset.mem_product]
    constructor
    · change componentOwnerCenter G D owner x z.1 ∈
        componentNeighborFinset G D owner x
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x _).mpr hu.2.1,
          (ConnectedComponent.mem_supp_iff owner _).mp hu.1⟩
    · change componentOwnerCenter G D owner y z.1 ∈
        componentNeighborFinset G D owner y
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset y _).mpr hv.2.1,
          (ConnectedComponent.mem_supp_iff owner _).mp hv.1⟩
  have hfinj : Function.Injective f := by
    intro z₁ z₂ hpair
    have hz₁ := (Finset.mem_filter.mp z₁.2).2
    have hz₂ := (Finset.mem_filter.mp z₂.2).2
    let u := componentOwnerCenter G D owner x z₁.1
    let v := componentOwnerCenter G D owner y z₁.1
    have hu₁ := componentOwnerCenter_spec G D owner hz₁.1
    have hv₁ := componentOwnerCenter_spec G D owner hz₁.2.symm
    have huEq : componentOwnerCenter G D owner x z₁.1 =
        componentOwnerCenter G D owner x z₂.1 := congrArg Prod.fst hpair
    have hvEq : componentOwnerCenter G D owner y z₁.1 =
        componentOwnerCenter G D owner y z₂.1 := congrArg Prod.snd hpair
    have hu₂ := componentOwnerCenter_spec G D owner hz₂.1
    have hv₂ := componentOwnerCenter_spec G D owner hz₂.2.symm
    rw [← huEq] at hu₂
    rw [← hvEq] at hv₂
    have huv : u ≠ v := by
      intro huv
      apply (componentOwnerGraph_adj_not_secondOrderDefect_adj G hfree owner ?_)
        hxyD
      exact componentOwnerGraph_adj_of_commonNeighbor_mem_owner
        G D owner hxyD.ne hu₁.1 hu₁.2.1 (by simpa [u, v, huv] using hv₁.2.1)
    apply Subtype.ext
    by_contra hzNe
    apply hfree
    exact containsC4_of_two_common huv hzNe
      hu₁.2.2 hv₁.2.2 hu₂.2.2 hv₂.2.2
  have himage : S.attach.image f ⊆ X ×ˢ Y := by
    intro p hp
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hp
    exact hfmem z
  calc
    S.card = S.attach.card := by simp
    _ = (S.attach.image f).card :=
      (Finset.card_image_of_injective _ hfinj).symm
    _ ≤ (X ×ˢ Y).card := Finset.card_le_card himage
    _ = X.card * Y.card := Finset.card_product X Y

/-- In a normalized component of size `qm`, the same-owner middle capacity
at every defect edge is at most `m²`. -/
theorem binarySquare_regular_sameOwner_defectEdge_card_le_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (howner : owner.supp.ncard = q * m)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) owner)
      (componentOwnerGraph G (secondOrderDefectGraph G) owner) x y).card ≤
        m * m := by
  have hsel (z : V) :
      (componentNeighborFinset G (secondOrderDefectGraph G) owner z).card = m := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk z) owner (x := z) (by rfl)
    rw [howner] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  simpa [hsel x, hsel y] using
    (sameOwner_coloredTwoStepMiddles_card_le_centerGrid
      G hfree owner hxyD)

/-- The two-owner defect-edge sandwich: certified same-owner pressure is
bounded above by the sum of the two center-grid capacities. -/
theorem binarySquare_regular_twoComponents_defectEdge_sameOwner_sandwich
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b)
    {m_a m_b : ℕ} (ha : a.supp.ncard = q * m_a)
    (hb : b.supp.ncard = q * m_b)
    {x y : V} (hxyD : (secondOrderDefectGraph G).Adj x y) :
    (q * q - 2 * (q - 1)) - 2 * m_a * m_b ≤ m_a * m_a + m_b * m_b := by
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  let AA := coloredTwoStepMiddles A A x y
  let BB := coloredTwoStepMiddles B B x y
  have hlo : (q * q - 2 * (q - 1)) - 2 * m_a * m_b ≤
      (AA ∪ BB).card := by
    exact binarySquare_regular_twoComponents_defectEdge_sameOwner_card_lower
      G hfree hq hreg hcard hcount a b hab ha hb hxyD
  have hAA : AA.card ≤ m_a * m_a := by
    exact binarySquare_regular_sameOwner_defectEdge_card_le_sq
      G hfree hq hreg hcard a ha hxyD
  have hBB : BB.card ≤ m_b * m_b := by
    exact binarySquare_regular_sameOwner_defectEdge_card_le_sq
      G hfree hq hreg hcard b hb hxyD
  have hdis : Disjoint AA BB := by
    exact coloredTwoStepMiddles_disjoint_of_orderedOwners_ne
      G hfree a a b b (by simpa using hab) x y
  rw [Finset.card_union_of_disjoint hdis] at hlo
  omega

end

end Erdos85

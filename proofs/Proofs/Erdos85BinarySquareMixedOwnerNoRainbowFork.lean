import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowMiddleCollision

/-! # A forced mixed-owner fork in the no-rainbow branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- The repeated-middle collision can be unpacked as two distinct closing
vertices, each completing the same owner-`a` edge to an `a-b-c` triangle.
All three vertices of either triangle lie in distinct defect components. -/
theorem orderSixtyFour_regular_fourComponents_noRainbow_exists_ownerFork
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      routingOwnerRainbow G d a b c)
    (x : Fin 64) :
    ∃ (e : (secondOrderDefectGraph G).ConnectedComponent)
      (y z₁ z₂ : Fin 64),
      e ≠ (secondOrderDefectGraph G).connectedComponentMk x ∧
      (secondOrderDefectGraph G).connectedComponentMk y = e ∧ z₁ ≠ z₂ ∧
      (secondOrderDefectGraph G).connectedComponentMk z₁ ≠ e ∧
      (secondOrderDefectGraph G).connectedComponentMk z₁ ≠
        (secondOrderDefectGraph G).connectedComponentMk x ∧
      (secondOrderDefectGraph G).connectedComponentMk z₂ ≠ e ∧
      (secondOrderDefectGraph G).connectedComponentMk z₂ ≠
        (secondOrderDefectGraph G).connectedComponentMk x ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x y ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y z₁ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁ x ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y z₂ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂ x := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨e, y, hene, hycomp, haxy, hcard⟩ :=
    orderSixtyFour_regular_fourComponents_noRainbow_exists_repeatedMiddle
      G hfree hreg hcount a b c hab hac hbc hno x
  let S := ((rootedAllDistinctRoutingCyclePairs G hfree a b c x).filter
    fun p => D.connectedComponentMk p.2 = e).filter fun p => p.2 = y
  have hone : 1 < S.card := by
    have : 2 ≤ S.card := by simpa [S, D] using hcard
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hone
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  have hpmid := Finset.mem_filter.mp hp'.1
  have hqmid := Finset.mem_filter.mp hq'.1
  have hpbase := hpmid.1
  have hqbase := hqmid.1
  obtain ⟨hxy₁, hyz₁, hzx₁, _ha₁, hb₁, hc₁⟩ :=
    (Finset.mem_filter.mp hpbase).2
  obtain ⟨hxy₂, hyz₂, hzx₂, _ha₂, hb₂, hc₂⟩ :=
    (Finset.mem_filter.mp hqbase).2
  have hpzcomp : D.connectedComponentMk p.1 ≠ e := by
    exact fun h => hyz₁ (hpmid.2.trans h.symm)
  have hqzcomp : D.connectedComponentMk q.1 ≠ e := by
    exact fun h => hyz₂ (hqmid.2.trans h.symm)
  have hpqz : p.1 ≠ q.1 := by
    intro hz
    apply hpq
    apply Prod.ext hz
    exact hp'.2.trans hq'.2.symm
  have hbyz₁ : (componentOwnerGraph G D b).Adj y p.1 := by
    have h := componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
      G hfree hyz₁
        ⟨p.2, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩ b hb₁
    rw [hp'.2] at h
    exact h
  have hczx₁ : (componentOwnerGraph G D c).Adj p.1 x :=
    componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
      G hfree hzx₁
        ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨x, ConnectedComponent.connectedComponentMk_mem⟩ c hc₁
  have hbyz₂ : (componentOwnerGraph G D b).Adj y q.1 := by
    have h := componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
      G hfree hyz₂
        ⟨q.2, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨q.1, ConnectedComponent.connectedComponentMk_mem⟩ b hb₂
    rw [hq'.2] at h
    exact h
  have hczx₂ : (componentOwnerGraph G D c).Adj q.1 x :=
    componentOwnerGraph_adj_of_crossIntermediateComponent_eq_owner
      G hfree hzx₂
        ⟨q.1, ConnectedComponent.connectedComponentMk_mem⟩
        ⟨x, ConnectedComponent.connectedComponentMk_mem⟩ c hc₂
  refine ⟨e, y, p.1, q.1, hene, hycomp, hpqz, hpzcomp, hzx₁,
    hqzcomp, hzx₂, haxy, hbyz₁, hczx₁, hbyz₂, hczx₂⟩

end

end Erdos85

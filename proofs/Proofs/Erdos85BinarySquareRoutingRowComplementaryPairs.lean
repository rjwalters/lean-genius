import Proofs.Erdos85BinarySquareRoutingRowResidualCenters

/-! # Complementary center pairs in a size-four routing row -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A routing row split into two complementary pairs of owner centers. -/
def HasComplementaryTwoCenterRoutingPairsForOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ (source target : (secondOrderDefectGraph G).ConnectedComponent)
      (hst : source ≠ target) (x : source.supp)
      (u₁ u₂ v₁ v₂ : owner.supp),
    u₁ ≠ u₂ ∧ v₁ ≠ v₂ ∧
      G.Adj x.1 u₁.1 ∧ G.Adj x.1 u₂.1 ∧
      G.Adj x.1 v₁.1 ∧ G.Adj x.1 v₂.1 ∧
      let S₁ := componentCrossNeighborFinset G target u₁
      let S₂ := componentCrossNeighborFinset G target u₂
      let T₁ := componentCrossNeighborFinset G target v₁
      let T₂ := componentCrossNeighborFinset G target v₂
      let R := (Finset.univ : Finset target.supp).filter fun y =>
        owner = crossIntermediateComponent G hfree hst x y
      Disjoint (S₁ ∪ S₂) (T₁ ∪ T₂) ∧
        (S₁ ∪ S₂).card = 2 * m target ∧
        (T₁ ∪ T₂).card = 2 * m target ∧
        (S₁ ∪ S₂) ∪ (T₁ ∪ T₂) = R

/-- **Size-four complementary-pair theorem, q-generic.**  Once one separated
center pair is known in an owner row with `m owner = 4`, the two remaining
centers form a second separated pair whose stars are exactly complementary
to the first pair's stars. -/
theorem twoCenterRoutingRowDensityForOwner_has_complementaryPair_of_m_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (hmo : m owner = 4)
    (h : HasTwoCenterRoutingRowDensityForOwner G hfree m owner) :
    HasComplementaryTwoCenterRoutingPairsForOwner G hfree m owner := by
  classical
  rcases h with ⟨source, target, hst, x, u₁, u₂, hne, hx₁, hx₂,
    hdis, hunionCard, hsub, _hrowCard⟩
  let C := componentCrossNeighborFinset G owner x
  let S₁ := componentCrossNeighborFinset G target u₁
  let S₂ := componentCrossNeighborFinset G target u₂
  let R := (Finset.univ : Finset target.supp).filter fun y =>
    owner = crossIntermediateComponent G hfree hst x y
  have hu₁C : u₁ ∈ C := by
    change u₁ ∈ componentCrossNeighborFinset G owner x
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx₁⟩
  have hu₂C : u₂ ∈ C := by
    change u₂ ∈ componentCrossNeighborFinset G owner x
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx₂⟩
  have hpairSub : ({u₁, u₂} : Finset owner.supp) ⊆ C := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hu₁C
    · exact hu₂C
  have hCcard : C.card = 4 := by
    change (componentCrossNeighborFinset G owner x).card = 4
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard source owner (x := x.1) x.2
    rw [hm owner, hmo] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have hresCardTwo : (C \ {u₁, u₂}).card = 2 := by
    rw [Finset.card_sdiff_of_subset hpairSub, hCcard]
    simp [hne]
  obtain ⟨v₁, v₂, hvne, hvpair⟩ := Finset.card_eq_two.mp hresCardTwo
  have hv₁res : v₁ ∈ C \ {u₁, u₂} := by simp [hvpair]
  have hv₂res : v₂ ∈ C \ {u₁, u₂} := by simp [hvpair]
  have hv₁C : v₁ ∈ C := (Finset.mem_sdiff.mp hv₁res).1
  have hv₂C : v₂ ∈ C := (Finset.mem_sdiff.mp hv₂res).1
  have hxv₁ : G.Adj x.1 v₁.1 := by
    exact (Finset.mem_filter.mp hv₁C).2
  have hxv₂ : G.Adj x.1 v₂.1 := by
    exact (Finset.mem_filter.mp hv₂C).2
  have hdenseV := binarySquare_regular_twoSeparatedCenters_routingRow_density
    G hfree hq hreg hcard m hm hst x v₁ v₂ hvne hxv₁ hxv₂
  let T₁ := componentCrossNeighborFinset G target v₁
  let T₂ := componentCrossNeighborFinset G target v₂
  have hdecomp : R = C.biUnion fun u =>
      componentCrossNeighborFinset G target u := by
    exact routingRow_eq_biUnion_componentCrossNeighborFinset
      G hfree hst owner x
  have hresidual :
      R \ (S₁ ∪ S₂) =
        (C \ {u₁, u₂}).biUnion fun u =>
          componentCrossNeighborFinset G target u := by
    ext y
    constructor
    · intro hy
      have hyR := (Finset.mem_sdiff.mp hy).1
      have hynot := (Finset.mem_sdiff.mp hy).2
      rw [hdecomp] at hyR
      obtain ⟨u, huC, huy⟩ := Finset.mem_biUnion.mp hyR
      have hupair : u ∉ ({u₁, u₂} : Finset owner.supp) := by
        intro hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hynot (Finset.mem_union_left _ huy)
        · exact hynot (Finset.mem_union_right _ huy)
      exact Finset.mem_biUnion.mpr
        ⟨u, Finset.mem_sdiff.mpr ⟨huC, hupair⟩, huy⟩
    · intro hy
      obtain ⟨u, husdiff, huy⟩ := Finset.mem_biUnion.mp hy
      have huC := (Finset.mem_sdiff.mp husdiff).1
      have hupair := (Finset.mem_sdiff.mp husdiff).2
      have hune₁ : u ≠ u₁ := by
        intro hu
        apply hupair
        simp [hu]
      have hune₂ : u ≠ u₂ := by
        intro hu
        apply hupair
        simp [hu]
      apply Finset.mem_sdiff.mpr
      constructor
      · rw [hdecomp]
        exact Finset.mem_biUnion.mpr ⟨u, huC, huy⟩
      · intro hyunion
        rcases Finset.mem_union.mp hyunion with hy₁ | hy₂
        · have hd := routingRow_starRows_pairwise_disjoint
            G hfree hst x huC hu₁C hune₁
          exact Finset.disjoint_left.mp hd huy hy₁
        · have hd := routingRow_starRows_pairwise_disjoint
            G hfree hst x huC hu₂C hune₂
          exact Finset.disjoint_left.mp hd huy hy₂
  have hresidual' : R \ (S₁ ∪ S₂) = T₁ ∪ T₂ := by
    simpa [C, S₁, S₂, T₁, T₂, R, hvpair] using hresidual
  have hcomplementDis : Disjoint (S₁ ∪ S₂) (T₁ ∪ T₂) := by
    rw [← hresidual']
    exact Finset.disjoint_sdiff
  have hcover : (S₁ ∪ S₂) ∪ (T₁ ∪ T₂) = R := by
    rw [← hresidual']
    exact Finset.union_sdiff_of_subset hsub
  exact ⟨source, target, hst, x, u₁, u₂, v₁, v₂,
    hne, hvne, hx₁, hx₂, hxv₁, hxv₂,
    hcomplementDis, hunionCard, hdenseV.2.1, hcover⟩

/-- The order-64 `[4,4]` pressure theorem therefore supplies two
complementary dense center pairs in one routing row, not merely one fragment. -/
theorem orderSixtyFour_fourFour_twoOwner_exists_complementaryRoutingPairs
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 4) (hmb : m b = 4)
    (hcross : 12288 ≤
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)).card) :
    HasComplementaryTwoCenterRoutingPairsForOwner G hfree m a ∨
      HasComplementaryTwoCenterRoutingPairsForOwner G hfree m b := by
  rcases orderSixtyFour_fourFour_twoOwner_exists_ownerDensity
    G hfree hreg hcount m hm a b hab hma hmb hcross with ha | hb
  · exact Or.inl
      (twoCenterRoutingRowDensityForOwner_has_complementaryPair_of_m_eq_four
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a hma ha)
  · exact Or.inr
      (twoCenterRoutingRowDensityForOwner_has_complementaryPair_of_m_eq_four
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b hmb hb)

end

end Erdos85

#print axioms Erdos85.twoCenterRoutingRowDensityForOwner_has_complementaryPair_of_m_eq_four
#print axioms Erdos85.orderSixtyFour_fourFour_twoOwner_exists_complementaryRoutingPairs

import Proofs.Erdos85BinarySquareMixedOwnerRootedPatternBounds

/-! # Forcing rooted owner triangles through three defect components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Neighbors in one owner color which stay inside the vertex's defect
component. -/
def sameDefectComponentOwnerNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (x : V) : Finset V :=
  ((componentOwnerGraph G (secondOrderDefectGraph G) owner).neighborFinset x).filter
    fun y => (secondOrderDefectGraph G).connectedComponentMk y =
      (secondOrderDefectGraph G).connectedComponentMk x

set_option maxRecDepth 10000 in
/-- In the order-64 four-component branch, every owner color has exactly two
neighbors inside the vertex's own defect component. -/
theorem orderSixtyFour_regular_fourComponents_sameDefectComponentOwnerNeighbors_card
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) (x : Fin 64) :
    (sameDefectComponentOwnerNeighbors G owner x).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  let xd : d.supp := ⟨x, (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let R := restrictedComponentOwnerGraph G d owner
  let S := sameDefectComponentOwnerNeighbors G owner x
  have hcardEq : (R.neighborFinset xd).card = S.card := by
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      have hyAdj := (R.mem_neighborFinset xd y).mp hy
      apply Finset.mem_filter.mpr
      refine ⟨((componentOwnerGraph G D owner).mem_neighborFinset x y.1).mpr hyAdj, ?_⟩
      exact (ConnectedComponent.mem_supp_iff d y.1).mp y.2
    · intro y hy z hz hyz
      exact Subtype.ext hyz
    · intro y hy
      have hy' := Finset.mem_filter.mp hy
      have hymem : y ∈ d.supp :=
        (ConnectedComponent.mem_supp_iff d y).mpr hy'.2
      refine ⟨⟨y, hymem⟩, ?_, rfl⟩
      exact (R.mem_neighborFinset xd ⟨y, hymem⟩).mpr
        (((componentOwnerGraph G D owner).mem_neighborFinset x y).mp hy'.1)
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hdegree : R.degree xd = 2 :=
    binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d owner
        (by simpa using hall d) (by simpa using hall owner) xd
  rw [← hcardEq, SimpleGraph.card_neighborFinset_eq_degree, hdegree]

/-- Consequently exactly twelve neighbors in each owner color leave the
vertex's defect component. -/
theorem orderSixtyFour_regular_fourComponents_crossDefectComponentOwnerNeighbors_card
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) (x : Fin 64) :
    (((componentOwnerGraph G (secondOrderDefectGraph G) owner).neighborFinset x).filter
      fun y => (secondOrderDefectGraph G).connectedComponentMk y ≠
        (secondOrderDefectGraph G).connectedComponentMk x).card = 12 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (componentOwnerGraph G (secondOrderDefectGraph G) owner).neighborFinset x)
    (p := fun y => (secondOrderDefectGraph G).connectedComponentMk y =
      (secondOrderDefectGraph G).connectedComponentMk x)
  have hlocal :=
    orderSixtyFour_regular_fourComponents_sameDefectComponentOwnerNeighbors_card
      G hfree hreg hcount owner x
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hdegree :
      (componentOwnerGraph G (secondOrderDefectGraph G) owner).degree x = 14 := by
    simpa using binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) owner
        (m_c := 2) (by norm_num [hall owner]) x
  change (sameDefectComponentOwnerNeighbors G owner x).card +
    (((componentOwnerGraph G (secondOrderDefectGraph G) owner).neighborFinset x).filter
      fun y => (secondOrderDefectGraph G).connectedComponentMk y ≠
        (secondOrderDefectGraph G).connectedComponentMk x).card =
      (componentOwnerGraph G (secondOrderDefectGraph G) owner).degree x at hsplit
  omega

set_option maxRecDepth 10000 in
/-- Pattern three, where both non-root vertices leave together into one
external component, has cardinality at most `12 * 2 = 24`. -/
theorem orderSixtyFour_regular_fourComponents_rootedPattern_three_card_le_twentyFour
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
    (x : Fin 64) :
    (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 3).card ≤ 24 := by
  classical
  let D := secondOrderDefectGraph G
  let OA := componentOwnerGraph G D a
  let OB := componentOwnerGraph G D b
  let OC := componentOwnerGraph G D c
  let Y := (OA.neighborFinset x).filter fun y =>
    D.connectedComponentMk y ≠ D.connectedComponentMk x
  let T := Y.sigma fun y => sameDefectComponentOwnerNeighbors G b y
  let S := rootedComponentPatternPairs D OA OB OC x 3
  have hmaps : ∀ p ∈ S, (⟨p.2, p.1⟩ : Σ _y : Fin 64, Fin 64) ∈ T := by
    intro p hp
    have hpattern := (rootedComponentPattern_eq_three_iff D x p).mp
      (Finset.mem_filter.mp hp).2
    have hcolor := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    simp only [T, Finset.mem_sigma]
    constructor
    · exact Finset.mem_filter.mpr ⟨(OA.mem_neighborFinset x p.2).mpr hcolor.1, hpattern.1⟩
    · exact Finset.mem_filter.mpr ⟨(OB.mem_neighborFinset p.2 p.1).mpr hcolor.2.1,
        hpattern.2.2.symm⟩
  have hle : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn
      (fun p : Fin 64 × Fin 64 => (⟨p.2, p.1⟩ : Σ _y : Fin 64, Fin 64))
    · exact fun p hp => hmaps p hp
    · intro p hp q hq hpq
      rcases p with ⟨z, y⟩
      rcases q with ⟨z', y'⟩
      simp only at hpq
      cases hpq
      rfl
  have hYcard : Y.card = 12 :=
    orderSixtyFour_regular_fourComponents_crossDefectComponentOwnerNeighbors_card
      G hfree hreg hcount a x
  calc
    _ = S.card := rfl
    _ ≤ T.card := hle
    _ = 24 := by
      rw [Finset.card_sigma]
      have htwo : ∀ y ∈ Y,
          (sameDefectComponentOwnerNeighbors G b y).card = 2 := by
        intro y _
        exact orderSixtyFour_regular_fourComponents_sameDefectComponentOwnerNeighbors_card
          G hfree hreg hcount b y
      rw [Finset.sum_congr rfl htwo]
      simp [hYcard]

/-- Therefore every root supports at least twelve prescribed-color triangles
whose three vertices lie in three pairwise-distinct defect components. -/
theorem orderSixtyFour_regular_fourComponents_rootedPattern_four_card_ge_twelve
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
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (x : Fin 64) :
    12 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 4).card := by
  let P := fun i : Fin 5 =>
    (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x i).card
  have hsum : (∑ i : Fin 5, P i) = 56 :=
    orderSixtyFour_regular_fourComponents_sum_rootedComponentPatterns_eq
      G hfree hreg hcount a b c hab hac hbc x
  rw [Fin.sum_univ_five] at hsum
  have hzero : P 0 ≤ 4 := by
    dsimp [P]
    rw [rootedComponentPatternPairs_zero_eq_sameComponent]
    exact orderSixtyFour_regular_fourComponents_rooted_sameComponent_mixedOwner_card_le
      G hfree hreg hcount a b c x
  have hone : P 1 ≤ 8 :=
    orderSixtyFour_regular_fourComponents_rootedPattern_one_card_le_eight
      G hfree hreg hcount a b c hab hac hbc x
  have htwo : P 2 ≤ 8 :=
    orderSixtyFour_regular_fourComponents_rootedPattern_two_card_le_eight
      G hfree hreg hcount a b c hab hac hbc x
  have hthree : P 3 ≤ 24 :=
    orderSixtyFour_regular_fourComponents_rootedPattern_three_card_le_twentyFour
      G hfree hreg hcount a b c x
  change 12 ≤ P 4
  omega

end

end Erdos85

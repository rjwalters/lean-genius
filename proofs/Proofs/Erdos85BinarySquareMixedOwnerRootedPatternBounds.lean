import Proofs.Erdos85BinarySquareMixedOwnerRootedComponentPatterns
import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Numerical bounds for rooted mixed-owner component patterns -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Middle vertices of a two-step walk `x-A-y-B-z`. -/
def coloredTwoStepMiddles
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (x z : V) : Finset V :=
  Finset.univ.filter fun y => A.Adj x y ∧ B.Adj y z

/-- A product entry of two adjacency matrices counts their colored
two-step middle vertices. -/
theorem mul_two_adjMatrices_apply_eq_card_coloredTwoStepMiddles
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B : SimpleGraph V) [DecidableRel A.Adj] [DecidableRel B.Adj]
    (x z : V) :
    (A.adjMatrix ℤ * B.adjMatrix ℤ) x z =
      (coloredTwoStepMiddles A B x z).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  push_cast
  simp only [coloredTwoStepMiddles, Finset.sum_filter, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hA : A.Adj x y <;> by_cases hB : B.Adj y z <;>
    simp [SimpleGraph.adjMatrix_apply, hA, hB]

/-- If `xz` has a third owner color, then exactly four `a-b` two-step
middles join it at order 64. -/
theorem orderSixtyFour_regular_fourComponents_coloredTwoStepMiddles_card_eq_four
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
    {x z : Fin 64}
    (hcz : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x z) :
    (coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) x z).card = 4 := by
  let A := (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ
  let B := (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix (Fin 64)
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hshift := binarySquare_regular_shiftedOwnerMatrices_cross_product
    G hfree (q := 8) (by norm_num) hreg (by norm_num) a b hab
      (m_c := 2) (m_d := 2) (by norm_num [hall a]) (by norm_num [hall b])
  have hprod : A * B = (4 : ℤ) • J - (2 : ℤ) • A - (2 : ℤ) • B -
      (4 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) := by
    calc
      A * B = (A + (2 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) *
          (B + (2 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) -
          (2 : ℤ) • A - (2 : ℤ) • B -
          (4 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) := by
            simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
              Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
            module
      _ = _ := by
        rw [show (A + (2 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) *
            (B + (2 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ)) =
            (4 : ℤ) • J by simpa [A, B, J] using hshift]
  have hnotA : ¬ (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x z := by
    rw [componentOwnerGraph_adj_iff_owner_eq_of_adj G hfree c hcz a]
    exact hac
  have hnotB : ¬ (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj x z := by
    rw [componentOwnerGraph_adj_iff_owner_eq_of_adj G hfree c hcz b]
    exact hbc
  have hxz : x ≠ z := hcz.ne
  have hAxz : A x z = 0 := by
    change (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ x z = 0
    simp only [SimpleGraph.adjMatrix_apply]
    rw [if_neg hnotA]
  have hBxz : B x z = 0 := by
    change (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ x z = 0
    simp only [SimpleGraph.adjMatrix_apply]
    rw [if_neg hnotB]
  have hentry : (A * B) x z = 4 := by
    rw [hprod]
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    simp [hAxz, hBxz, J, FriendshipTheoremOQ01.onesMatrix, hxz]
  have hcard := mul_two_adjMatrices_apply_eq_card_coloredTwoStepMiddles
    (componentOwnerGraph G (secondOrderDefectGraph G) a)
    (componentOwnerGraph G (secondOrderDefectGraph G) b) x z
  change (A * B) x z =
    ((coloredTwoStepMiddles
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) x z).card : ℤ) at hcard
  exact_mod_cast hcard.symm.trans hentry

set_option maxRecDepth 10000 in
/-- Pattern one (only the middle vertex leaves the root component) has at
most eight elements. -/
theorem orderSixtyFour_regular_fourComponents_rootedPattern_one_card_le_eight
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
    (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 1).card ≤ 8 := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  let xd : d.supp := ⟨x, (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let OA := componentOwnerGraph G D a
  let OB := componentOwnerGraph G D b
  let OC := componentOwnerGraph G D c
  let RC := restrictedComponentOwnerGraph G d c
  let S := rootedComponentPatternPairs D OA OB OC x 1
  let T := (RC.neighborFinset xd).sigma fun z =>
    coloredTwoStepMiddles OA OB x z.1
  let lift : (p : ↥S) → Σ z : d.supp, Fin 64 := fun p =>
    ⟨⟨p.1.1, (ConnectedComponent.mem_supp_iff d p.1.1).mpr
      ((rootedComponentPattern_eq_one_iff D x p.1).mp
        (Finset.mem_filter.mp p.2).2).2⟩, p.1.2⟩
  have hlift_mem : ∀ p : ↥S, lift p ∈ T := by
    intro p
    have hcolor := (Finset.mem_filter.mp
      (Finset.mem_filter.mp p.2).1).2
    simp only [T, Finset.mem_sigma, SimpleGraph.mem_neighborFinset]
    constructor
    · change OC.Adj x p.1.1
      exact hcolor.2.2.symm
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor.1, hcolor.2.1⟩
  let F : ↥S → ↥T := fun p => ⟨lift p, hlift_mem p⟩
  have hFinj : Function.Injective F := by
    intro p q hpq
    apply Subtype.ext
    rcases p with ⟨⟨z, y⟩, hp⟩
    rcases q with ⟨⟨z', y'⟩, hq⟩
    simp only [F, lift] at hpq
    cases hpq
    rfl
  have hle : S.card ≤ T.card := Finset.card_le_card_of_injective hFinj
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hRCdeg : RC.degree xd = 2 :=
    binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d c
        (by simpa using hall d) (by simpa using hall c) xd
  calc
    _ = S.card := rfl
    _ ≤ T.card := hle
    _ = 8 := by
      rw [Finset.card_sigma]
      have hfour : ∀ z ∈ RC.neighborFinset xd,
          (coloredTwoStepMiddles OA OB x z.1).card = 4 := by
        intro z hz
        have hcz : OC.Adj x z.1 := by
          exact ((RC.mem_neighborFinset xd z).mp hz)
        exact orderSixtyFour_regular_fourComponents_coloredTwoStepMiddles_card_eq_four
          G hfree hreg hcount a b c hab hac hbc hcz
      rw [Finset.sum_congr rfl hfour]
      simp [SimpleGraph.card_neighborFinset_eq_degree, hRCdeg]

set_option maxRecDepth 10000 in
/-- Pattern two (only the closing vertex leaves the root component) also has
at most eight elements. -/
theorem orderSixtyFour_regular_fourComponents_rootedPattern_two_card_le_eight
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
    (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 2).card ≤ 8 := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  let xd : d.supp := ⟨x, (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let OA := componentOwnerGraph G D a
  let OB := componentOwnerGraph G D b
  let OC := componentOwnerGraph G D c
  let RA := restrictedComponentOwnerGraph G d a
  let S := rootedComponentPatternPairs D OA OB OC x 2
  let T := (RA.neighborFinset xd).sigma fun y =>
    coloredTwoStepMiddles OB OC y.1 x
  let lift : (p : ↥S) → Σ y : d.supp, Fin 64 := fun p =>
    ⟨⟨p.1.2, (ConnectedComponent.mem_supp_iff d p.1.2).mpr
      ((rootedComponentPattern_eq_two_iff D x p.1).mp
        (Finset.mem_filter.mp p.2).2).1⟩, p.1.1⟩
  have hlift_mem : ∀ p : ↥S, lift p ∈ T := by
    intro p
    have hcolor := (Finset.mem_filter.mp
      (Finset.mem_filter.mp p.2).1).2
    simp only [T, Finset.mem_sigma, SimpleGraph.mem_neighborFinset]
    constructor
    · change OA.Adj x p.1.2
      exact hcolor.1
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcolor.2.1, hcolor.2.2⟩
  let F : ↥S → ↥T := fun p => ⟨lift p, hlift_mem p⟩
  have hFinj : Function.Injective F := by
    intro p q hpq
    apply Subtype.ext
    rcases p with ⟨⟨z, y⟩, hp⟩
    rcases q with ⟨⟨z', y'⟩, hq⟩
    simp only [F, lift] at hpq
    cases hpq
    rfl
  have hle : S.card ≤ T.card := Finset.card_le_card_of_injective hFinj
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hRAdeg : RA.degree xd = 2 :=
    binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d a
        (by simpa using hall d) (by simpa using hall a) xd
  calc
    _ = S.card := rfl
    _ ≤ T.card := hle
    _ = 8 := by
      rw [Finset.card_sigma]
      have hfour : ∀ y ∈ RA.neighborFinset xd,
          (coloredTwoStepMiddles OB OC y.1 x).card = 4 := by
        intro y hy
        have hay : (componentOwnerGraph G D a).Adj y.1 x := by
          exact ((RA.mem_neighborFinset xd y).mp hy).symm
        exact orderSixtyFour_regular_fourComponents_coloredTwoStepMiddles_card_eq_four
          G hfree hreg hcount b c a hbc hab.symm hac.symm hay
      rw [Finset.sum_congr rfl hfour]
      simp [SimpleGraph.card_neighborFinset_eq_degree, hRAdeg]

/-- After bounding the local and one-vertex-leaves patterns, either the two
leaving vertices share an external component at least eighteen times or all
three vertices occupy distinct components at least eighteen times. -/
theorem orderSixtyFour_regular_fourComponents_large_pattern_three_or_four
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
    18 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 3).card ∨
    18 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
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
  change 18 ≤ P 3 ∨ 18 ≤ P 4
  omega

end

end Erdos85

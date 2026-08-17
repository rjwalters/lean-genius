import Proofs.Erdos85BinarySquareMixedOwnerFiberBound
import Proofs.Erdos85MooreFriendship

/-! # Rooted mixed owner triangle census at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem ownerMatrix_mul_eq
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
    (hb : b.supp.ncard = q * m_b) :
    (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
      (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ =
      ((m_a : ℤ) * (m_b : ℤ)) • FriendshipTheoremOQ01.onesMatrix V -
        (m_b : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ -
        (m_a : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ -
        ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
  have hshift := binarySquare_regular_shiftedOwnerMatrices_cross_product
    G hfree hq hreg hcard a b hab ha hb
  calc
    _ = ((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ +
          (m_a : ℤ) • (1 : Matrix V V ℤ)) *
        ((componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ +
          (m_b : ℤ) • (1 : Matrix V V ℤ)) -
        (m_b : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ -
        (m_a : ℤ) •
          (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ -
        ((m_a : ℤ) * (m_b : ℤ)) • (1 : Matrix V V ℤ) := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_smul,
            Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
          module
    _ = _ := by rw [hshift]

/-- The ordered pairs `(z,y)` closing a cyclically colored triangle rooted at
`x`: the edges are `x-A-y-B-z-C-x`. -/
def rootedCyclicColoredPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (x : V) : Finset (V × V) :=
  Finset.univ.filter fun p =>
    A.Adj x p.2 ∧ B.Adj p.2 p.1 ∧ C.Adj p.1 x

/-- The rooted colored triangles whose other two vertices stay in the root's
connected component of `D`. -/
def rootedSameComponentCyclicColoredPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (x : V) : Finset (V × V) :=
  (rootedCyclicColoredPairs A B C x).filter fun p =>
    D.connectedComponentMk p.2 = D.connectedComponentMk x ∧
      D.connectedComponentMk p.1 = D.connectedComponentMk x

/-- The complementary rooted colored triangles, with at least one other
vertex outside the root's component. -/
def rootedCrossComponentCyclicColoredPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (x : V) : Finset (V × V) :=
  (rootedCyclicColoredPairs A B C x).filter fun p =>
    ¬ (D.connectedComponentMk p.2 = D.connectedComponentMk x ∧
      D.connectedComponentMk p.1 = D.connectedComponentMk x)

/-- A rooted mixed cubic matrix entry is exactly the corresponding rooted
colored-triangle cardinality. -/
theorem mul_three_adjMatrices_apply_eq_card_rootedCyclicColoredPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (x : V) :
    (A.adjMatrix ℤ * B.adjMatrix ℤ * C.adjMatrix ℤ) x x =
      (rootedCyclicColoredPairs A B C x).card := by
  classical
  rw [Finset.card_eq_sum_ones]
  push_cast
  simp only [rootedCyclicColoredPairs, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Matrix.mul_apply, SimpleGraph.adjMatrix_apply,
    -Finset.sum_const, -Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hC : C.Adj z x <;> simp [hC]
  rw [Finset.card_eq_sum_ones]
  push_cast
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hA : A.Adj x y <;> by_cases hB : B.Adj y z <;> simp [hA, hB]

/-- The global count `3584` is pointwise uniform: every starting vertex lies
on exactly `56` cyclic triangles with any fixed ordered triple of distinct
owner colors. -/
theorem orderSixtyFour_regular_fourComponents_mixedOwnerMatrix_cube_apply
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
    (((componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ *
      (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ) *
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ) x x =
      56 := by
  let A := (componentOwnerGraph G (secondOrderDefectGraph G) a).adjMatrix ℤ
  let B := (componentOwnerGraph G (secondOrderDefectGraph G) b).adjMatrix ℤ
  let C := (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix (Fin 64)
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hAB : A * B = (4 : ℤ) • J - (2 : ℤ) • A - (2 : ℤ) • B -
      (4 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) := by
    simpa [A, B, J] using ownerMatrix_mul_eq G hfree (q := 8)
      (by norm_num) hreg (by norm_num) a b hab
        (m_a := 2) (m_b := 2) (by norm_num [hall a]) (by norm_num [hall b])
  have hAC : (A * C) x x = 0 := by
    rw [show A * C = (4 : ℤ) • J - (2 : ℤ) • A - (2 : ℤ) • C -
      (4 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) by
        simpa [A, C, J] using ownerMatrix_mul_eq G hfree (q := 8)
          (by norm_num) hreg (by norm_num) a c hac
            (m_a := 2) (m_b := 2) (by norm_num [hall a]) (by norm_num [hall c])]
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    simp [A, C, J, SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix]
  have hBC : (B * C) x x = 0 := by
    rw [show B * C = (4 : ℤ) • J - (2 : ℤ) • B - (2 : ℤ) • C -
      (4 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) by
        simpa [B, C, J] using ownerMatrix_mul_eq G hfree (q := 8)
          (by norm_num) hreg (by norm_num) b c hbc
            (m_a := 2) (m_b := 2) (by norm_num [hall b]) (by norm_num [hall c])]
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    simp [B, C, J, SimpleGraph.adjMatrix_apply,
      FriendshipTheoremOQ01.onesMatrix]
  have hCreg : ∀ y,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).degree y = 14 := by
    intro y
    simpa using binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) c
        (m_c := 2) (by norm_num [hall c]) y
  have hJC : J * C = (14 : ℤ) • J := by
    simpa [C, J] using onesMatrix_mul_adjMatrix_of_regular
      (componentOwnerGraph G (secondOrderDefectGraph G) c) 14 hCreg
  change (A * B * C) x x = 56
  rw [hAB, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul,
    Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.one_mul, hJC]
  simp only [Matrix.sub_apply, Matrix.smul_apply]
  simp [hAC, hBC, C, J, SimpleGraph.adjMatrix_apply,
    FriendshipTheoremOQ01.onesMatrix]

/-- Combinatorial rooted form: every vertex starts exactly `56` triangles
with the prescribed three distinct owner colors. -/
theorem orderSixtyFour_regular_fourComponents_rooted_mixedOwner_card_eq
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
    (rootedCyclicColoredPairs
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x).card = 56 := by
  have hmatrix :=
    orderSixtyFour_regular_fourComponents_mixedOwnerMatrix_cube_apply
      G hfree hreg hcount a b c hab hac hbc x
  rw [mul_three_adjMatrices_apply_eq_card_rootedCyclicColoredPairs] at hmatrix
  exact_mod_cast hmatrix

set_option maxRecDepth 10000 in
/-- At most four of the `56` rooted mixed-owner triangles can stay wholly
inside the root's defect component. -/
theorem orderSixtyFour_regular_fourComponents_rooted_sameComponent_mixedOwner_card_le
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) (x : Fin 64) :
    (rootedSameComponentCyclicColoredPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x).card ≤ 4 := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  let xd : d.supp := ⟨x, (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let A := restrictedComponentOwnerGraph G d a
  let B := restrictedComponentOwnerGraph G d b
  let T := (A.neighborFinset xd).sigma fun y => B.neighborFinset y
  let S := rootedSameComponentCyclicColoredPairs D
      (componentOwnerGraph G D a) (componentOwnerGraph G D b)
      (componentOwnerGraph G D c) x
  let lift : (p : ↥S) → Σ y : d.supp, d.supp := fun p =>
    ⟨⟨p.1.2, (ConnectedComponent.mem_supp_iff d p.1.2).mpr
        ((Finset.mem_filter.mp p.2).2.1)⟩,
      ⟨p.1.1, (ConnectedComponent.mem_supp_iff d p.1.1).mpr
        ((Finset.mem_filter.mp p.2).2.2)⟩⟩
  have hlift_mem : ∀ p : ↥S, lift p ∈ T := by
    intro p
    have hcolor := (Finset.mem_filter.mp (Finset.mem_filter.mp p.2).1).2
    simp only [T, Finset.mem_sigma, SimpleGraph.mem_neighborFinset]
    change A.Adj xd (lift p).1 ∧ B.Adj (lift p).1 (lift p).2
    constructor
    · change (componentOwnerGraph G D a).Adj x p.1.2
      exact hcolor.1
    · change (componentOwnerGraph G D b).Adj p.1.2 p.1.1
      exact hcolor.2.1
  let F : ↥S → ↥T := fun p => ⟨lift p, hlift_mem p⟩
  have hFinj : Function.Injective F := by
    intro p q hpq
    apply Subtype.ext
    rcases p with ⟨⟨z, y⟩, hp⟩
    rcases q with ⟨⟨z', y'⟩, hq⟩
    simp only [F, lift] at hpq
    cases hpq
    rfl
  have hle : S.card ≤ T.card :=
    Finset.card_le_card_of_injective hFinj
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hAdeg : A.degree xd = 2 := by
    exact binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d a
        (by simpa using hall d) (by simpa using hall a) xd
  have hBdeg : ∀ y : d.supp, B.degree y = 2 := by
    intro y
    exact binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
      G hfree (q := 8) (by norm_num) hreg (by norm_num) d b
        (by simpa using hall d) (by simpa using hall b) y
  calc
    _ = S.card := rfl
    _ ≤ T.card := hle
    _ = 4 := by
      simp [T, Finset.card_sigma, SimpleGraph.card_neighborFinset_eq_degree,
        hAdeg, hBdeg]

/-- Consequently at least `52` of the `56` rooted colored triangles leave
the root's defect component. -/
theorem orderSixtyFour_regular_fourComponents_rooted_crossComponent_mixedOwner_card_ge
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
    52 ≤ (rootedCrossComponentCyclicColoredPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x).card := by
  have htotal := orderSixtyFour_regular_fourComponents_rooted_mixedOwner_card_eq
    G hfree hreg hcount a b c hab hac hbc x
  have hlocal :=
    orderSixtyFour_regular_fourComponents_rooted_sameComponent_mixedOwner_card_le
      G hfree hreg hcount a b c x
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := rootedCyclicColoredPairs
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x)
    (p := fun p =>
      (secondOrderDefectGraph G).connectedComponentMk p.2 =
          (secondOrderDefectGraph G).connectedComponentMk x ∧
        (secondOrderDefectGraph G).connectedComponentMk p.1 =
          (secondOrderDefectGraph G).connectedComponentMk x)
  change (rootedSameComponentCyclicColoredPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x).card +
    (rootedCrossComponentCyclicColoredPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x).card =
    (rootedCyclicColoredPairs
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x).card at hsplit
  omega

end

end Erdos85

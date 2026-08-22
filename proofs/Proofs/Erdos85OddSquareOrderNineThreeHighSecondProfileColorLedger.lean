import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileCore
import Proofs.Erdos85ThreePartTwoRegularEdgeLedger

/-! # The balanced color ledger of the q = 9 three-high second-profile core

Node: B.3 / GAP B-CLASSIFY.  The 27 bin-one vertices form a two-regular
defect core.  Coloring each vertex by its unique high neighbor partitions
that core into three independent nine-point classes.  Consequently every
pair of colors supports exactly nine core edges.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the second h=3 profile, the bin-one defect core has three balanced
high-root colors and exactly nine defect edges between each pair of colors. -/
theorem squareOrderNine_threeHigh_secondProfile_binOne_color_edge_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (hH : squareOrderHighVertices G 9 = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let K := D.induce (↑(B 1) : Set V)
    let A := (Finset.univ : Finset ↥(↑(B 1) : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset a
    let Q := (Finset.univ : Finset ↥(↑(B 1) : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset b
    let C := (Finset.univ : Finset ↥(↑(B 1) : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset c
    (∑ x ∈ A, (K.neighborFinset x ∩ Q).card) = 9 ∧
      (∑ x ∈ Q, (K.neighborFinset x ∩ C).card) = 9 ∧
      (∑ x ∈ C, (K.neighborFinset x ∩ A).card) = 9 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let K := D.induce (↑(B 1) : Set V)
  let A := (Finset.univ : Finset ↥(↑(B 1) : Set V)).filter fun y =>
    y.1 ∈ G.neighborFinset a
  let Q := (Finset.univ : Finset ↥(↑(B 1) : Set V)).filter fun y =>
    y.1 ∈ G.neighborFinset b
  let C := (Finset.univ : Finset ↥(↑(B 1) : Set V)).filter fun y =>
    y.1 ∈ G.neighborFinset c
  have haH : a ∈ squareOrderHighVertices G 9 := by rw [hH]; simp
  have hbH : b ∈ squareOrderHighVertices G 9 := by rw [hH]; simp
  have hcH : c ∈ squareOrderHighVertices G 9 := by rw [hH]; simp
  have colorCard (r : V) :
      ((Finset.univ : Finset ↥(↑(B 1) : Set V)).filter fun y =>
        y.1 ∈ G.neighborFinset r).card =
        (G.neighborFinset r ∩ B 1).card := by
    rw [← Fintype.card_subtype]
    let e : {y : ↥(↑(B 1) : Set V) // y.1 ∈ G.neighborFinset r} ≃
        ↥(↑(G.neighborFinset r ∩ B 1) : Set V) :=
      { toFun := fun y =>
          ⟨y.1.1, Finset.mem_inter.mpr ⟨y.2, y.1.2⟩⟩
        invFun := fun y =>
          ⟨⟨y.1, (Finset.mem_inter.mp y.2).2⟩,
            (Finset.mem_inter.mp y.2).1⟩
        left_inv := by intro y; rfl
        right_inv := by intro y; rfl }
    exact (Fintype.card_congr e).trans
      (Fintype.card_coe (G.neighborFinset r ∩ B 1))
  have hAcard : A.card = 9 := by
    rw [colorCard]
    exact (squareOrderNine_threeHigh_secondProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc2 hc4 haH).1
  have hQcard : Q.card = 9 := by
    rw [colorCard]
    exact (squareOrderNine_threeHigh_secondProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc2 hc4 hbH).1
  have hCcard : C.card = 9 := by
    rw [colorCard]
    exact (squareOrderNine_threeHigh_secondProfile_highRoot_neighbor_split
      G hfree hmin hcard hp hhigh hc2 hc4 hcH).1
  have hAQ : Disjoint A Q := by
    rw [Finset.disjoint_left]
    intro y hya hyq
    have haya := (Finset.mem_filter.mp hya).2
    have hayb := (Finset.mem_filter.mp hyq).2
    have hyB : y.1 ∈ B 1 := y.2
    have hcardOne := (Finset.mem_filter.mp hyB).2
    have haInc : a ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 a).mpr
        ((G.adj_comm a y.1).mp ((G.mem_neighborFinset a y.1).mp haya)), haH⟩
    have hbInc : b ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 b).mpr
        ((G.adj_comm b y.1).mp ((G.mem_neighborFinset b y.1).mp hayb)), hbH⟩
    exact hab (Finset.card_le_one.mp (Nat.le_of_eq hcardOne) a haInc b hbInc)
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro y hya hyc
    have haya := (Finset.mem_filter.mp hya).2
    have hayc := (Finset.mem_filter.mp hyc).2
    have hyB : y.1 ∈ B 1 := y.2
    have hcardOne := (Finset.mem_filter.mp hyB).2
    have haInc : a ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 a).mpr
        ((G.adj_comm a y.1).mp ((G.mem_neighborFinset a y.1).mp haya)), haH⟩
    have hcInc : c ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 c).mpr
        ((G.adj_comm c y.1).mp ((G.mem_neighborFinset c y.1).mp hayc)), hcH⟩
    exact hac (Finset.card_le_one.mp (Nat.le_of_eq hcardOne) a haInc c hcInc)
  have hQC : Disjoint Q C := by
    rw [Finset.disjoint_left]
    intro y hyq hyc
    have hayb := (Finset.mem_filter.mp hyq).2
    have hayc := (Finset.mem_filter.mp hyc).2
    have hyB : y.1 ∈ B 1 := y.2
    have hcardOne := (Finset.mem_filter.mp hyB).2
    have hbInc : b ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 b).mpr
        ((G.adj_comm b y.1).mp ((G.mem_neighborFinset b y.1).mp hayb)), hbH⟩
    have hcInc : c ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 c).mpr
        ((G.adj_comm c y.1).mp ((G.mem_neighborFinset c y.1).mp hayc)), hcH⟩
    exact hbc (Finset.card_le_one.mp (Nat.le_of_eq hcardOne) b hbInc c hcInc)
  have hpart : A ∪ Q ∪ C = Finset.univ := by
    ext y
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hyB : y.1 ∈ B 1 := y.2
    have hincCard :
        (G.neighborFinset y.1 ∩ squareOrderHighVertices G 9).card = 1 :=
      (Finset.mem_filter.mp hyB).2
    obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega :
      0 < (G.neighborFinset y.1 ∩ squareOrderHighVertices G 9).card)
    have hr' := Finset.mem_inter.mp hr
    rw [hH] at hr'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr'
    rcases hr'.2 with hra | hrb | hrc
    · exact Or.inl (Or.inl (Finset.mem_filter.mpr ⟨by simp,
        (G.mem_neighborFinset a y.1).mpr
          ((G.adj_comm y.1 a).mp ((G.mem_neighborFinset y.1 a).mp
            (hra ▸ hr'.1)))⟩))
    · exact Or.inl (Or.inr (Finset.mem_filter.mpr ⟨by simp,
        (G.mem_neighborFinset b y.1).mpr
          ((G.adj_comm y.1 b).mp ((G.mem_neighborFinset y.1 b).mp
            (hrb ▸ hr'.1)))⟩))
    · exact Or.inr (Finset.mem_filter.mpr ⟨by simp,
        (G.mem_neighborFinset c y.1).mpr
          ((G.adj_comm y.1 c).mp ((G.mem_neighborFinset y.1 c).mp
            (hrc ▸ hr'.1)))⟩)
  have hKdeg : ∀ y : ↥(↑(B 1) : Set V), K.degree y = 2 := by
    simpa [K, B, D] using
      (squareOrderNine_threeHigh_secondProfile_binOne_defect_twoRegular
        G hfree hmin hcover hcard hp hhigh hc2 hc4)
  have independentColor (r : V) (hrH : r ∈ squareOrderHighVertices G 9)
      (R : Finset ↥(↑(B 1) : Set V))
      (hR : R = Finset.univ.filter fun y =>
        y.1 ∈ G.neighborFinset r) :
      ∀ x ∈ R, (K.neighborFinset x ∩ R).card = 0 := by
    intro x hx
    rw [Finset.card_eq_zero]
    ext z
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hxz hzR
    have hxr : x.1 ∈ G.neighborFinset r := by
      rw [hR] at hx
      exact (Finset.mem_filter.mp hx).2
    have hzr : z.1 ∈ G.neighborFinset r := by
      rw [hR] at hzR
      exact (Finset.mem_filter.mp hzR).2
    have hKadj : K.Adj x z := (K.mem_neighborFinset x z).mp hxz
    have hDadj : D.Adj x.1 z.1 := hKadj
    have hnot := not_secondOrderDefect_adj_of_commonNeighbor
      G hfree (D.ne_of_adj hDadj)
      ((G.adj_comm r x.1).mp ((G.mem_neighborFinset r x.1).mp hxr))
      ((G.adj_comm r z.1).mp ((G.mem_neighborFinset r z.1).mp hzr))
    exact hnot hDadj
  have hAind := independentColor a haH A rfl
  have hQind := independentColor b hbH Q rfl
  have hCind := independentColor c hcH C rfl
  exact threePart_twoRegular_crossEdge_ledger K A Q C 9 hpart hAQ hAC hQC
    hAcard hQcard hCcard hKdeg hAind hQind hCind

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_binOne_color_edge_ledger

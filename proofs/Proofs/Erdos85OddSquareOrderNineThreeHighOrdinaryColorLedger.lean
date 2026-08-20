import Proofs.Erdos85OddSquareOrderNineThreeHighBinOneDefectTypes
import Proofs.Erdos85ThreePartTwoRegularEdgeLedger

/-! # The balanced color ledger of the q = 9 three-high ordinary core -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- After enumerating the three high roots, their ordinary bin-one classes
partition the 21-vertex two-regular defect core into independent sets of size
seven.  Exactly seven defect edges join each pair of colors. -/
theorem squareOrderNine_threeHigh_firstProfile_ordinary_color_structure
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (hH : squareOrderHighVertices G 9 = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let O := (B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 0
    let K := D.induce (↑O : Set V)
    let A := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset a
    let Q := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset b
    let C := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset c
    ((∑ x ∈ A, (K.neighborFinset x ∩ Q).card) = 7 ∧
      (∑ x ∈ Q, (K.neighborFinset x ∩ C).card) = 7 ∧
      (∑ x ∈ C, (K.neighborFinset x ∩ A).card) = 7) ∧
    (∃ x ∈ A, (K.neighborFinset x ∩ Q).card = 1 ∧
      (K.neighborFinset x ∩ C).card = 1) ∧
    (∃ x ∈ Q, (K.neighborFinset x ∩ C).card = 1 ∧
      (K.neighborFinset x ∩ A).card = 1) ∧
    (∃ x ∈ C, (K.neighborFinset x ∩ A).card = 1 ∧
      (K.neighborFinset x ∩ Q).card = 1) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let O := (B 1).filter fun y =>
    ((secondOrderDefectGraph G).neighborFinset y ∩ B 2).card = 0
  let K := D.induce (↑O : Set V)
  let A := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
    y.1 ∈ G.neighborFinset a
  let Q := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
    y.1 ∈ G.neighborFinset b
  let C := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
    y.1 ∈ G.neighborFinset c
  have haH : a ∈ squareOrderHighVertices G 9 := by rw [hH]; simp
  have hbH : b ∈ squareOrderHighVertices G 9 := by rw [hH]; simp
  have hcH : c ∈ squareOrderHighVertices G 9 := by rw [hH]; simp
  have colorCard (r : V) :
      ((Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
        y.1 ∈ G.neighborFinset r).card = (G.neighborFinset r ∩ O).card := by
    rw [← Fintype.card_subtype]
    let e : {y : ↥(↑O : Set V) // y.1 ∈ G.neighborFinset r} ≃
        ↥(↑(G.neighborFinset r ∩ O) : Set V) :=
      { toFun := fun y => ⟨y.1.1, Finset.mem_inter.mpr ⟨y.2, y.1.2⟩⟩
        invFun := fun y => ⟨⟨y.1, (Finset.mem_inter.mp y.2).2⟩,
          (Finset.mem_inter.mp y.2).1⟩
        left_inv := by intro y; rfl
        right_inv := by intro y; rfl }
    exact (Fintype.card_congr e).trans
      (Fintype.card_coe (G.neighborFinset r ∩ O))
  have hAcard : A.card = 7 := by
    have h := squareOrderNine_threeHigh_firstProfile_ordinary_binOne_at_high_card
      G hfree hmin hcover hcard hp hhigh hc3 hc4 haH
    change (G.neighborFinset a ∩ O).card = 7 at h
    exact (colorCard a).trans h
  have hQcard : Q.card = 7 := by
    have h := squareOrderNine_threeHigh_firstProfile_ordinary_binOne_at_high_card
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hbH
    change (G.neighborFinset b ∩ O).card = 7 at h
    exact (colorCard b).trans h
  have hCcard : C.card = 7 := by
    have h := squareOrderNine_threeHigh_firstProfile_ordinary_binOne_at_high_card
      G hfree hmin hcover hcard hp hhigh hc3 hc4 hcH
    change (G.neighborFinset c ∩ O).card = 7 at h
    exact (colorCard c).trans h
  have hAQ : Disjoint A Q := by
    dsimp [A, Q]
    -- Directly use singleton high incidence rather than the generic helper's
    -- intentionally narrow root-membership side condition.
    rw [Finset.disjoint_left]
    intro y hya hyq
    have haya := (Finset.mem_filter.mp hya).2
    have hayb := (Finset.mem_filter.mp hyq).2
    have hyO : y.1 ∈ O := y.2
    have hyB : y.1 ∈ B 1 := (Finset.mem_filter.mp hyO).1
    have hcardOne := (Finset.mem_filter.mp hyB).2
    have haInc : a ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 a).mpr
        ((G.adj_comm a y.1).mp ((G.mem_neighborFinset a y.1).mp haya)), haH⟩
    have hbInc : b ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 b).mpr
        ((G.adj_comm b y.1).mp ((G.mem_neighborFinset b y.1).mp hayb)), hbH⟩
    exact hab (Finset.card_le_one.mp (Nat.le_of_eq hcardOne) a haInc b hbInc)
  have hAC : Disjoint A C := by
    dsimp [A, C]
    rw [Finset.disjoint_left]
    intro y hya hyc
    have haya := (Finset.mem_filter.mp hya).2
    have hayc := (Finset.mem_filter.mp hyc).2
    have hyO : y.1 ∈ O := y.2
    have hyB : y.1 ∈ B 1 := (Finset.mem_filter.mp hyO).1
    have hcardOne := (Finset.mem_filter.mp hyB).2
    have haInc : a ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 a).mpr
        ((G.adj_comm a y.1).mp ((G.mem_neighborFinset a y.1).mp haya)), haH⟩
    have hcInc : c ∈ G.neighborFinset y.1 ∩ squareOrderHighVertices G 9 :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset y.1 c).mpr
        ((G.adj_comm c y.1).mp ((G.mem_neighborFinset c y.1).mp hayc)), hcH⟩
    exact hac (Finset.card_le_one.mp (Nat.le_of_eq hcardOne) a haInc c hcInc)
  have hQC : Disjoint Q C := by
    dsimp [Q, C]
    rw [Finset.disjoint_left]
    intro y hyq hyc
    have hayb := (Finset.mem_filter.mp hyq).2
    have hayc := (Finset.mem_filter.mp hyc).2
    have hyO : y.1 ∈ O := y.2
    have hyB : y.1 ∈ B 1 := (Finset.mem_filter.mp hyO).1
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
    have hyO : y.1 ∈ O := y.2
    have hyB : y.1 ∈ B 1 := (Finset.mem_filter.mp hyO).1
    have hincCard : (G.neighborFinset y.1 ∩
        squareOrderHighVertices G 9).card = 1 :=
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
  have hKdeg : ∀ y : ↥(↑O : Set V), K.degree y = 2 := by
    simpa [K, O, B, D] using
      (squareOrderNine_threeHigh_firstProfile_ordinary_binOne_defect_twoRegular
        G hfree hmin hcover hcard hp hhigh hc3 hc4)
  have independentColor (r : V) (hrH : r ∈ squareOrderHighVertices G 9)
      (R : Finset ↥(↑O : Set V))
      (hR : R = (Finset.univ.filter fun y => y.1 ∈ G.neighborFinset r)) :
      ∀ x ∈ R, (K.neighborFinset x ∩ R).card = 0 := by
    intro x hx
    rw [Finset.card_eq_zero]
    ext z
    simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
    intro hxz hzR
    have hxr : x.1 ∈ G.neighborFinset r := by rw [hR] at hx; exact (Finset.mem_filter.mp hx).2
    have hzr : z.1 ∈ G.neighborFinset r := by rw [hR] at hzR; exact (Finset.mem_filter.mp hzR).2
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
  have hpartQ : Q ∪ C ∪ A = Finset.univ := by
    rw [← hpart]
    ext x
    simp only [Finset.mem_union]
    tauto
  have hpartC : C ∪ A ∪ Q = Finset.univ := by
    rw [← hpart]
    ext x
    simp only [Finset.mem_union]
    tauto
  exact ⟨
    threePart_twoRegular_crossEdge_ledger K A Q C 7 hpart hAQ hAC hQC
      hAcard hQcard hCcard hKdeg hAind hQind hCind,
    threePart_twoRegular_exists_cross_wedge_of_odd K A Q C 7 hpart
      hAQ hAC hQC hAcard hQcard hCcard hKdeg hAind hQind hCind (by norm_num),
    threePart_twoRegular_exists_cross_wedge_of_odd K Q C A 7 hpartQ
      hQC hAQ.symm hAC.symm hQcard hCcard hAcard hKdeg hQind hCind hAind
      (by norm_num),
    threePart_twoRegular_exists_cross_wedge_of_odd K C A Q 7 hpartC
      hAC.symm hQC.symm hAQ hCcard hAcard hQcard hKdeg hCind hAind hQind
      (by norm_num)⟩

/-- The cross-edge ledger projection of the full ordinary-color structure. -/
theorem squareOrderNine_threeHigh_firstProfile_ordinary_color_edge_ledger
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (hH : squareOrderHighVertices G 9 = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let O := (B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 0
    let K := D.induce (↑O : Set V)
    let A := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset a
    let Q := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset b
    let C := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset c
    (∑ x ∈ A, (K.neighborFinset x ∩ Q).card) = 7 ∧
      (∑ x ∈ Q, (K.neighborFinset x ∩ C).card) = 7 ∧
      (∑ x ∈ C, (K.neighborFinset x ∩ A).card) = 7 := by
  exact (squareOrderNine_threeHigh_firstProfile_ordinary_color_structure
    G hfree hmin hcover hcard hp hhigh hc3 hc4 hH hab hac hbc).1

/-- Each high color contains an ordinary bin-one vertex whose two defect
neighbors have the other two high colors, one of each. -/
theorem squareOrderNine_threeHigh_firstProfile_ordinary_rainbow_wedges
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
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 0)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {a b c : V}
    (hH : squareOrderHighVertices G 9 = {a, b, c})
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let O := (B 1).filter fun y => (D.neighborFinset y ∩ B 2).card = 0
    let K := D.induce (↑O : Set V)
    let A := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset a
    let Q := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset b
    let C := (Finset.univ : Finset ↥(↑O : Set V)).filter fun y =>
      y.1 ∈ G.neighborFinset c
    (∃ x ∈ A, (K.neighborFinset x ∩ Q).card = 1 ∧
      (K.neighborFinset x ∩ C).card = 1) ∧
    (∃ x ∈ Q, (K.neighborFinset x ∩ C).card = 1 ∧
      (K.neighborFinset x ∩ A).card = 1) ∧
    (∃ x ∈ C, (K.neighborFinset x ∩ A).card = 1 ∧
      (K.neighborFinset x ∩ Q).card = 1) := by
  exact (squareOrderNine_threeHigh_firstProfile_ordinary_color_structure
    G hfree hmin hcover hcard hp hhigh hc3 hc4 hH hab hac hbc).2

end

end Erdos85

#print axioms Erdos85.squareOrderNine_threeHigh_firstProfile_ordinary_color_edge_ledger
#print axioms Erdos85.squareOrderNine_threeHigh_firstProfile_ordinary_rainbow_wedges

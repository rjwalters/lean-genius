import Proofs.Erdos85OrderFortyNineThreeHighDistOneC2Normalization

/-! # Normalization infrastructure for the three-high `dist1_c1` scout -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Coordinate targets for the three high neighborhoods in the unpaired,
no-sibling-coincidence case.  Coordinates `0` and `2` are the two pairwise
intersection roots; their local matching mates occupy `1` and `3`. -/
def orderFortyNineDistOneC1FirstTarget : Fin 8 → Fin 49 :=
  ![3, 6, 4, 7, 8, 9, 10, 11]

def orderFortyNineDistOneC1SecondTarget : Fin 8 → Fin 49 :=
  ![3, 12, 5, 13, 14, 15, 16, 17]

def orderFortyNineDistOneC1ThirdTarget : Fin 8 → Fin 49 :=
  ![4, 18, 5, 19, 20, 21, 22, 23]

set_option maxRecDepth 100000 in
theorem orderFortyNineDistOneC1FirstTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneC1FirstTarget
      [3, 4, 6, 7, 8, 9, 10, 11]
      [(3, 6), (4, 7), (8, 9), (10, 11)] := by
  unfold OrderFortyNineStandardMatchingTarget
  decide

set_option maxRecDepth 100000 in
theorem orderFortyNineDistOneC1SecondTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneC1SecondTarget
      [3, 5, 12, 13, 14, 15, 16, 17]
      [(3, 12), (5, 13), (14, 15), (16, 17)] := by
  unfold OrderFortyNineStandardMatchingTarget
  decide

set_option maxRecDepth 100000 in
theorem orderFortyNineDistOneC1ThirdTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneC1ThirdTarget
      [4, 5, 18, 19, 20, 21, 22, 23]
      [(4, 18), (5, 19), (20, 21), (22, 23)] := by
  unfold OrderFortyNineStandardMatchingTarget
  decide

abbrev ThreeC1OverlapIndex := Fin 8 ⊕ (Fin 7 ⊕ Fin 6)

def orderFortyNineDistOneC1ThirdKeep : Fin 6 → Fin 8 :=
  ![1, 3, 4, 5, 6, 7]

theorem orderFortyNineDistOneC1ThirdKeep_injective :
    Function.Injective orderFortyNineDistOneC1ThirdKeep := by
  decide

theorem orderFortyNineDistOneC1ThirdKeep_ne_zero (i : Fin 6) :
    orderFortyNineDistOneC1ThirdKeep i ≠ 0 := by
  fin_cases i <;> decide

theorem orderFortyNineDistOneC1ThirdKeep_ne_two (i : Fin 6) :
    orderFortyNineDistOneC1ThirdKeep i ≠ 2 := by
  fin_cases i <;> decide

def threeC1OverlapSource
    {V : Type*} [DecidableEq V]
    (A B C : Finset V)
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8) : ThreeC1OverlapIndex → V
  | Sum.inl i => (eA.symm i).1
  | Sum.inr (Sum.inl i) => (eB.symm i.succ).1
  | Sum.inr (Sum.inr i) =>
      (eC.symm (orderFortyNineDistOneC1ThirdKeep i)).1

theorem threeC1OverlapSource_injective
    {V : Type*} [DecidableEq V]
    (A B C : Finset V) {uAB uAC uBC : V}
    (huAB_B : uAB ∈ B) (huAC_C : uAC ∈ C) (huBC_C : uBC ∈ C)
    (hAB : A ∩ B = {uAB}) (hAC : A ∩ C = {uAC})
    (hBC : B ∩ C = {uBC})
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8)
    (hAB_B_coord : eB ⟨uAB, huAB_B⟩ = 0)
    (hAC_C_coord : eC ⟨uAC, huAC_C⟩ = 0)
    (hBC_C_coord : eC ⟨uBC, huBC_C⟩ = 2) :
    Function.Injective (threeC1OverlapSource A B C eA eB eC) := by
  have hABne : ∀ (i : Fin 8) (j : Fin 7),
      (eA.symm i).1 ≠ (eB.symm j.succ).1 := by
    intro i j hij
    have hx : (eA.symm i).1 ∈ A ∩ B :=
      Finset.mem_inter.mpr ⟨(eA.symm i).2, hij ▸ (eB.symm j.succ).2⟩
    have hxroot : (eA.symm i).1 = uAB := by simpa [hAB] using hx
    have hbsub : eB.symm j.succ = ⟨uAB, huAB_B⟩ :=
      Subtype.ext (hij.symm.trans hxroot)
    have he := congrArg eB hbsub
    simp only [eB.apply_symm_apply, hAB_B_coord] at he
    exact Fin.succ_ne_zero j he
  have hACne : ∀ (i : Fin 8) (j : Fin 6),
      (eA.symm i).1 ≠
        (eC.symm (orderFortyNineDistOneC1ThirdKeep j)).1 := by
    intro i j hij
    have hx : (eA.symm i).1 ∈ A ∩ C :=
      Finset.mem_inter.mpr ⟨(eA.symm i).2,
        hij ▸ (eC.symm (orderFortyNineDistOneC1ThirdKeep j)).2⟩
    have hxroot : (eA.symm i).1 = uAC := by simpa [hAC] using hx
    have hcsub : eC.symm (orderFortyNineDistOneC1ThirdKeep j) =
        ⟨uAC, huAC_C⟩ := Subtype.ext (hij.symm.trans hxroot)
    have he := congrArg eC hcsub
    simp only [eC.apply_symm_apply, hAC_C_coord] at he
    exact orderFortyNineDistOneC1ThirdKeep_ne_zero j he
  have hBCne : ∀ (i : Fin 7) (j : Fin 6),
      (eB.symm i.succ).1 ≠
        (eC.symm (orderFortyNineDistOneC1ThirdKeep j)).1 := by
    intro i j hij
    have hx : (eB.symm i.succ).1 ∈ B ∩ C :=
      Finset.mem_inter.mpr ⟨(eB.symm i.succ).2,
        hij ▸ (eC.symm (orderFortyNineDistOneC1ThirdKeep j)).2⟩
    have hxroot : (eB.symm i.succ).1 = uBC := by simpa [hBC] using hx
    have hcsub : eC.symm (orderFortyNineDistOneC1ThirdKeep j) =
        ⟨uBC, huBC_C⟩ := Subtype.ext (hij.symm.trans hxroot)
    have he := congrArg eC hcsub
    simp only [eC.apply_symm_apply, hBC_C_coord] at he
    exact orderFortyNineDistOneC1ThirdKeep_ne_two j he
  intro p q hpq
  cases p with
  | inl i =>
      cases q with
      | inl j =>
          exact congrArg Sum.inl (eA.symm.injective (Subtype.ext hpq))
      | inr q =>
          cases q with
          | inl j => exact (hABne i j hpq).elim
          | inr j => exact (hACne i j hpq).elim
  | inr p =>
      cases p with
      | inl i =>
          cases q with
          | inl j => exact (hABne j i hpq.symm).elim
          | inr q =>
              cases q with
              | inl j =>
                  exact congrArg Sum.inr (congrArg Sum.inl
                    (Fin.succ_injective 7
                      (eB.symm.injective (Subtype.ext hpq))))
              | inr j => exact (hBCne i j hpq).elim
      | inr i =>
          cases q with
          | inl j => exact (hACne j i hpq.symm).elim
          | inr q =>
              cases q with
              | inl j => exact (hBCne j i hpq.symm).elim
              | inr j =>
                  apply congrArg Sum.inr
                  apply congrArg Sum.inr
                  apply orderFortyNineDistOneC1ThirdKeep_injective
                  exact eC.symm.injective (Subtype.ext hpq)

def orderFortyNineDistOneC1OverlapTarget :
    ThreeC1OverlapIndex → Fin 49
  | Sum.inl i => orderFortyNineDistOneC1FirstTarget i
  | Sum.inr (Sum.inl i) => orderFortyNineDistOneC1SecondTarget i.succ
  | Sum.inr (Sum.inr i) =>
      orderFortyNineDistOneC1ThirdTarget
        (orderFortyNineDistOneC1ThirdKeep i)

theorem orderFortyNineDistOneC1OverlapTarget_injective :
    Function.Injective orderFortyNineDistOneC1OverlapTarget := by
  decide

def orderFortyNineDistOneC1HighTarget : Fin 3 → Fin 49 := ![0, 1, 2]

theorem orderFortyNineDistOneC1HighTarget_injective :
    Function.Injective orderFortyNineDistOneC1HighTarget := by
  decide

theorem orderFortyNineDistOneC1HighTarget_disjoint_overlap :
    ∀ i j, orderFortyNineDistOneC1HighTarget i ≠
      orderFortyNineDistOneC1OverlapTarget j := by
  decide

/-- Extend the three locally normalized neighborhoods, deduplicating their
three singleton overlaps, and simultaneously pin the high vertices. -/
theorem exists_orderFortyNine_equiv_of_threeC1Overlap_with_highs
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 49)
    (A B C : Finset V) {uAB uAC uBC : V}
    (huAB_B : uAB ∈ B) (huAC_C : uAC ∈ C) (huBC_C : uBC ∈ C)
    (hAB : A ∩ B = {uAB}) (hAC : A ∩ C = {uAC})
    (hBC : B ∩ C = {uBC})
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8)
    (hAB_B_coord : eB ⟨uAB, huAB_B⟩ = 0)
    (hAC_C_coord : eC ⟨uAC, huAC_C⟩ = 0)
    (hBC_C_coord : eC ⟨uBC, huBC_C⟩ = 2)
    (high : Fin 3 → V) (hhigh : Function.Injective high)
    (hcross : ∀ i j,
      high i ≠ threeC1OverlapSource A B C eA eB eC j) :
    ∃ E : V ≃ Fin 49,
      (∀ i, E (high i) = orderFortyNineDistOneC1HighTarget i) ∧
      (∀ j, E (threeC1OverlapSource A B C eA eB eC j) =
        orderFortyNineDistOneC1OverlapTarget j) := by
  exact exists_equiv_fin_extending_disjoint_pairs hcard
    high (threeC1OverlapSource A B C eA eB eC)
    orderFortyNineDistOneC1HighTarget
    orderFortyNineDistOneC1OverlapTarget
    hhigh
    (threeC1OverlapSource_injective A B C huAB_B huAC_C huBC_C
      hAB hAC hBC eA eB eC hAB_B_coord hAC_C_coord hBC_C_coord)
    orderFortyNineDistOneC1HighTarget_injective
    orderFortyNineDistOneC1OverlapTarget_injective hcross
    orderFortyNineDistOneC1HighTarget_disjoint_overlap

theorem exists_orderFortyNine_threeHighDistOneC1_geometryLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v1 v2 v3 u12 u13 u23 x2 x3 : Fin 49}
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hu12 : G.neighborFinset v1 ∩ G.neighborFinset v2 = {u12})
    (hu13 : G.neighborFinset v1 ∩ G.neighborFinset v3 = {u13})
    (hu23 : G.neighborFinset v2 ∩ G.neighborFinset v3 = {u23})
    (hu1213 : u12 ≠ u13) (hu1223 : u12 ≠ u23)
    (hu1323 : u13 ≠ u23)
    (hnotPair : ¬ G.Adj u12 u13)
    (hx2u12 : G.Adj u12 x2) (hx2v2 : G.Adj v2 x2)
    (hx3u13 : G.Adj u13 x3) (hx3v3 : G.Adj v3 x3)
    (hx2ne : x2 ≠ u23) (hx3ne : x3 ≠ u23) :
    ∃ E : Equiv.Perm (Fin 49),
      let H := orderFortyNineRelabeledGraph G E
      E v1 = 0 ∧ E v2 = 1 ∧ E v3 = 2 ∧
      H.neighborFinset 0 =
        Finset.univ.image orderFortyNineDistOneC1FirstTarget ∧
      H.neighborFinset 1 =
        Finset.univ.image orderFortyNineDistOneC1SecondTarget ∧
      H.neighborFinset 2 =
        Finset.univ.image orderFortyNineDistOneC1ThirdTarget ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [3, 4, 6, 7, 8, 9, 10, 11]
        [(3, 6), (4, 7), (8, 9), (10, 11)] ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [3, 5, 12, 13, 14, 15, 16, 17]
        [(3, 12), (5, 13), (14, 15), (16, 17)] ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [4, 5, 18, 19, 20, 21, 22, 23]
        [(4, 18), (5, 19), (20, 21), (22, 23)] := by
  have hu12mem : u12 ∈ G.neighborFinset v1 ∩ G.neighborFinset v2 := by
    simp [hu12]
  have hu13mem : u13 ∈ G.neighborFinset v1 ∩ G.neighborFinset v3 := by
    simp [hu13]
  have hu23mem : u23 ∈ G.neighborFinset v2 ∩ G.neighborFinset v3 := by
    simp [hu23]
  have hu12v1 : G.Adj u12 v1 :=
    ((G.mem_neighborFinset v1 u12).mp (Finset.mem_inter.mp hu12mem).1).symm
  have hu12v2 : G.Adj u12 v2 :=
    ((G.mem_neighborFinset v2 u12).mp (Finset.mem_inter.mp hu12mem).2).symm
  have hu13v1 : G.Adj u13 v1 :=
    ((G.mem_neighborFinset v1 u13).mp (Finset.mem_inter.mp hu13mem).1).symm
  have hu13v3 : G.Adj u13 v3 :=
    ((G.mem_neighborFinset v3 u13).mp (Finset.mem_inter.mp hu13mem).2).symm
  have hu23v2 : G.Adj u23 v2 :=
    ((G.mem_neighborFinset v2 u23).mp (Finset.mem_inter.mp hu23mem).1).symm
  have hu23v3 : G.Adj u23 v3 :=
    ((G.mem_neighborFinset v3 u23).mp (Finset.mem_inter.mp hu23mem).2).symm
  have hnot12_23 : ¬ G.Adj u12 u23 := by
    intro hadj
    have hu := orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin (Fintype.card_fin 49) hv2 hu12v2
    have heq := hu.unique ⟨hadj, hu23v2.symm⟩ ⟨hx2u12, hx2v2⟩
    exact hx2ne heq.symm
  have hnot13_23 : ¬ G.Adj u13 u23 := by
    intro hadj
    have hu := orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin (Fintype.card_fin 49) hv3 hu13v3
    have heq := hu.unique ⟨hadj, hu23v3.symm⟩ ⟨hx3u13, hx3v3⟩
    exact hx3ne heq.symm
  obtain ⟨eA, hA0, hA2, hcanA⟩ :=
    exists_orderFortyNine_highNeighborhood_two_rooted_matching
      G hfree hmin (Fintype.card_fin 49) hv1 hu12v1 hu13v1
      hu1213 hnotPair
  obtain ⟨eB, hB0, hB2, hcanB⟩ :=
    exists_orderFortyNine_highNeighborhood_two_rooted_matching
      G hfree hmin (Fintype.card_fin 49) hv2 hu12v2 hu23v2
      hu1223 hnot12_23
  obtain ⟨eC, hC0, hC2, hcanC⟩ :=
    exists_orderFortyNine_highNeighborhood_two_rooted_matching
      G hfree hmin (Fintype.card_fin 49) hv3 hu13v3 hu23v3
      hu1323 hnot13_23
  let A := G.neighborFinset v1
  let B := G.neighborFinset v2
  let C := G.neighborFinset v3
  let toA : {x : Fin 49 // x ∈ A} ≃
      {x : Fin 49 // x ∈ G.neighborSet v1} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [A])
  let toB : {x : Fin 49 // x ∈ B} ≃
      {x : Fin 49 // x ∈ G.neighborSet v2} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [B])
  let toC : {x : Fin 49 // x ∈ C} ≃
      {x : Fin 49 // x ∈ G.neighborSet v3} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [C])
  let eA' := toA.trans eA
  let eB' := toB.trans eB
  let eC' := toC.trans eC
  have hu12B : u12 ∈ B := by simpa [B] using (Finset.mem_inter.mp hu12mem).2
  have hu13C : u13 ∈ C := by simpa [C] using (Finset.mem_inter.mp hu13mem).2
  have hu23C : u23 ∈ C := by simpa [C] using (Finset.mem_inter.mp hu23mem).2
  have hB0' : eB' ⟨u12, hu12B⟩ = 0 := by simpa [eB', toB] using hB0
  have hC0' : eC' ⟨u13, hu13C⟩ = 0 := by simpa [eC', toC] using hC0
  have hC2' : eC' ⟨u23, hu23C⟩ = 2 := by simpa [eC', toC] using hC2
  let high : Fin 3 → Fin 49 := ![v1, v2, v3]
  have hhigh : Function.Injective high := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [high, h12, h13, h23, Ne.symm h12, Ne.symm h13, Ne.symm h23]
  have hn12 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin (Fintype.card_fin 49) hv1 hv2
  have hn13 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin (Fintype.card_fin 49) hv1 hv3
  have hn23 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin (Fintype.card_fin 49) hv2 hv3
  have houtside : ∀ z : Fin 49,
      ¬ G.Adj z v1 → ¬ G.Adj z v2 → ¬ G.Adj z v3 →
      ∀ j, z ≠ threeC1OverlapSource A B C eA' eB' eC' j := by
    intro z hz1 hz2 hz3 j
    rcases j with j | j
    · intro heq
      apply hz1
      have hm := (eA'.symm j).2
      simpa [threeC1OverlapSource, A, G.adj_comm, heq] using
        ((G.mem_neighborFinset v1 _).mp hm)
    · rcases j with j | j
      · intro heq
        apply hz2
        have hm := (eB'.symm j.succ).2
        simpa [threeC1OverlapSource, B, G.adj_comm, heq] using
          ((G.mem_neighborFinset v2 _).mp hm)
      · intro heq
        apply hz3
        have hm := (eC'.symm (orderFortyNineDistOneC1ThirdKeep j)).2
        simpa [threeC1OverlapSource, C, G.adj_comm, heq] using
          ((G.mem_neighborFinset v3 _).mp hm)
  have hcross : ∀ i j,
      high i ≠ threeC1OverlapSource A B C eA' eB' eC' j := by
    intro i
    fin_cases i
    · exact houtside v1 (G.loopless.irrefl v1) hn12 hn13
    · exact houtside v2 (by simpa [G.adj_comm] using hn12)
        (G.loopless.irrefl v2) hn23
    · exact houtside v3 (by simpa [G.adj_comm] using hn13)
        (by simpa [G.adj_comm] using hn23) (G.loopless.irrefl v3)
  obtain ⟨E, hHighMap, hOverlap⟩ :=
    exists_orderFortyNine_equiv_of_threeC1Overlap_with_highs
      (Fintype.card_fin 49) A B C hu12B hu13C hu23C
      (by simpa [A, B] using hu12) (by simpa [A, C] using hu13)
      (by simpa [B, C] using hu23) eA' eB' eC'
      hB0' hC0' hC2' high hhigh hcross
  have hmapA : ∀ i, E (eA.symm i).1 =
      orderFortyNineDistOneC1FirstTarget i := by
    intro i
    simpa [threeC1OverlapSource, orderFortyNineDistOneC1OverlapTarget,
      eA', toA] using hOverlap (Sum.inl i)
  have hArootSymm : eA.symm 0 =
      ⟨u12, by simpa using hu12v1.symm⟩ := by
    apply eA.injective
    simp [hA0]
  have hAotherSymm : eA.symm 2 =
      ⟨u13, by simpa using hu13v1.symm⟩ := by
    apply eA.injective
    simp [hA2]
  have hBrootSymm : eB.symm 0 =
      ⟨u12, by simpa using hu12v2.symm⟩ := by
    apply eB.injective
    simp [hB0]
  have hBotherSymm : eB.symm 2 =
      ⟨u23, by simpa using hu23v2.symm⟩ := by
    apply eB.injective
    simp [hB2]
  have hCrootSymm : eC.symm 0 =
      ⟨u13, by simpa using hu13v3.symm⟩ := by
    apply eC.injective
    simp [hC0]
  have hCotherSymm : eC.symm 2 =
      ⟨u23, by simpa using hu23v3.symm⟩ := by
    apply eC.injective
    simp [hC2]
  have hmapB : ∀ i, E (eB.symm i).1 =
      orderFortyNineDistOneC1SecondTarget i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hBrootSymm, hArootSymm,
        orderFortyNineDistOneC1SecondTarget,
        orderFortyNineDistOneC1FirstTarget] using hmapA 0
    · simpa [threeC1OverlapSource,
        orderFortyNineDistOneC1OverlapTarget, eB', toB] using
        hOverlap (Sum.inr (Sum.inl j))
  have hmapC : ∀ i, E (eC.symm i).1 =
      orderFortyNineDistOneC1ThirdTarget i := by
    intro i
    fin_cases i
    · simpa [hCrootSymm, hAotherSymm,
        orderFortyNineDistOneC1ThirdTarget,
        orderFortyNineDistOneC1FirstTarget] using hmapA 2
    · simpa [threeC1OverlapSource,
        orderFortyNineDistOneC1OverlapTarget,
        orderFortyNineDistOneC1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (0 : Fin 6)))
    · simpa [hCotherSymm, hBotherSymm,
        orderFortyNineDistOneC1ThirdTarget,
        orderFortyNineDistOneC1SecondTarget] using hmapB 2
    · simpa [threeC1OverlapSource,
        orderFortyNineDistOneC1OverlapTarget,
        orderFortyNineDistOneC1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (1 : Fin 6)))
    · simpa [threeC1OverlapSource,
        orderFortyNineDistOneC1OverlapTarget,
        orderFortyNineDistOneC1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (2 : Fin 6)))
    · simpa [threeC1OverlapSource,
        orderFortyNineDistOneC1OverlapTarget,
        orderFortyNineDistOneC1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (3 : Fin 6)))
    · simpa [threeC1OverlapSource,
        orderFortyNineDistOneC1OverlapTarget,
        orderFortyNineDistOneC1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (4 : Fin 6)))
    · simpa [threeC1OverlapSource,
        orderFortyNineDistOneC1OverlapTarget,
        orderFortyNineDistOneC1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (5 : Fin 6)))
  have hEv1 : E v1 = 0 := by
    simpa [high, orderFortyNineDistOneC1HighTarget] using hHighMap 0
  have hEv2 : E v2 = 1 := by
    simpa [high, orderFortyNineDistOneC1HighTarget] using hHighMap 1
  have hEv3 : E v3 = 2 := by
    simpa [high, orderFortyNineDistOneC1HighTarget] using hHighMap 2
  have hN0 := orderFortyNineRelabeledGraph_neighborFinset_eq_targetImage_of_map
    G eA E orderFortyNineDistOneC1FirstTarget hmapA
  have hN1 := orderFortyNineRelabeledGraph_neighborFinset_eq_targetImage_of_map
    G eB E orderFortyNineDistOneC1SecondTarget hmapB
  have hN2 := orderFortyNineRelabeledGraph_neighborFinset_eq_targetImage_of_map
    G eC E orderFortyNineDistOneC1ThirdTarget hmapC
  have hm0 := orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
    G eA E orderFortyNineDistOneC1FirstTarget
      [3, 4, 6, 7, 8, 9, 10, 11]
      [(3, 6), (4, 7), (8, 9), (10, 11)]
      hcanA hmapA orderFortyNineDistOneC1FirstTarget_standard
  have hm1 := orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
    G eB E orderFortyNineDistOneC1SecondTarget
      [3, 5, 12, 13, 14, 15, 16, 17]
      [(3, 12), (5, 13), (14, 15), (16, 17)]
      hcanB hmapB orderFortyNineDistOneC1SecondTarget_standard
  have hm2 := orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
    G eC E orderFortyNineDistOneC1ThirdTarget
      [4, 5, 18, 19, 20, 21, 22, 23]
      [(4, 18), (5, 19), (20, 21), (22, 23)]
      hcanC hmapC orderFortyNineDistOneC1ThirdTarget_standard
  refine ⟨E, hEv1, hEv2, hEv3, ?_, ?_, ?_, hm0, hm1, hm2⟩
  · rw [hEv1] at hN0
    exact hN0
  · rw [hEv2] at hN1
    exact hN1
  · rw [hEv3] at hN2
    exact hN2

theorem orderFortyNineThreeHighDistOneC1_smallHighAlignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v1 v2 v3 : Fin 49}
    (hHigh : orderFortyNineHighVertices G = {v1, v2, v3})
    (E : Equiv.Perm (Fin 49))
    (hEv1 : E v1 = 0) (hEv2 : E v2 = 1) (hEv3 : E v3 = 2)
    (hN0 : (orderFortyNineRelabeledGraph G E).neighborFinset 0 =
      Finset.univ.image orderFortyNineDistOneC1FirstTarget)
    (hN1 : (orderFortyNineRelabeledGraph G E).neighborFinset 1 =
      Finset.univ.image orderFortyNineDistOneC1SecondTarget)
    (hN2 : (orderFortyNineRelabeledGraph G E).neighborFinset 2 =
      Finset.univ.image orderFortyNineDistOneC1ThirdTarget) :
    SmallHighAlignedLabeling 3 G E
      orderFortyNineThreeHighDistOneNoCoincidenceMasks := by
  let H := orderFortyNineRelabeledGraph G E
  letI : DecidableRel (antipodalGraph H).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph H).Adj := Classical.decRel _
  have hdegree : ∀ i : Fin 49, H.degree i =
      if i.val < 3 then 8 else 7 := by
    intro i
    by_cases hi : i.val < 3
    · have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi' with rfl | rfl | rfl
      · rw [if_pos (by omega), ← H.card_neighborFinset_eq_degree, hN0]
        decide
      · rw [if_pos (by omega), ← H.card_neighborFinset_eq_degree, hN1]
        decide
      · rw [if_pos (by omega), ← H.card_neighborFinset_eq_degree, hN2]
        decide
    · rw [if_neg hi, orderFortyNineRelabeledGraph_degree]
      rcases orderFortyNine_degree_eq_seven_or_eight
          G hfree hmin (Fintype.card_fin 49) (E.symm i) with h7 | h8
      · exact h7
      · exfalso
        have hm : E.symm i = v1 ∨ E.symm i = v2 ∨ E.symm i = v3 := by
          have : E.symm i ∈ orderFortyNineHighVertices G :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h8⟩
          rw [hHigh] at this
          simpa using this
        rcases hm with hm | hm | hm
        · apply hi
          have : i = 0 := by
            have h := congrArg E hm
            simpa [hEv1] using h
          simp [this]
        · apply hi
          have : i = 1 := by
            have h := congrArg E hm
            simpa [hEv2] using h
          simp [this]
        · apply hi
          have : i = 2 := by
            have h := congrArg E hm
            simpa [hEv3] using h
          simp [this]
  have hsupport : ∀ i : Fin 49, ∀ w : Fin 9, w.val < 3 →
      decide (H.Adj i ⟨w.val, by omega⟩) =
        (orderFortyNineSupportMask
          orderFortyNineThreeHighDistOneNoCoincidenceMasks i).getLsbD w.val := by
    intro i w hw
    have hAdj0 : H.Adj i 0 ↔
        i ∈ Finset.univ.image orderFortyNineDistOneC1FirstTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN0]
    have hAdj1 : H.Adj i 1 ↔
        i ∈ Finset.univ.image orderFortyNineDistOneC1SecondTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN1]
    have hAdj2 : H.Adj i 2 ↔
        i ∈ Finset.univ.image orderFortyNineDistOneC1ThirdTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN2]
    have hw' : w = 0 ∨ w = 1 ∨ w = 2 := by omega
    rcases hw' with rfl | rfl | rfl
    · rw [Bool.eq_iff_iff, decide_eq_true_eq]
      change H.Adj i 0 ↔ _
      rw [hAdj0]
      fin_cases i <;> decide
    · rw [Bool.eq_iff_iff, decide_eq_true_eq]
      change H.Adj i 1 ↔ _
      rw [hAdj1]
      fin_cases i <;> decide
    · rw [Bool.eq_iff_iff, decide_eq_true_eq]
      change H.Adj i 2 ↔ _
      rw [hAdj2]
      fin_cases i <;> decide
  refine ⟨orderFortyNineThreeHighDistOneNoCoincidenceMasks_size,
    hdegree, hsupport, ?_⟩
  intro i hi w hw
  let wi : Fin 49 := ⟨w.val, by omega⟩
  have hfiber : orderFortyNineSupportFiber
      orderFortyNineThreeHighDistOneNoCoincidenceMasks w =
      H.neighborFinset wi := by
    ext k
    simp only [orderFortyNineSupportFiber, Finset.mem_filter,
      Finset.mem_univ, true_and]
    have hs := hsupport k w hw
    rw [← hs]
    simp [wi, H.adj_comm, SimpleGraph.mem_neighborFinset]
  rw [hfiber]
  have hi3 : ¬ i.val < 3 := by omega
  have hwi3 : wi.val < 3 := by simpa [wi] using hw
  exact orderFortyNine_low_high_card_common_eq_one H
    (orderFortyNineRelabeledGraph_not_containsC4 G E hfree)
    (fun x => by rw [hdegree]; split <;> omega)
    (Fintype.card_fin 49)
    (by simpa [hi3] using hdegree i)
    (by simpa [hwi3] using hdegree wi)

theorem exists_orderFortyNine_threeHighDistOneC1_alignedLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    {v1 v2 v3 u12 u13 u23 x2 x3 : Fin 49}
    (hHigh : orderFortyNineHighVertices G = {v1, v2, v3})
    (hv1 : G.degree v1 = 8) (hv2 : G.degree v2 = 8)
    (hv3 : G.degree v3 = 8)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hu12 : G.neighborFinset v1 ∩ G.neighborFinset v2 = {u12})
    (hu13 : G.neighborFinset v1 ∩ G.neighborFinset v3 = {u13})
    (hu23 : G.neighborFinset v2 ∩ G.neighborFinset v3 = {u23})
    (hu1213 : u12 ≠ u13) (hu1223 : u12 ≠ u23)
    (hu1323 : u13 ≠ u23)
    (hnotPair : ¬ G.Adj u12 u13)
    (hx2u12 : G.Adj u12 x2) (hx2v2 : G.Adj v2 x2)
    (hx3u13 : G.Adj u13 x3) (hx3v3 : G.Adj v3 x3)
    (hx2ne : x2 ≠ u23) (hx3ne : x3 ≠ u23) :
    ∃ E : Equiv.Perm (Fin 49),
      ThreeHighDistOneC1ScoutAlignedLabeling G E := by
  obtain ⟨E, hEv1, hEv2, hEv3, hN0, hN1, hN2, hm0, hm1, hm2⟩ :=
    exists_orderFortyNine_threeHighDistOneC1_geometryLabeling
      G hfree hmin hv1 hv2 hv3 h12 h13 h23 hu12 hu13 hu23
      hu1213 hu1223 hu1323 hnotPair hx2u12 hx2v2 hx3u13 hx3v3
      hx2ne hx3ne
  exact ⟨E,
    orderFortyNineThreeHighDistOneC1_smallHighAlignedLabeling
      G hfree hmin hHigh E hEv1 hEv2 hEv3 hN0 hN1 hN2,
    hm0, hm1, hm2⟩

theorem orderFortyNine_threeHighDistOneC1AlignedCover :
    ThreeHighDistOneC1AlignedCover := by
  intro G _ _ _ hfree hmin D
  rintro ⟨x2, x3, hsib, hnotPair, hx2ne, hx3ne⟩
  rcases hsib with
    ⟨_hx2deg, _hx3deg, hx2u12, hx2v2, hx3u13, hx3v3⟩
  exact exists_orderFortyNine_threeHighDistOneC1_alignedLabeling
    G hfree hmin D.hHigh D.hv1 D.hv2 D.hv3
    D.h12 D.h13 D.h23 D.hu12 D.hu13 D.hu23
    D.hu1213 D.hu1223 D.hu1323 hnotPair
    hx2u12 hx2v2 hx3u13 hx3v3 hx2ne hx3ne

end

end Erdos85

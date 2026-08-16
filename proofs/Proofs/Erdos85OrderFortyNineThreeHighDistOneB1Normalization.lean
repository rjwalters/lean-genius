import Proofs.Erdos85OrderFortyNineThreeHighDistOneC2Normalization
import Proofs.Erdos85OrderFortyNineThreeHighDistOneCaseTerminal

/-! # Normalization of the three-high distance-one `b1` geometry

The three pairwise high-neighborhood intersections are sent to coordinates
`3`, `4`, and `5`.  In the `b1` case the first two intersection vertices are
partners in the first high neighborhood, while the other two local views have
the two distinguished roots in separate matching edges.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

def orderFortyNineDistOneB1FirstTarget : Fin 8 → Fin 49 :=
  ![3, 4, 6, 7, 8, 9, 10, 11]

def orderFortyNineDistOneB1SecondTarget : Fin 8 → Fin 49 :=
  ![3, 12, 5, 13, 14, 15, 16, 17]

def orderFortyNineDistOneB1ThirdTarget : Fin 8 → Fin 49 :=
  ![4, 18, 5, 19, 20, 21, 22, 23]

theorem orderFortyNineDistOneB1FirstTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneB1FirstTarget
      [3, 4, 6, 7, 8, 9, 10, 11]
      [(3, 4), (6, 7), (8, 9), (10, 11)] := by
  unfold OrderFortyNineStandardMatchingTarget
  decide +kernel

theorem orderFortyNineDistOneB1SecondTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneB1SecondTarget
      [3, 5, 12, 13, 14, 15, 16, 17]
      [(3, 12), (5, 13), (14, 15), (16, 17)] := by
  unfold OrderFortyNineStandardMatchingTarget
  decide +kernel

theorem orderFortyNineDistOneB1ThirdTarget_standard :
    OrderFortyNineStandardMatchingTarget
      orderFortyNineDistOneB1ThirdTarget
      [4, 5, 18, 19, 20, 21, 22, 23]
      [(4, 18), (5, 19), (20, 21), (22, 23)] := by
  unfold OrderFortyNineStandardMatchingTarget
  decide +kernel

abbrev ThreeB1CyclicOverlapIndex := Fin 8 ⊕ (Fin 7 ⊕ Fin 6)

def orderFortyNineDistOneB1ThirdKeep : Fin 6 → Fin 8 :=
  ![1, 3, 4, 5, 6, 7]

def threeB1CyclicOverlapSource
    {V : Type*} [DecidableEq V]
    (A B C : Finset V)
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8) : ThreeB1CyclicOverlapIndex → V
  | Sum.inl i => (eA.symm i).1
  | Sum.inr (Sum.inl i) => (eB.symm i.succ).1
  | Sum.inr (Sum.inr i) =>
      (eC.symm (orderFortyNineDistOneB1ThirdKeep i)).1

theorem orderFortyNineDistOneB1ThirdKeep_injective :
    Function.Injective orderFortyNineDistOneB1ThirdKeep := by
  decide +kernel

theorem orderFortyNineDistOneB1ThirdKeep_ne_zero (i : Fin 6) :
    orderFortyNineDistOneB1ThirdKeep i ≠ 0 := by
  fin_cases i <;> decide

theorem orderFortyNineDistOneB1ThirdKeep_ne_two (i : Fin 6) :
    orderFortyNineDistOneB1ThirdKeep i ≠ 2 := by
  fin_cases i <;> decide

theorem threeB1CyclicOverlapSource_injective
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
    Function.Injective (threeB1CyclicOverlapSource A B C eA eB eC) := by
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
        (eC.symm (orderFortyNineDistOneB1ThirdKeep j)).1 := by
    intro i j hij
    have hx : (eA.symm i).1 ∈ A ∩ C :=
      Finset.mem_inter.mpr ⟨(eA.symm i).2,
        hij ▸ (eC.symm (orderFortyNineDistOneB1ThirdKeep j)).2⟩
    have hxroot : (eA.symm i).1 = uAC := by simpa [hAC] using hx
    have hcsub : eC.symm (orderFortyNineDistOneB1ThirdKeep j) =
        ⟨uAC, huAC_C⟩ := Subtype.ext (hij.symm.trans hxroot)
    have he := congrArg eC hcsub
    simp only [eC.apply_symm_apply, hAC_C_coord] at he
    exact orderFortyNineDistOneB1ThirdKeep_ne_zero j he
  have hBCne : ∀ (i : Fin 7) (j : Fin 6),
      (eB.symm i.succ).1 ≠
        (eC.symm (orderFortyNineDistOneB1ThirdKeep j)).1 := by
    intro i j hij
    have hx : (eB.symm i.succ).1 ∈ B ∩ C :=
      Finset.mem_inter.mpr ⟨(eB.symm i.succ).2,
        hij ▸ (eC.symm (orderFortyNineDistOneB1ThirdKeep j)).2⟩
    have hxroot : (eB.symm i.succ).1 = uBC := by simpa [hBC] using hx
    have hcsub : eC.symm (orderFortyNineDistOneB1ThirdKeep j) =
        ⟨uBC, huBC_C⟩ := Subtype.ext (hij.symm.trans hxroot)
    have he := congrArg eC hcsub
    simp only [eC.apply_symm_apply, hBC_C_coord] at he
    exact orderFortyNineDistOneB1ThirdKeep_ne_two j he
  intro p q hpq
  cases p with
  | inl i =>
      cases q with
      | inl j => exact congrArg Sum.inl (eA.symm.injective (Subtype.ext hpq))
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
                  apply orderFortyNineDistOneB1ThirdKeep_injective
                  exact eC.symm.injective (Subtype.ext hpq)

def orderFortyNineDistOneB1OverlapTarget :
    ThreeB1CyclicOverlapIndex → Fin 49
  | Sum.inl i => orderFortyNineDistOneB1FirstTarget i
  | Sum.inr (Sum.inl i) => orderFortyNineDistOneB1SecondTarget i.succ
  | Sum.inr (Sum.inr i) =>
      orderFortyNineDistOneB1ThirdTarget
        (orderFortyNineDistOneB1ThirdKeep i)

theorem orderFortyNineDistOneB1OverlapTarget_injective :
    Function.Injective orderFortyNineDistOneB1OverlapTarget := by
  decide +kernel

theorem orderFortyNineDistOneB1HighTarget_disjoint_overlap :
    ∀ i j, orderFortyNineDistOneC2HighTarget i ≠
      orderFortyNineDistOneB1OverlapTarget j := by
  decide +kernel

/-- Extend the three cyclically overlapping normalized neighborhoods and the
three high centers to a global labeling using the `b1` coordinate target. -/
theorem exists_orderFortyNine_equiv_of_threeCyclicOverlap_b1_with_highs
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
      high i ≠ threeB1CyclicOverlapSource A B C eA eB eC j) :
    ∃ E : V ≃ Fin 49,
      (∀ i, E (high i) = orderFortyNineDistOneC2HighTarget i) ∧
      (∀ j, E (threeB1CyclicOverlapSource A B C eA eB eC j) =
        orderFortyNineDistOneB1OverlapTarget j) := by
  exact exists_equiv_fin_extending_disjoint_pairs hcard
    high (threeB1CyclicOverlapSource A B C eA eB eC)
    orderFortyNineDistOneC2HighTarget
    orderFortyNineDistOneB1OverlapTarget
    hhigh
    (threeB1CyclicOverlapSource_injective A B C huAB_B huAC_C huBC_C
      hAB hAC hBC eA eB eC hAB_B_coord hAC_C_coord hBC_C_coord)
    orderFortyNineDistOneC2HighTarget_injective
    orderFortyNineDistOneB1OverlapTarget_injective hcross
    orderFortyNineDistOneB1HighTarget_disjoint_overlap

theorem orderFortyNineB1_localPartner_coordinate_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v root mate : V} (hrootv : G.Adj root v)
    (hmaterv : G.Adj mate v) (hrootmate : G.Adj root mate)
    (e : {x : V // x ∈ G.neighborSet v} ≃ Fin 8)
    (hroot : e ⟨root, by simpa using hrootv.symm⟩ = 0)
    (hcanonical : ∀ x y,
      decide ((G.induce (G.neighborSet v)).Adj x y) =
        decide (e y = oneHighStandardMate (e x))) :
    e ⟨mate, by simpa using hmaterv.symm⟩ = 1 := by
  let rootLocal : {x : V // x ∈ G.neighborSet v} :=
    ⟨root, by simpa using hrootv.symm⟩
  let mateLocal : {x : V // x ∈ G.neighborSet v} :=
    ⟨mate, by simpa using hmaterv.symm⟩
  have hc := hcanonical rootLocal mateLocal
  have ht : decide ((G.induce (G.neighborSet v)).Adj
      rootLocal mateLocal) = true := by
    simp [rootLocal, mateLocal, hrootmate]
  rw [hc] at ht
  have heq := of_decide_eq_true ht
  have hmate : oneHighStandardMate (0 : Fin 8) = 1 := by decide
  simpa [rootLocal, mateLocal, hroot, hmate] using heq

theorem orderFortyNineB1_neighborFinset_eq_targetImage_of_map
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {v : V} (e : {x : V // x ∈ G.neighborSet v} ≃ Fin 8)
    (E : V ≃ Fin 49) (target : Fin 8 → Fin 49)
    (hmap : ∀ i, E (e.symm i).1 = target i) :
    (orderFortyNineRelabeledGraph G E).neighborFinset (E v) =
      Finset.univ.image target := by
  rw [orderFortyNineRelabeledGraph_neighborFinset]
  ext z
  simp only [Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    let x' : {x : V // x ∈ G.neighborSet v} := ⟨x, by simpa using hx⟩
    exact ⟨e x', by simpa [x'] using (hmap (e x')).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(e.symm i).1,
      (G.mem_neighborFinset v _).mpr (e.symm i).2, hmap i⟩

/-- Exact global geometry labeling for the paired/no-coincidence `b1` case. -/
theorem exists_orderFortyNine_threeHighDistOneB1_geometryLabeling
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (D : ThreeHighDistinctRootBase G)
    {x2 x3 : Fin 49} (hsib : ThreeHighDistOneSiblingData G D x2 x3)
    (hpair : G.Adj D.u12 D.u13)
    (hx2ne : x2 ≠ D.u23) (hx3ne : x3 ≠ D.u23) :
    ∃ E : Equiv.Perm (Fin 49),
      let H := orderFortyNineRelabeledGraph G E
      E D.v1 = 0 ∧ E D.v2 = 1 ∧ E D.v3 = 2 ∧
      H.neighborFinset 0 =
        Finset.univ.image orderFortyNineDistOneB1FirstTarget ∧
      H.neighborFinset 1 =
        Finset.univ.image orderFortyNineDistOneB1SecondTarget ∧
      H.neighborFinset 2 =
        Finset.univ.image orderFortyNineDistOneB1ThirdTarget ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [3, 4, 6, 7, 8, 9, 10, 11]
        [(3, 4), (6, 7), (8, 9), (10, 11)] ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [3, 5, 12, 13, 14, 15, 16, 17]
        [(3, 12), (5, 13), (14, 15), (16, 17)] ∧
      OrderFortyNineGraphPinnedMatchingRealized H
        [4, 5, 18, 19, 20, 21, 22, 23]
        [(4, 18), (5, 19), (20, 21), (22, 23)] := by
  rcases hsib with ⟨_hx2deg, _hx3deg, hx2u12, hx2v2, hx3u13, hx3v3⟩
  have hu12mem : D.u12 ∈ G.neighborFinset D.v1 ∩ G.neighborFinset D.v2 := by
    simp [D.hu12]
  have hu13mem : D.u13 ∈ G.neighborFinset D.v1 ∩ G.neighborFinset D.v3 := by
    simp [D.hu13]
  have hu23mem : D.u23 ∈ G.neighborFinset D.v2 ∩ G.neighborFinset D.v3 := by
    simp [D.hu23]
  have hu12v1 : G.Adj D.u12 D.v1 :=
    ((G.mem_neighborFinset D.v1 D.u12).mp (Finset.mem_inter.mp hu12mem).1).symm
  have hu12v2 : G.Adj D.u12 D.v2 :=
    ((G.mem_neighborFinset D.v2 D.u12).mp (Finset.mem_inter.mp hu12mem).2).symm
  have hu13v1 : G.Adj D.u13 D.v1 :=
    ((G.mem_neighborFinset D.v1 D.u13).mp (Finset.mem_inter.mp hu13mem).1).symm
  have hu13v3 : G.Adj D.u13 D.v3 :=
    ((G.mem_neighborFinset D.v3 D.u13).mp (Finset.mem_inter.mp hu13mem).2).symm
  have hu23v2 : G.Adj D.u23 D.v2 :=
    ((G.mem_neighborFinset D.v2 D.u23).mp (Finset.mem_inter.mp hu23mem).1).symm
  have hu23v3 : G.Adj D.u23 D.v3 :=
    ((G.mem_neighborFinset D.v3 D.u23).mp (Finset.mem_inter.mp hu23mem).2).symm
  have hnot12_23 : ¬ G.Adj D.u12 D.u23 := by
    intro hadj
    have hu := orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin (Fintype.card_fin 49) D.hv2 hu12v2
    have heq := hu.unique ⟨hadj, hu23v2.symm⟩ ⟨hx2u12, hx2v2⟩
    exact hx2ne heq.symm
  have hnot13_23 : ¬ G.Adj D.u13 D.u23 := by
    intro hadj
    have hu := orderFortyNine_existsUnique_local_partner_of_high
      G hfree hmin (Fintype.card_fin 49) D.hv3 hu13v3
    have heq := hu.unique ⟨hadj, hu23v3.symm⟩ ⟨hx3u13, hx3v3⟩
    exact hx3ne heq.symm
  obtain ⟨eA, hA0, hcanA⟩ :=
    exists_orderFortyNine_highNeighborhood_rooted_matching
      G hfree hmin (Fintype.card_fin 49) D.hv1 hu12v1
  have hA1 : eA ⟨D.u13, by simpa using hu13v1.symm⟩ = 1 :=
    orderFortyNineB1_localPartner_coordinate_one G hu12v1 hu13v1
      hpair eA hA0 hcanA
  obtain ⟨eB, hB0, hB2, hcanB⟩ :=
    exists_orderFortyNine_highNeighborhood_two_rooted_matching
      G hfree hmin (Fintype.card_fin 49) D.hv2 hu12v2 hu23v2
      D.hu1223 hnot12_23
  obtain ⟨eC, hC0, hC2, hcanC⟩ :=
    exists_orderFortyNine_highNeighborhood_two_rooted_matching
      G hfree hmin (Fintype.card_fin 49) D.hv3 hu13v3 hu23v3
      D.hu1323 hnot13_23
  let A := G.neighborFinset D.v1
  let B := G.neighborFinset D.v2
  let C := G.neighborFinset D.v3
  let toA : {x : Fin 49 // x ∈ A} ≃
      {x : Fin 49 // x ∈ G.neighborSet D.v1} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [A])
  let toB : {x : Fin 49 // x ∈ B} ≃
      {x : Fin 49 // x ∈ G.neighborSet D.v2} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [B])
  let toC : {x : Fin 49 // x ∈ C} ≃
      {x : Fin 49 // x ∈ G.neighborSet D.v3} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun x => by simp [C])
  let eA' := toA.trans eA
  let eB' := toB.trans eB
  let eC' := toC.trans eC
  have hu12B : D.u12 ∈ B := by
    simpa [B] using (Finset.mem_inter.mp hu12mem).2
  have hu13C : D.u13 ∈ C := by
    simpa [C] using (Finset.mem_inter.mp hu13mem).2
  have hu23C : D.u23 ∈ C := by
    simpa [C] using (Finset.mem_inter.mp hu23mem).2
  have hB0' : eB' ⟨D.u12, hu12B⟩ = 0 := by
    simpa [eB', toB] using hB0
  have hC0' : eC' ⟨D.u13, hu13C⟩ = 0 := by
    simpa [eC', toC] using hC0
  have hC2' : eC' ⟨D.u23, hu23C⟩ = 2 := by
    simpa [eC', toC] using hC2
  let high : Fin 3 → Fin 49 := ![D.v1, D.v2, D.v3]
  have hhigh : Function.Injective high := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [high, D.h12, D.h13, D.h23, Ne.symm D.h12,
        Ne.symm D.h13, Ne.symm D.h23]
  have hn12 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin (Fintype.card_fin 49) D.hv1 D.hv2
  have hn13 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin (Fintype.card_fin 49) D.hv1 D.hv3
  have hn23 := orderFortyNine_not_adj_degreeEight_degreeEight
    G hfree hmin (Fintype.card_fin 49) D.hv2 D.hv3
  have houtside : ∀ z : Fin 49,
      ¬ G.Adj z D.v1 → ¬ G.Adj z D.v2 → ¬ G.Adj z D.v3 →
      ∀ j, z ≠ threeB1CyclicOverlapSource A B C eA' eB' eC' j := by
    intro z hz1 hz2 hz3 j
    rcases j with j | j
    · intro heq
      apply hz1
      have hm := (eA'.symm j).2
      simpa [threeB1CyclicOverlapSource, A, G.adj_comm, heq] using
        ((G.mem_neighborFinset D.v1 _).mp hm)
    · rcases j with j | j
      · intro heq
        apply hz2
        have hm := (eB'.symm j.succ).2
        simpa [threeB1CyclicOverlapSource, B, G.adj_comm, heq] using
          ((G.mem_neighborFinset D.v2 _).mp hm)
      · intro heq
        apply hz3
        have hm := (eC'.symm (orderFortyNineDistOneB1ThirdKeep j)).2
        simpa [threeB1CyclicOverlapSource, C, G.adj_comm, heq] using
          ((G.mem_neighborFinset D.v3 _).mp hm)
  have hcross : ∀ i j,
      high i ≠ threeB1CyclicOverlapSource A B C eA' eB' eC' j := by
    intro i
    fin_cases i
    · exact houtside D.v1 (G.loopless.irrefl D.v1) hn12 hn13
    · exact houtside D.v2 (by simpa [G.adj_comm] using hn12)
        (G.loopless.irrefl D.v2) hn23
    · exact houtside D.v3 (by simpa [G.adj_comm] using hn13)
        (by simpa [G.adj_comm] using hn23) (G.loopless.irrefl D.v3)
  obtain ⟨E, hHighMap, hOverlap⟩ :=
    exists_orderFortyNine_equiv_of_threeCyclicOverlap_b1_with_highs
      (Fintype.card_fin 49) A B C hu12B hu13C hu23C
      (by simpa [A, B] using D.hu12) (by simpa [A, C] using D.hu13)
      (by simpa [B, C] using D.hu23) eA' eB' eC'
      hB0' hC0' hC2' high hhigh hcross
  have hmapA : ∀ i, E (eA.symm i).1 =
      orderFortyNineDistOneB1FirstTarget i := by
    intro i
    simpa [threeB1CyclicOverlapSource,
      orderFortyNineDistOneB1OverlapTarget, eA', toA] using
      hOverlap (Sum.inl i)
  have hArootSymm : eA.symm 0 =
      ⟨D.u12, by simpa using hu12v1.symm⟩ := by
    apply eA.injective
    simp [hA0]
  have hAmateSymm : eA.symm 1 =
      ⟨D.u13, by simpa using hu13v1.symm⟩ := by
    apply eA.injective
    simp [hA1]
  have hBrootSymm : eB.symm 0 =
      ⟨D.u12, by simpa using hu12v2.symm⟩ := by
    apply eB.injective
    simp [hB0]
  have hBotherSymm : eB.symm 2 =
      ⟨D.u23, by simpa using hu23v2.symm⟩ := by
    apply eB.injective
    simp [hB2]
  have hCrootSymm : eC.symm 0 =
      ⟨D.u13, by simpa using hu13v3.symm⟩ := by
    apply eC.injective
    simp [hC0]
  have hCotherSymm : eC.symm 2 =
      ⟨D.u23, by simpa using hu23v3.symm⟩ := by
    apply eC.injective
    simp [hC2]
  have hmapB : ∀ i, E (eB.symm i).1 =
      orderFortyNineDistOneB1SecondTarget i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [hBrootSymm, hArootSymm,
        orderFortyNineDistOneB1SecondTarget,
        orderFortyNineDistOneB1FirstTarget] using hmapA 0
    · simpa [threeB1CyclicOverlapSource,
        orderFortyNineDistOneB1OverlapTarget, eB', toB] using
        hOverlap (Sum.inr (Sum.inl j))
  have hmapC : ∀ i, E (eC.symm i).1 =
      orderFortyNineDistOneB1ThirdTarget i := by
    intro i
    fin_cases i
    · simpa [hCrootSymm, hAmateSymm,
        orderFortyNineDistOneB1ThirdTarget,
        orderFortyNineDistOneB1FirstTarget] using hmapA 1
    · simpa [threeB1CyclicOverlapSource,
        orderFortyNineDistOneB1OverlapTarget,
        orderFortyNineDistOneB1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (0 : Fin 6)))
    · simpa [hCotherSymm, hBotherSymm,
        orderFortyNineDistOneB1ThirdTarget,
        orderFortyNineDistOneB1SecondTarget] using hmapB 2
    · simpa [threeB1CyclicOverlapSource,
        orderFortyNineDistOneB1OverlapTarget,
        orderFortyNineDistOneB1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (1 : Fin 6)))
    · simpa [threeB1CyclicOverlapSource,
        orderFortyNineDistOneB1OverlapTarget,
        orderFortyNineDistOneB1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (2 : Fin 6)))
    · simpa [threeB1CyclicOverlapSource,
        orderFortyNineDistOneB1OverlapTarget,
        orderFortyNineDistOneB1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (3 : Fin 6)))
    · simpa [threeB1CyclicOverlapSource,
        orderFortyNineDistOneB1OverlapTarget,
        orderFortyNineDistOneB1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (4 : Fin 6)))
    · simpa [threeB1CyclicOverlapSource,
        orderFortyNineDistOneB1OverlapTarget,
        orderFortyNineDistOneB1ThirdKeep, eC', toC] using
        hOverlap (Sum.inr (Sum.inr (5 : Fin 6)))
  have hEv1 : E D.v1 = 0 := by
    simpa [high, orderFortyNineDistOneC2HighTarget] using hHighMap 0
  have hEv2 : E D.v2 = 1 := by
    simpa [high, orderFortyNineDistOneC2HighTarget] using hHighMap 1
  have hEv3 : E D.v3 = 2 := by
    simpa [high, orderFortyNineDistOneC2HighTarget] using hHighMap 2
  have hN0 := orderFortyNineB1_neighborFinset_eq_targetImage_of_map
    G eA E orderFortyNineDistOneB1FirstTarget hmapA
  have hN1 := orderFortyNineB1_neighborFinset_eq_targetImage_of_map
    G eB E orderFortyNineDistOneB1SecondTarget hmapB
  have hN2 := orderFortyNineB1_neighborFinset_eq_targetImage_of_map
    G eC E orderFortyNineDistOneB1ThirdTarget hmapC
  have hm0 := orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
    G eA E orderFortyNineDistOneB1FirstTarget
      [3, 4, 6, 7, 8, 9, 10, 11]
      [(3, 4), (6, 7), (8, 9), (10, 11)]
      hcanA hmapA orderFortyNineDistOneB1FirstTarget_standard
  have hm1 := orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
    G eB E orderFortyNineDistOneB1SecondTarget
      [3, 5, 12, 13, 14, 15, 16, 17]
      [(3, 12), (5, 13), (14, 15), (16, 17)]
      hcanB hmapB orderFortyNineDistOneB1SecondTarget_standard
  have hm2 := orderFortyNineGraphPinnedMatchingRealized_of_localNormalization
    G eC E orderFortyNineDistOneB1ThirdTarget
      [4, 5, 18, 19, 20, 21, 22, 23]
      [(4, 18), (5, 19), (20, 21), (22, 23)]
      hcanC hmapC orderFortyNineDistOneB1ThirdTarget_standard
  refine ⟨E, hEv1, hEv2, hEv3, ?_, ?_, ?_, hm0, hm1, hm2⟩
  · rw [hEv1] at hN0
    exact hN0
  · rw [hEv2] at hN1
    exact hN1
  · rw [hEv3] at hN2
    exact hN2

/-- The three exact `b1` neighborhoods determine the small-high mask fields. -/
theorem orderFortyNineThreeHighDistOneB1_smallHighAlignedLabeling
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
      Finset.univ.image orderFortyNineDistOneB1FirstTarget)
    (hN1 : (orderFortyNineRelabeledGraph G E).neighborFinset 1 =
      Finset.univ.image orderFortyNineDistOneB1SecondTarget)
    (hN2 : (orderFortyNineRelabeledGraph G E).neighborFinset 2 =
      Finset.univ.image orderFortyNineDistOneB1ThirdTarget) :
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
        i ∈ Finset.univ.image orderFortyNineDistOneB1FirstTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN0]
    have hAdj1 : H.Adj i 1 ↔
        i ∈ Finset.univ.image orderFortyNineDistOneB1SecondTarget := by
      rw [H.adj_comm, ← H.mem_neighborFinset, hN1]
    have hAdj2 : H.Adj i 2 ↔
        i ∈ Finset.univ.image orderFortyNineDistOneB1ThirdTarget := by
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

/-- The paired/no-coincidence graph case admits the exact scout labeling. -/
theorem orderFortyNine_threeHighDistOneB1AlignedCover :
    ThreeHighDistOneB1AlignedCover := by
  intro G _ _ _ hfree hmin D hcase
  obtain ⟨x2, x3, hsib, hpair, hx2ne, hx3ne⟩ := hcase
  obtain ⟨E, hEv1, hEv2, hEv3, hN0, hN1, hN2, hm0, hm1, hm2⟩ :=
    exists_orderFortyNine_threeHighDistOneB1_geometryLabeling
      G hfree hmin D hsib hpair hx2ne hx3ne
  refine ⟨E, ?_⟩
  exact ⟨orderFortyNineThreeHighDistOneB1_smallHighAlignedLabeling
      G hfree hmin D.hHigh E hEv1 hEv2 hEv3 hN0 hN1 hN2,
    hm0, hm1, hm2⟩

end

end Erdos85

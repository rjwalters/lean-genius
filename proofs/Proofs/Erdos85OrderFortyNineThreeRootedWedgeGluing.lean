import Proofs.Erdos85FiniteEquivGluing

/-! # Gluing three eight-point neighborhoods at one common root -/

namespace Erdos85

noncomputable section

abbrev ThreeRootedWedgeIndex := Fin 8 ⊕ (Fin 7 ⊕ Fin 7)

def threeRootedWedgeSource
    {V : Type*} [DecidableEq V]
    (A B C : Finset V)
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8) : ThreeRootedWedgeIndex → V
  | Sum.inl i => (eA.symm i).1
  | Sum.inr (Sum.inl i) => (eB.symm i.succ).1
  | Sum.inr (Sum.inr i) => (eC.symm i.succ).1

def orderFortyNineDistTwoFirstTarget : Fin 8 → Fin 49 :=
  ![3, 4, 5, 6, 7, 8, 9, 10]

def orderFortyNineDistTwoSecondTarget : Fin 8 → Fin 49 :=
  ![3, 11, 14, 15, 16, 17, 18, 19]

def orderFortyNineDistTwoThirdTarget : Fin 8 → Fin 49 :=
  ![3, 12, 20, 21, 22, 23, 24, 25]

def orderFortyNineDistTwoWedgeTarget :
    ThreeRootedWedgeIndex → Fin 49
  | Sum.inl i => orderFortyNineDistTwoFirstTarget i
  | Sum.inr (Sum.inl i) => orderFortyNineDistTwoSecondTarget i.succ
  | Sum.inr (Sum.inr i) => orderFortyNineDistTwoThirdTarget i.succ

theorem orderFortyNineDistTwoWedgeTarget_injective :
    Function.Injective orderFortyNineDistTwoWedgeTarget := by
  decide +revert

theorem threeRootedWedgeSource_injective
    {V : Type*} [DecidableEq V]
    (A B C : Finset V) {root : V}
    (hrB : root ∈ B) (hrC : root ∈ C)
    (hAB : A ∩ B = {root}) (hAC : A ∩ C = {root})
    (hBC : B ∩ C = {root})
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8)
    (hrootB : eB ⟨root, hrB⟩ = 0)
    (hrootC : eC ⟨root, hrC⟩ = 0) :
    Function.Injective (threeRootedWedgeSource A B C eA eB eC) := by
  have hABne : ∀ (i : Fin 8) (j : Fin 7),
      (eA.symm i).1 ≠ (eB.symm j.succ).1 := by
    intro i j hij
    have hx : (eA.symm i).1 ∈ A ∩ B := by
      exact Finset.mem_inter.mpr ⟨(eA.symm i).2, hij ▸ (eB.symm j.succ).2⟩
    have hxroot : (eA.symm i).1 = root := by simpa [hAB] using hx
    have hbroot : (eB.symm j.succ).1 = root := hij.symm.trans hxroot
    have hbsub : eB.symm j.succ = ⟨root, hrB⟩ := Subtype.ext hbroot
    have he := congrArg eB hbsub
    simp only [eB.apply_symm_apply, hrootB] at he
    exact Fin.succ_ne_zero j he
  have hACne : ∀ (i : Fin 8) (j : Fin 7),
      (eA.symm i).1 ≠ (eC.symm j.succ).1 := by
    intro i j hij
    have hx : (eA.symm i).1 ∈ A ∩ C := by
      exact Finset.mem_inter.mpr ⟨(eA.symm i).2, hij ▸ (eC.symm j.succ).2⟩
    have hxroot : (eA.symm i).1 = root := by simpa [hAC] using hx
    have hcroot : (eC.symm j.succ).1 = root := hij.symm.trans hxroot
    have hcsub : eC.symm j.succ = ⟨root, hrC⟩ := Subtype.ext hcroot
    have he := congrArg eC hcsub
    simp only [eC.apply_symm_apply, hrootC] at he
    exact Fin.succ_ne_zero j he
  have hBCne : ∀ (i j : Fin 7),
      (eB.symm i.succ).1 ≠ (eC.symm j.succ).1 := by
    intro i j hij
    have hx : (eB.symm i.succ).1 ∈ B ∩ C := by
      exact Finset.mem_inter.mpr ⟨(eB.symm i.succ).2, hij ▸ (eC.symm j.succ).2⟩
    have hxroot : (eB.symm i.succ).1 = root := by simpa [hBC] using hx
    have hbsub : eB.symm i.succ = ⟨root, hrB⟩ := Subtype.ext hxroot
    have he := congrArg eB hbsub
    simp only [eB.apply_symm_apply, hrootB] at he
    exact Fin.succ_ne_zero i he
  intro p q hpq
  cases p with
  | inl i =>
      cases q with
      | inl j =>
          have hij : i = j := eA.symm.injective (Subtype.ext hpq)
          subst j
          rfl
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
                  have hs : i.succ = j.succ :=
                    eB.symm.injective (Subtype.ext hpq)
                  have hij : i = j := Fin.succ_injective 7 hs
                  subst j
                  rfl
              | inr j => exact (hBCne i j hpq).elim
      | inr i =>
          cases q with
          | inl j => exact (hACne j i hpq.symm).elim
          | inr q =>
              cases q with
              | inl j => exact (hBCne j i hpq.symm).elim
              | inr j =>
                  have hs : i.succ = j.succ :=
                    eC.symm.injective (Subtype.ext hpq)
                  have hij : i = j := Fin.succ_injective 7 hs
                  subst j
                  rfl

theorem exists_orderFortyNine_equiv_of_threeRootedWedge
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 49)
    (A B C : Finset V) {root : V}
    (hrA : root ∈ A) (hrB : root ∈ B) (hrC : root ∈ C)
    (hAB : A ∩ B = {root}) (hAC : A ∩ C = {root})
    (hBC : B ∩ C = {root})
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8)
    (hrootA : eA ⟨root, hrA⟩ = 0)
    (hrootB : eB ⟨root, hrB⟩ = 0)
    (hrootC : eC ⟨root, hrC⟩ = 0) :
    ∃ E : V ≃ Fin 49, E root = 3 ∧ ∀ i,
      E (threeRootedWedgeSource A B C eA eB eC i) =
        orderFortyNineDistTwoWedgeTarget i := by
  obtain ⟨E, hE⟩ := exists_equiv_fin_extending_pair hcard
    (threeRootedWedgeSource A B C eA eB eC)
    orderFortyNineDistTwoWedgeTarget
    (threeRootedWedgeSource_injective A B C hrB hrC
      hAB hAC hBC eA eB eC hrootB hrootC)
    orderFortyNineDistTwoWedgeTarget_injective
  refine ⟨E, ?_, hE⟩
  have hsymm : eA.symm 0 = ⟨root, hrA⟩ := by
    apply eA.injective
    simp [hrootA]
  simpa [threeRootedWedgeSource, orderFortyNineDistTwoWedgeTarget,
    orderFortyNineDistTwoFirstTarget, hsymm] using
      hE (Sum.inl (0 : Fin 8))

def orderFortyNineDistTwoExtraTarget : Fin 4 → Fin 49 := ![0, 1, 2, 13]

theorem orderFortyNineDistTwoExtraTarget_injective :
    Function.Injective orderFortyNineDistTwoExtraTarget := by
  decide +revert

theorem orderFortyNineDistTwoExtraTarget_disjoint_wedge :
    ∀ i j, orderFortyNineDistTwoExtraTarget i ≠
      orderFortyNineDistTwoWedgeTarget j := by
  decide

/-- Add the three high centers and the residual root neighbor to the rooted
wedge before extending the partial labeling to all 49 vertices. -/
theorem exists_orderFortyNine_equiv_of_threeRootedWedge_with_extra
    {V : Type*} [Fintype V] [DecidableEq V]
    (hcard : Fintype.card V = 49)
    (A B C : Finset V) {root : V}
    (hrA : root ∈ A) (hrB : root ∈ B) (hrC : root ∈ C)
    (hAB : A ∩ B = {root}) (hAC : A ∩ C = {root})
    (hBC : B ∩ C = {root})
    (eA : {x // x ∈ A} ≃ Fin 8)
    (eB : {x // x ∈ B} ≃ Fin 8)
    (eC : {x // x ∈ C} ≃ Fin 8)
    (hrootA : eA ⟨root, hrA⟩ = 0)
    (hrootB : eB ⟨root, hrB⟩ = 0)
    (hrootC : eC ⟨root, hrC⟩ = 0)
    (extra : Fin 4 → V) (hextra : Function.Injective extra)
    (hcross : ∀ i j,
      extra i ≠ threeRootedWedgeSource A B C eA eB eC j) :
    ∃ E : V ≃ Fin 49,
      (∀ i, E (extra i) = orderFortyNineDistTwoExtraTarget i) ∧
      E root = 3 ∧
      (∀ j, E (threeRootedWedgeSource A B C eA eB eC j) =
        orderFortyNineDistTwoWedgeTarget j) := by
  obtain ⟨E, hExtra, hWedge⟩ :=
    exists_equiv_fin_extending_disjoint_pairs hcard
      extra (threeRootedWedgeSource A B C eA eB eC)
      orderFortyNineDistTwoExtraTarget orderFortyNineDistTwoWedgeTarget
      hextra
      (threeRootedWedgeSource_injective A B C hrB hrC
        hAB hAC hBC eA eB eC hrootB hrootC)
      orderFortyNineDistTwoExtraTarget_injective
      orderFortyNineDistTwoWedgeTarget_injective hcross
      orderFortyNineDistTwoExtraTarget_disjoint_wedge
  refine ⟨E, hExtra, ?_, hWedge⟩
  have hsymm : eA.symm 0 = ⟨root, hrA⟩ := by
    apply eA.injective
    simp [hrootA]
  simpa [threeRootedWedgeSource, orderFortyNineDistTwoWedgeTarget,
    orderFortyNineDistTwoFirstTarget, hsymm] using
      hWedge (Sum.inl (0 : Fin 8))

end

end Erdos85
